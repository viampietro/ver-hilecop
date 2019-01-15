Require Export Hilecop.SPN.

(*========================================================*)
(*=== TYPES FOR GENERALIZED, EXTENDED, SYNCHRONOUS AND ===*)
(*=== TEMPORAL PETRI NETS.                             ===*)
(*========================================================*)

(* 
 * Defines the time interval structure associated with transitions.
 * Transitions are firable when min_t <= cnt <= max_t.
 * 
 *)
Structure chrono_type : Set :=
  mk_chrono {
      cnt : nat;   (* possibly 0 /!\ *)
      min_t : nat_star;
      max_t : nat_star;

      (* true, if the upper bound of the time interval 
       * is infinite.
       *)
      max_is_infinite : bool;

      (* Tells that the lower bound of the time interval 
       * is always less than or equal to the upper bound.
       *)
      min_t_le_max_t : (int min_t) <= (int max_t);
      
  }.

(*  
 * Defines the STPN structure. 
 * 
 * Basically, same structure as an spn with chronos associated to transitions.
 * (At most one chrono by transition, or None)
 *
 * STPN is declared as a coercion of SPN.
 *)
Structure STPN : Set :=
  mk_STPN {
      chronos : list (trans_type * option chrono_type);
      spn :> SPN
    }.

(*==============================================*)
(*============ PROPERTIES ON SPN ===============*)
(*==============================================*)

(* Properties on chronos. *)
Definition ChronosHaveSameStruct (chronos chronos' : list (trans_type * option chrono_type)) :=
  fst (split chronos) = fst (split chronos').

Definition PriorityGroupsAreRefInChronos
           (priority_groups : list (list trans_type))
           (chronos : list (trans_type * option chrono_type)) :=
  (forall pgroup : list trans_type,
      In pgroup priority_groups ->
      (forall t : trans_type, In t pgroup -> In t (fst (split chronos)))).

Definition NoUnknownTransInChronos (stpn : STPN) :=
  stpn.(transs) = fst (split stpn.(chronos)).

(* Properties on whole STPN. *)
Definition IsWellStructuredStpn (stpn : STPN) :=
  NoUnknownTransInChronos stpn /\ IsWellStructuredSpn stpn.(spn).

(*===================================================*)
(*=============== CHRONO SECTION  ===================*)
(*===================================================*)
Section Chrono.

  (*  
   * Function : Returns true if chrono doesn't exist,
   *            or if the associated cnt is greater or equal
   *            to min_t and less or equal to max_t.
   *            Returns false otherwise.
   *)
  Definition check_chrono (opt_chrono : option chrono_type) : bool :=
    match opt_chrono with
    | None => true
    | Some (mk_chrono cnt min_t max_t max_is_infinite _) =>
      (* If upper bound is infinite, tests only the lower bound *)
      if max_is_infinite then
        int min_t <=? cnt
      else (int min_t <=? cnt) && (cnt <=? int max_t)
    end.

  (*** Formal specification : check_chrono ***)
  Inductive CheckChrono : option chrono_type -> Prop :=
  | CheckChrono_none : 
      CheckChrono None
  | CheckChrono_infinite :
      forall (cnt : nat)
             (min_t max_t : nat_star)
             (max_is_infinite : bool)
             (min_t_le_max_t : (int min_t) <= (int max_t)),
        max_is_infinite = true ->
        (int min_t) <= cnt ->
        CheckChrono (Some (mk_chrono cnt min_t max_t max_is_infinite min_t_le_max_t))
  | CheckChrono_cons :
      forall (cnt : nat)
             (min_t max_t : nat_star)
             (max_is_infinite : bool)
             (min_t_le_max_t : (int min_t) <= (int max_t)),
        max_is_infinite = false ->
        ((int min_t) <= cnt) /\ (cnt <= (int max_t)) ->
        CheckChrono (Some (mk_chrono cnt min_t max_t max_is_infinite min_t_le_max_t)).

  Functional Scheme check_chrono_ind :=
    Induction for check_chrono Sort Prop.

  (*** Correctness proof : check_chrono ***)
  Theorem check_chrono_correct :
    forall (opt_chrono : option chrono_type),
      check_chrono opt_chrono = true -> CheckChrono opt_chrono.
  Proof.
    intros chrono;
      functional induction (check_chrono chrono)
                 using check_chrono_ind;
      intro Htrue.
    (* Case max_is_infinite = true. *)
    - apply CheckChrono_infinite with (cnt := cnt0)
                                      (min_t := min_t0)
                                      (max_t := max_t0)
                                      (min_t_le_max_t := _x).
      + auto.
      + apply leb_complete in Htrue; auto.
    (* General case, with one min and one max. *)
    - apply CheckChrono_cons with (cnt := cnt0)
                                  (min_t := min_t0)
                                  (max_t := max_t0)
                                  (min_t_le_max_t := _x).
      + auto.
      + apply andb_true_iff in Htrue; elim Htrue; intros; split.
        -- apply leb_complete in H; auto.
        -- apply leb_complete in H0; auto.
    (* Case chrono = None *)
    - apply CheckChrono_none.
  Qed.

  (*** Completeness proof : check_chrono ***)
  Theorem check_chrono_complete :
    forall (opt_chrono : option chrono_type),
      CheckChrono opt_chrono -> check_chrono opt_chrono = true.     
  Proof.
    intros chrono Hspec; elim Hspec; intros.
    (* Case CheckChrono_none *)
    - simpl; auto.
    (* Case CheckChrono_infinite *)
    - simpl; rewrite H; apply leb_correct; auto.
    (* Case CheckChrono_cons *)
    - simpl; rewrite H; elim H0; intros; apply andb_true_iff; split.
      + apply leb_correct; auto.
      + apply leb_correct; auto.
  Qed.
  
  (*  
   * Function : Returns the chrono associated to
   *            transition t if t is referenced in the chronos list.
   *            Raises an error (None value) otherwise.
   *)
  Fixpoint get_chrono
           (chronos : list (trans_type * option chrono_type))
           (t : trans_type) {struct chronos} :
    option (option chrono_type) :=
    match chronos with
    | (t', opt_chrono) :: tail => if t =? t' then
                                    Some opt_chrono
                                  else get_chrono tail t
    (* Case of error!!! *)
    | [] => None
    end.

    Functional Scheme get_chrono_ind := Induction for get_chrono Sort Prop. 

    (*** Formal specification : get_chrono ***)
    Inductive GetChrono :
      list (trans_type * option chrono_type) ->
      trans_type ->
      option (option chrono_type) -> Prop :=
    | GetChrono_err :
        forall t : trans_type,
          GetChrono [] t None
    | GetChrono_hd_true :
        forall (chronos : list (trans_type * option chrono_type))
               (t t' : trans_type)
               (opt_chrono : option chrono_type),
          t = t' ->
          GetChrono ((t', opt_chrono) :: chronos) t (Some opt_chrono)
    | GetChrono_hd_false :
        forall (chronos : list (trans_type * option chrono_type))
               (t t' : trans_type)
               (opt_chrono : option chrono_type)
               (opt_opt_chrono : option (option chrono_type)),
          t <> t' ->
          GetChrono chronos t opt_opt_chrono ->
          GetChrono ((t', opt_chrono) :: chronos) t opt_opt_chrono.
          
    (*** Correctness proof : get_chrono ***)
    Theorem get_chrono_correct :
      forall (chronos : list (trans_type * option chrono_type))
             (t : trans_type)
             (opt_opt_chrono : option (option chrono_type)),
        get_chrono chronos t = opt_opt_chrono ->
        GetChrono chronos t opt_opt_chrono.
    Proof.
      intros chronos t.
      functional induction (get_chrono chronos t) using get_chrono_ind; intros.
      (* Error case chronos = []. *)
      - rewrite <- H; apply GetChrono_err.
      (* Case t = hd chronos. *)
      - rewrite <- H; apply GetChrono_hd_true; apply beq_nat_true in e1; auto.
      (* Case t <> hd chronos. *)
      - rewrite <- H; apply GetChrono_hd_false.
        + apply beq_nat_false in e1; auto.
        + apply IHo; auto.
    Qed.

    (*** Completeness proof : get_chrono ***)
    Theorem get_chrono_compl :
      forall (chronos : list (trans_type * option chrono_type))
             (t : trans_type)
             (opt_opt_chrono : option (option chrono_type)),
        GetChrono chronos t opt_opt_chrono ->
        get_chrono chronos t = opt_opt_chrono.
    Proof.
      intros chronos t opt_opt_chrono H.
      induction H.
      (* Case GetChrono_err *)
      - simpl; auto.
      (* Case GetChrono_hd_true *)
      - simpl; apply Nat.eqb_eq in H; rewrite H; auto.
      (* Case GetChrono_hd_false *)
      - simpl; apply Nat.eqb_neq in H; rewrite H; auto.
    Qed.

    (* Lemma : For all chronos and transition t, 
     *         (get_chrono chronos t) returns no error
     *         if t is referenced in chronos.
     *
     *)
    Lemma get_chrono_no_error :
      forall (chronos : list (trans_type * option chrono_type))
             (t : trans_type),
        In t (fst (split chronos)) ->
        exists v : option chrono_type, get_chrono chronos t = Some v.
    Proof.
      intros chronos t H;
        functional induction (get_chrono chronos t) using get_chrono_ind;
        decide_accessor_no_err.
    Qed.
    
    (* 
     * Function : Returns true if chrono and chrono' are equal.
     * 
     *            Two chronos are equal only if their max_is_infinite attribute
     *            values are the same.
     *
     *            If max_is_infinite is true for both chronos, then
     *            only counter value and min_t value are compared for equality.
     *            Otherwise, counter, min_t and max_t are compared.     
     *)
    Definition beq_chrono (chrono chrono' : chrono_type) : bool :=
      match (max_is_infinite chrono), (max_is_infinite chrono') with
      | true, true => ((cnt chrono) =? (cnt chrono'))
                        && ((int (min_t chrono)) =? (int (min_t chrono')))
      | false, false => ((cnt chrono) =? (cnt chrono'))
                          && ((int (min_t chrono)) =? (int (min_t chrono')))
                          && ((int (max_t chrono)) =? (int (max_t chrono')))
      | _, _ => false
      end.

    Functional Scheme beq_chrono_ind := Induction for beq_chrono Sort Prop. 

    (*** Formal specification : beq_chrono ***)
    Inductive BEqChrono (chrono chrono' : chrono_type) : Prop :=
    | BEqChrono_inf :
        max_is_infinite chrono = true ->
        max_is_infinite chrono' = true ->
        cnt chrono = cnt chrono' ->
        (int (min_t chrono)) = (int (min_t chrono')) ->
        BEqChrono chrono chrono'
    | BEqChrono_cons : 
        max_is_infinite chrono = false ->
        max_is_infinite chrono' = false ->
        cnt chrono = cnt chrono' ->
        (int (min_t chrono)) = (int (min_t chrono')) ->
        (int (max_t chrono)) = (int (max_t chrono')) ->
        BEqChrono chrono chrono'.

    (*** Correctness proof : beq_chrono ***)
    Theorem beq_chrono_correct :
      forall chrono chrono' : chrono_type,
        beq_chrono chrono chrono' = true ->
        BEqChrono chrono chrono'.
    Proof.
      do 2 intro.
      functional induction (beq_chrono chrono chrono')
                 using beq_chrono_ind;
      intros.
      (* Case max_is_infinite = true for both chronos. *)
      - apply andb_true_iff in H; elim H; intros.
        apply Nat.eqb_eq in H0.
        apply Nat.eqb_eq in H1.
        apply BEqChrono_inf; auto.
      (* 2 cases, max_is_infinite is different for both chronos. *)
      - inversion H.
      - inversion H.
      (* Case max_is_infinite = false for both chronos. *)
      - apply andb_true_iff in H; elim H; intros.
        apply andb_true_iff in H0; elim H0; intros.
        apply Nat.eqb_eq in H1.
        apply Nat.eqb_eq in H2.
        apply Nat.eqb_eq in H3.
        apply BEqChrono_cons; auto.
    Qed.

    (*** Completeness proof : beq_chrono ***)
    Theorem beq_chrono_compl :
      forall chrono chrono' : chrono_type,
        BEqChrono chrono chrono' ->
        beq_chrono chrono chrono' = true.
    Proof.
      intros; elim H; intros.
      (*  *)
      - unfold beq_chrono; rewrite H0; rewrite H1.
        apply andb_true_iff; split.
        + apply Nat.eqb_eq in H2; auto.
        + apply Nat.eqb_eq in H3; auto.
      (*  *)
      - unfold beq_chrono; rewrite H0; rewrite H1.
        apply andb_true_iff; split; [ apply andb_true_iff; split; [apply Nat.eqb_eq in H2; auto
                                                                  | apply Nat.eqb_eq in H3; auto]
                                    | apply Nat.eqb_eq; auto].
    Qed.

    (*  
     * Useful to prove replace_chrono_correct.
     *)
    Theorem beq_chrono_iff :
      forall chrono chrono' : chrono_type,
        BEqChrono chrono chrono' <-> beq_chrono chrono chrono' = true.
    Proof.
      intros.
      split.
      apply beq_chrono_compl.
      apply beq_chrono_correct.
    Qed.
    
    (*  
     * Function : Returns a list of pair (trans, chrono) where the first 
     *            occurence of old_chrono has been replaced by new_chrono 
     *            (if old_chrono is found in the list).
     *)
    Fixpoint replace_chrono
             (old_chrono new_chrono : chrono_type)
             (chronos : list (trans_type * option chrono_type))
             {struct chronos} :
      list (trans_type * option chrono_type) :=
      match chronos with
      | (t, opt_chrono) :: tail =>
        match opt_chrono with
        (* opt_chrono has Some chrono. *)
        | Some chrono =>
          (* If old_chrono equals chrono, replaces old_chrono by new_chrono. *)
          if beq_chrono old_chrono chrono then
            (t, Some new_chrono) :: tail
          else (t, opt_chrono) :: replace_chrono old_chrono new_chrono tail
        (* If opt_chrono is None, then looks for old_chrono in the tail. *)
        | None => (t, opt_chrono) :: replace_chrono old_chrono new_chrono tail
        end
      | [] => []
      end.

    Functional Scheme replace_chrono_ind := Induction for replace_chrono Sort Prop.
    
    (*** Formal specification : replace_chrono ***)
    Inductive ReplaceChrono (old_chrono new_chrono : chrono_type) :
      list (trans_type * option chrono_type) ->
      list (trans_type * option chrono_type) -> Prop :=
    | ReplaceChrono_nil :
        ReplaceChrono old_chrono new_chrono [] []
    | ReplaceChrono_hd_true :
        forall (chronos : list (trans_type * option chrono_type))
               (t : trans_type)
               (opt_chrono : option chrono_type)
               (chrono : chrono_type),
          opt_chrono = Some chrono ->
          BEqChrono old_chrono chrono ->
          ReplaceChrono old_chrono new_chrono
                        ((t, opt_chrono) :: chronos)
                        ((t, Some new_chrono) :: chronos)
    | ReplaceChrono_hd_false :
        forall (chronos : list (trans_type * option chrono_type))
               (t : trans_type)
               (opt_chrono : option chrono_type)
               (chrono : chrono_type)
               (final_chronos : list (trans_type * option chrono_type)),
          opt_chrono = Some chrono ->
          ~BEqChrono old_chrono chrono ->
          ReplaceChrono old_chrono new_chrono chronos final_chronos ->
          ReplaceChrono old_chrono new_chrono
                        ((t, opt_chrono) :: chronos)
                        ((t, opt_chrono) :: final_chronos)
    | ReplaceChrono_hd_none :
        forall (chronos : list (trans_type * option chrono_type))
               (t : trans_type)
               (opt_chrono : option chrono_type)
               (final_chronos : list (trans_type * option chrono_type)),
          opt_chrono = None ->
          ReplaceChrono old_chrono new_chrono chronos final_chronos ->
          ReplaceChrono old_chrono new_chrono
                        ((t, opt_chrono) :: chronos)
                        ((t, opt_chrono) :: final_chronos).

    (*** Correctness proof : replace_chrono ***)
    Theorem replace_chrono_correct :
      forall (old_chrono new_chrono : chrono_type)
             (chronos : list (trans_type * option chrono_type))
             (final_chronos : list (trans_type * option chrono_type)),
        replace_chrono old_chrono new_chrono chronos = final_chronos ->
        ReplaceChrono old_chrono new_chrono chronos final_chronos.
    Proof.
      intros old_chrono new_chrono chronos.
      functional induction (replace_chrono old_chrono new_chrono chronos)
                 using replace_chrono_ind; intros.
      (* Case chronos = [] *)
      - rewrite <- H; apply ReplaceChrono_nil.
      (* Case beq_chrono old_chrono chrono = true. *)
      - rewrite <- H; apply ReplaceChrono_hd_true with (chrono := chrono).
        + auto.
        + apply beq_chrono_correct in e2; auto.
      (* Case beq_chrono old_chrono chrono = false. *)
      - rewrite <- H; apply ReplaceChrono_hd_false with (chrono := chrono).
        + auto.
        + assert (Hnot_beq_chrono := (not_iff_compat (beq_chrono_iff old_chrono chrono))).
          apply Hnot_beq_chrono; red; intro.
          rewrite H0 in e2; inversion e2.
        + apply IHl; auto.
      (* Case opt_chrono = None. *)
      - rewrite <- H; apply ReplaceChrono_hd_none.
        + auto.
        + apply IHl; auto.
    Qed.

    (*** Completeness proof : replace_chrono ***)
    Theorem replace_chrono_compl :
      forall (old_chrono new_chrono : chrono_type)
             (chronos : list (trans_type * option chrono_type))
             (final_chronos : list (trans_type * option chrono_type)),
        ReplaceChrono old_chrono new_chrono chronos final_chronos ->
        replace_chrono old_chrono new_chrono chronos = final_chronos.
    Proof.
      intros old_chrono new_chrono chronos final_chronos H.
      elim H; intros.
      (* ReplaceChrono_nil *)
      - simpl; auto.
      (* ReplaceChrono_hd_true *)
      - apply beq_chrono_compl in H1; simpl; rewrite H0; rewrite H1; auto.
      (* ReplaceChrono_hd_false *)
      - assert (Hnot_beq_chrono := (not_iff_compat (beq_chrono_iff old_chrono chrono))).
        apply Hnot_beq_chrono in H1; apply not_true_is_false in H1.
        simpl; rewrite H0; rewrite H1; rewrite H3; auto.
      (* ReplaceChrono_hd_none *)
      - simpl; rewrite H0; rewrite H2; auto.
    Qed.

    (* Lemma : Proves that replace_chrono preserves structure
     *         of chronos.
     *)
    Lemma replace_chrono_same_struct :
      forall (old_chrono new_chrono : chrono_type)
             (chronos : list (trans_type * option chrono_type)),
        ChronosHaveSameStruct (replace_chrono old_chrono new_chrono chronos) chronos.
    Proof.
      intros old_chrono new_chrono chronos.
      unfold ChronosHaveSameStruct.
      functional induction (replace_chrono old_chrono new_chrono chronos)
                 using replace_chrono_ind;
        intros.
      (* Base case. *)
      - auto.
      (* Case old_chrono is head of the list. *)
      - rewrite fst_split_app; symmetry; rewrite fst_split_app; simpl; auto.
      (* Case old_chrono is not head of list. *)
      - rewrite fst_split_app; symmetry; rewrite fst_split_app; rewrite IHl; auto.
      (* Case head of chronos is None. *)
      - rewrite fst_split_app; symmetry; rewrite fst_split_app; rewrite IHl; auto.
    Qed.
    
    (*  
     * Function : Returns a new list of chronos, where the time
     *            counter of transition t is incremented.
     *            Raises an error (None value) if get_chrono returns
     *            an error.
     *)
    Definition increment_chrono
               (t : trans_type) 
               (chronos : list (trans_type * option chrono_type)) :
      option (list (trans_type * option chrono_type)) :=
      match get_chrono chronos t with
      | Some opt_chrono =>
        match opt_chrono with
        (* Replaces old chrono by an incremented chrono 
         * in chronos list.
         *)
        | Some (mk_chrono cnt min_t max_t max_is_infinite min_t_le_max_t) =>
          Some (replace_chrono (mk_chrono cnt min_t max_t max_is_infinite min_t_le_max_t)
                               (mk_chrono (cnt + 1) min_t max_t max_is_infinite min_t_le_max_t)
                               chronos)
        (* Otherwise, nothing to increment, t has no associated chrono. *)
        | None => Some chronos
        end
      (* Case of error!!! *)
      | None => None
      end.

    Functional Scheme increment_chrono_ind := Induction for increment_chrono Sort Prop. 
    
    (*** Formal specification : increment_chrono ***)
    Inductive IncrementChrono (t : trans_type) :
      list (trans_type * option chrono_type) ->
      option (list (trans_type * option chrono_type)) ->
      Prop :=
    | IncrementChrono_err :
        forall (chronos : list (trans_type * option chrono_type)),
          GetChrono chronos t None ->
          IncrementChrono t chronos None
    | IncrementChrono_some :
        forall (chronos : list (trans_type * option chrono_type))
               (opt_chrono : option chrono_type)
               (cnt : nat)
               (min_t max_t : nat_star)
               (max_is_infinite : bool)
               (min_t_le_max_t : (int min_t) <= (int max_t))
               (final_chronos : list (trans_type * option chrono_type)),
          GetChrono chronos t (Some opt_chrono) ->
          opt_chrono = Some (mk_chrono cnt min_t max_t max_is_infinite min_t_le_max_t) ->
          ReplaceChrono (mk_chrono cnt min_t max_t max_is_infinite min_t_le_max_t)
                        (mk_chrono (cnt + 1) min_t max_t max_is_infinite min_t_le_max_t)
                        chronos
                        final_chronos ->
          IncrementChrono t chronos (Some final_chronos)
    | IncrementChrono_none :
        forall (chronos : list (trans_type * option chrono_type))
               (opt_chrono : option chrono_type),
          GetChrono chronos t (Some opt_chrono) ->
          opt_chrono = None ->
          IncrementChrono t chronos (Some chronos).
                    
    (*** Correctness proof : increment_chrono ***)
    Theorem increment_chrono_correct :
      forall (t : trans_type)
             (chronos : list (trans_type * option chrono_type))
             (opt_final_chronos : option (list (trans_type * option chrono_type))),
        increment_chrono t chronos = opt_final_chronos ->
        IncrementChrono t chronos opt_final_chronos.
    Proof.
      intros t chronos.  
      functional induction (increment_chrono t chronos)
                 using  increment_chrono_ind; intros.
      (* Case get_chrono returns Some (Some chrono). *)
      - rewrite <- H; apply IncrementChrono_some
                        with (opt_chrono := (Some {| cnt := cnt0;
                                                     min_t := min_t0;
                                                     max_t := max_t0;
                                                     max_is_infinite := max_is_infinite0;
                                                     min_t_le_max_t := min_t_le_max_t0 |}))
                             (cnt := cnt0)
                             (min_t := min_t0)
                             (max_t := max_t0)
                             (max_is_infinite := max_is_infinite0)
                             (min_t_le_max_t := min_t_le_max_t0).
        + apply get_chrono_correct; auto.
        + auto.
        + apply replace_chrono_correct; auto.
      (* Case get_chrono returns Some (None) *)
      - rewrite <- H; apply IncrementChrono_none with (opt_chrono := None).
        + apply get_chrono_correct; auto.
        + auto.
      (* Case get_chrono returns an error. *)
      - rewrite <- H; apply IncrementChrono_err; apply get_chrono_correct; auto.
    Qed.

    (*** Completeness proof increment_chrono ***)
    Theorem increment_chrono_complete :
      forall (t : trans_type)
             (chronos : list (trans_type * option chrono_type))
             (opt_final_chronos : option (list (trans_type * option chrono_type))),
        IncrementChrono t chronos opt_final_chronos ->
        increment_chrono t chronos = opt_final_chronos.
    Proof.
      intros t chronos opt_final_chronos H; elim H; intros.
      (* IncrementChrono_err *)
      - apply get_chrono_compl in H0; unfold increment_chrono; rewrite H0; auto.
      (* IncrementChrono_some *)
      - apply get_chrono_compl in H0; apply replace_chrono_compl in H2.
        unfold increment_chrono; rewrite H0; rewrite H1; rewrite H2; auto.
      (* IncrementChrono_none *)
      - apply get_chrono_compl in H0; unfold increment_chrono; rewrite H0; rewrite H1; auto.
    Qed.

    (* Lemma : Proves that increment_chrono preserves
     *         the structure of the chronos passed as argument.  
     *)
    Lemma increment_chrono_same_struct :
      forall (t : trans_type)
             (chronos chronos': list (trans_type * option chrono_type)),
        increment_chrono t chronos = Some chronos' ->
        ChronosHaveSameStruct chronos chronos'.
    Proof.
      intros t chronos.
      functional induction (increment_chrono t chronos)
                 using increment_chrono_ind;
        intros.
      - injection H; intros.
        rewrite <- H0.
        unfold ChronosHaveSameStruct; symmetry.
        apply replace_chrono_same_struct.
      - injection H; intros; rewrite H0; unfold ChronosHaveSameStruct; auto.
      - inversion H.
    Qed.
    
    (* Lemma : For all transition t and chronos, 
     *         increment_chrono t chronos returns no error
     *         if t is referenced in chronos.
     *)
    Lemma increment_chrono_no_error :
      forall (t : trans_type)
             (chronos : list (trans_type * option chrono_type)),
        In t (fst (split chronos)) ->
        exists v : list (trans_type * option chrono_type),
          increment_chrono t chronos = Some v.
    Proof.
      intros t chronos H.
      functional induction (increment_chrono t chronos)
                 using increment_chrono_ind.    
      (* Base case *)
      - exists(replace_chrono
                 {| cnt := cnt0;
                    min_t := min_t0;
                    max_t := max_t0;
                    max_is_infinite := max_is_infinite0;
                    min_t_le_max_t := min_t_le_max_t0 |}
                 {| cnt := cnt0 + 1;
                    min_t := min_t0;
                    max_t := max_t0;
                    max_is_infinite := max_is_infinite0;
                    min_t_le_max_t := min_t_le_max_t0 |}
                 chronos).
        auto.
      (* Case opt_chrono = None *)
      - exists chronos; auto.    
      (* Case get_chrono = None, not possible. *)
      - apply get_chrono_no_error in H.
        elim H; intros; rewrite H0 in e; inversion e.      
    Qed.             
    
    (*  
     * Function : Returns an option to a list of pair (trans, option chrono_type),
     *            where all chronos associated to transition in the list 
     *            transs have been incremented.
     *            
     *            Raises an error (None value) if an incrementation
     *            went wrong for one of the transition of the list.
     * 
     *)
    Fixpoint increment_all_chronos
             (chronos : list (trans_type * option chrono_type))
             (transs : list trans_type) :
      option (list (trans_type * option chrono_type)) :=
      match transs with
      | t :: tail => match increment_chrono t chronos with
                     (* If increment_chrono returns Some new_chronos, 
                      * then passes new_chronos as argument of recursive call.
                      *)
                     | Some new_chronos => increment_all_chronos new_chronos tail
                     (* Case of error!!! *)
                     | None => None
                     end
      (* Recursion base case. *)
      | [] => Some chronos
      end.

    Functional Scheme increment_all_chronos_ind := Induction for increment_all_chronos Sort Prop.
    
    (*** Formal specification : increment_all_chronos ***)
    Inductive IncrementAllChronos
              (chronos : list (trans_type * option chrono_type)) :       
      list trans_type ->
      option (list (trans_type * option chrono_type)) ->
      Prop :=      
    | IncrementAllChronos_nil :
        IncrementAllChronos chronos [] (Some chronos)
    | IncrementAllChronos_cons :
        forall (t : trans_type)
               (transs : list trans_type)
               (new_chronos : list (trans_type * option chrono_type))
               (opt_final_chronos : option (list (trans_type * option chrono_type))),
          IncrementChrono t chronos (Some new_chronos) ->
          IncrementAllChronos new_chronos transs opt_final_chronos ->  
          IncrementAllChronos chronos (t :: transs) opt_final_chronos
    | IncrementAllChronos_err :
        forall (t : trans_type)
               (transs : list trans_type),
          IncrementChrono t chronos None ->
          IncrementAllChronos chronos (t :: transs) None.
    
    (*** Correctness proof : increment_all_chronos ***)
    Theorem increment_all_chronos_correct :
      forall (chronos : list (trans_type * option chrono_type))
             (transs : list trans_type)
             (opt_final_chronos : option (list (trans_type * option chrono_type))),
        increment_all_chronos chronos transs = opt_final_chronos ->
        IncrementAllChronos chronos transs opt_final_chronos.
    Proof.
      intros chronos transs.  
      functional induction (increment_all_chronos chronos transs)
                 using  increment_all_chronos_ind; intros.
      (* Base case, transs = [] *)
      - rewrite <- H; apply IncrementAllChronos_nil.
      (* Case increment_chrono returns Some value *)
      - rewrite <- H; apply IncrementAllChronos_cons with (new_chronos := new_chronos).
        + apply increment_chrono_correct; auto.
        + apply IHo; auto.
      (* Error case, increment_chrono returns None *)
      - rewrite <- H; apply IncrementAllChronos_err; apply increment_chrono_correct; auto.
    Qed.

    (*** Completeness proof : increment_all_chronos ***)
    Theorem increment_all_chronos_complete :
      forall (chronos : list (trans_type * option chrono_type))
             (transs : list trans_type)
             (opt_final_chronos : option (list (trans_type * option chrono_type))),
        IncrementAllChronos chronos transs opt_final_chronos ->
        increment_all_chronos chronos transs = opt_final_chronos.
    Proof.
      intros chronos transs opt_final_chronos H; elim H; intros.
      (* IncrementAllChronos_nil *)
      - simpl; auto.
      (* IncrementAllChronos_cons *)
      - apply increment_chrono_complete in H0.
        unfold increment_all_chronos; rewrite H0; auto.
      (* IncrementAllChronos_err *)
      - apply increment_chrono_complete in H0.
        unfold increment_all_chronos; rewrite H0; auto.
    Qed.
    
    (* Lemma : Proves that increment_all_chronos preserves
     *         the structure of the chronos passed as argument.  
     *)
    Lemma increment_all_chronos_same_struct :
      forall (chronos : list (trans_type * option chrono_type))
             (transs : list trans_type)
             (incremented_chronos : list (trans_type * option chrono_type)),
        increment_all_chronos chronos transs = Some incremented_chronos ->
        ChronosHaveSameStruct chronos incremented_chronos.
    Proof.
      intros chronos transs.
      functional induction (increment_all_chronos chronos transs)
                 using increment_all_chronos_ind; intros.
      - injection H; intros; rewrite H0; unfold ChronosHaveSameStruct; auto.
      - apply increment_chrono_same_struct in e0.
        apply IHo in H.
        unfold ChronosHaveSameStruct.
        unfold ChronosHaveSameStruct in e0.
        unfold ChronosHaveSameStruct in H.
        transitivity (fst (split new_chronos)); [auto | auto].
      - inversion H.
    Qed.
    
    (* Lemma : Proves that increment_all_chronos returns no error 
     *         if all transitions of the list transs
     *         are referenced in chronos.
     *)
    Lemma increment_all_chronos_no_error :
      forall (chronos : list (trans_type * option chrono_type))
             (transs : list trans_type),
        incl transs (fst (split chronos)) ->
        exists v : list (trans_type * option chrono_type),
          increment_all_chronos chronos transs = Some v.
    Proof.
      unfold incl.
      intros chronos transs;
        functional induction (increment_all_chronos chronos transs)
                   using increment_all_chronos_ind;
        intros.
      (* Base case, transs = []. *)
      - exists chronos0; auto.
      (* Case increment_chrono returns new_chronos. *)
      - apply IHo; intros.
        apply (in_cons t) in H0.
        apply H in H0.
        apply increment_chrono_same_struct in e0.
        unfold ChronosHaveSameStruct in e0.
        rewrite <- e0.
        auto.
      (* Case increment_chrono returns None, 
       * impossible regarding the hypothesis 
       *)
      - assert (H' := (in_eq t tail)).
        apply H in H'.
        apply (increment_chrono_no_error t) in H'.
        elim H'; intros; rewrite e0 in H0; inversion H0.
    Qed.
    
    (**************************************************************)
    (**************************************************************)

    (*  
     * Function : Returns a new list of chronos, where the time
     *            counter of transition t has been set to zero.
     *            Raises an error (None value) if get_chrono returns
     *            an error.
     *)
    Definition reset_chrono
               (t : trans_type) 
               (chronos : list (trans_type * option chrono_type)) :
      option (list (trans_type * option chrono_type)) :=
      match get_chrono chronos t with
      | Some opt_chrono =>
        match opt_chrono with
        (* Replaces old chrono by a reset chrono in chronos list. *)
        | Some (mk_chrono cnt min_t max_t max_is_infinite min_t_le_max_t) =>
          Some (replace_chrono (mk_chrono cnt min_t max_t max_is_infinite min_t_le_max_t)
                               (mk_chrono 0 min_t max_t max_is_infinite min_t_le_max_t)
                               chronos)
        (* Otherwise, nothing to reset, t has no associated chrono. *)
        | None => Some chronos
        end
      (* Case of error!!! *)
      | None => None
      end.

    Functional Scheme reset_chrono_ind := Induction for reset_chrono Sort Prop. 
    
    (*** Formal specification : reset_chrono ***)
    Inductive ResetChrono (t : trans_type) :
      list (trans_type * option chrono_type) ->
      option (list (trans_type * option chrono_type)) ->
      Prop :=
    | ResetChrono_err :
        forall (chronos : list (trans_type * option chrono_type)),
          GetChrono chronos t None ->
          ResetChrono t chronos None
    | ResetChrono_some :
        forall (chronos : list (trans_type * option chrono_type))
               (opt_chrono : option chrono_type)
               (cnt : nat)
               (min_t max_t : nat_star)
               (max_is_infinite : bool)
               (min_t_le_max_t : (int min_t) <= (int max_t))
               (final_chronos : list (trans_type * option chrono_type)),
          GetChrono chronos t (Some opt_chrono) ->
          opt_chrono = Some (mk_chrono cnt min_t max_t max_is_infinite min_t_le_max_t) ->
          ReplaceChrono (mk_chrono cnt min_t max_t max_is_infinite min_t_le_max_t)
                        (mk_chrono 0 min_t max_t max_is_infinite min_t_le_max_t)
                        chronos
                        final_chronos ->
          ResetChrono t chronos (Some final_chronos)
    | ResetChrono_none :
        forall (chronos : list (trans_type * option chrono_type))
               (opt_chrono : option chrono_type),
          GetChrono chronos t (Some opt_chrono) ->
          opt_chrono = None ->
          ResetChrono t chronos (Some chronos).
                    
    (*** Correctness proof : reset_chrono ***)
    Theorem reset_chrono_correct :
      forall (t : trans_type)
             (chronos : list (trans_type * option chrono_type))
             (opt_final_chronos : option (list (trans_type * option chrono_type))),
        reset_chrono t chronos = opt_final_chronos ->
        ResetChrono t chronos opt_final_chronos.
    Proof.
      intros t chronos.  
      functional induction (reset_chrono t chronos)
                 using  reset_chrono_ind; intros.
      (* Case get_chrono returns Some (Some chrono). *)
      - rewrite <- H; apply ResetChrono_some
                        with (opt_chrono := (Some {| cnt := cnt0;
                                                     min_t := min_t0;
                                                     max_t := max_t0;
                                                     max_is_infinite := max_is_infinite0;
                                                     min_t_le_max_t := min_t_le_max_t0 |}))
                             (cnt := cnt0)
                             (min_t := min_t0)
                             (max_t := max_t0)
                             (max_is_infinite := max_is_infinite0)
                             (min_t_le_max_t := min_t_le_max_t0).
        + apply get_chrono_correct; auto.
        + auto.
        + apply replace_chrono_correct; auto.
      (* Case get_chrono returns Some (None) *)
      - rewrite <- H; apply ResetChrono_none with (opt_chrono := None).
        + apply get_chrono_correct; auto.
        + auto.
      (* Case get_chrono returns an error. *)
      - rewrite <- H; apply ResetChrono_err; apply get_chrono_correct; auto.
    Qed.

    (*** Completeness proof reset_chrono ***)
    Theorem reset_chrono_complete :
      forall (t : trans_type)
             (chronos : list (trans_type * option chrono_type))
             (opt_final_chronos : option (list (trans_type * option chrono_type))),
        ResetChrono t chronos opt_final_chronos ->
        reset_chrono t chronos = opt_final_chronos.
    Proof.
      intros t chronos opt_final_chronos H; elim H; intros.
      (* ResetChrono_err *)
      - apply get_chrono_compl in H0; unfold reset_chrono; rewrite H0; auto.
      (* ResetChrono_some *)
      - apply get_chrono_compl in H0; apply replace_chrono_compl in H2.
        unfold reset_chrono; rewrite H0; rewrite H1; rewrite H2; auto.
      (* ResetChrono_none *)
      - apply get_chrono_compl in H0; unfold reset_chrono; rewrite H0; rewrite H1; auto.
    Qed.

    (* Lemma : Proves that reset_chrono preserves
     *         the structure of the chronos passed as argument.  
     *)
    Lemma reset_chrono_same_struct :
      forall (t : trans_type)
             (chronos chronos': list (trans_type * option chrono_type)),
        reset_chrono t chronos = Some chronos' ->
        ChronosHaveSameStruct chronos chronos'.
    Proof.
      intros t chronos.
      functional induction (reset_chrono t chronos)
                 using reset_chrono_ind;
        intros.
      - injection H; intros.
        rewrite <- H0.
        unfold ChronosHaveSameStruct; symmetry.
        apply replace_chrono_same_struct.
      - injection H; intros; rewrite H0; unfold ChronosHaveSameStruct; auto.
      - inversion H.
    Qed.
    
    (* Lemma : For all transition t and chronos, 
     *         reset_chrono t chronos returns no error
     *         if t is referenced in chronos.
     *)
    Lemma reset_chrono_no_error :
      forall (t : trans_type)
             (chronos : list (trans_type * option chrono_type)),
        In t (fst (split chronos)) ->
        exists v : list (trans_type * option chrono_type),
          reset_chrono t chronos = Some v.
    Proof.
      intros t chronos H.
      functional induction (reset_chrono t chronos)
                 using reset_chrono_ind.    
      (* Base case *)
      - exists(replace_chrono
                 {| cnt := cnt0;
                    min_t := min_t0;
                    max_t := max_t0;
                    max_is_infinite := max_is_infinite0;
                    min_t_le_max_t := min_t_le_max_t0 |}
                 {| cnt := 0;
                    min_t := min_t0;
                    max_t := max_t0;
                    max_is_infinite := max_is_infinite0;
                    min_t_le_max_t := min_t_le_max_t0 |}
                 chronos).
        auto.
      (* Case opt_chrono = None *)
      - exists chronos; auto.    
      (* Case get_chrono = None, not possible. *)
      - apply get_chrono_no_error in H.
        elim H; intros; rewrite H0 in e; inversion e.      
    Qed.
    
    (* 
     * Reseting the counter ought to be smarter :
     * 
     * 1) When should it be done ?  
     *  ----> at the end of a cycle or rather in stpn_sub_fire_pre !
     * 2) Which transitions are concerned ?
     *  ----> The ones disabled during the cycle, even in a transitive way.
     *
     *)
    
    (*  
     * Function : Returns an option to a list of pair (trans, option chrono_type),
     *            where all chronos associated to transition in the list 
     *            transs have been set to zero.
     *            
     *            Raises an error (None value) if a reseting
     *            went wrong for one of the transition of the list.
     * 
     *)
    Fixpoint reset_all_chronos
             (chronos : list (trans_type * option chrono_type))
             (transs : list trans_type) :
      option (list (trans_type * option chrono_type)) :=
      match transs with
      | t :: tail =>
        match reset_chrono t chronos with
        (* If reset_chrono returns Some new_chronos, 
         * then passes new_chronos as argument of recursive call.
         *)
        | Some new_chronos =>
          reset_all_chronos new_chronos tail
        (* Case of error!!! *)
        | None => None
        end
      (* Recursion base case. *)
      | [] => Some chronos
      end.

    Functional Scheme reset_all_chronos_ind := Induction for reset_all_chronos Sort Prop.
    
    (*** Formal specification : reset_all_chronos ***)
    Inductive ResetAllChronos (chronos : list (trans_type * option chrono_type)) :       
      list trans_type ->
      option (list (trans_type * option chrono_type)) ->
      Prop :=      
    | ResetAllChronos_nil :
        ResetAllChronos chronos [] (Some chronos)
    | ResetAllChronos_cons :
        forall (t : trans_type)
               (transs : list trans_type)
               (new_chronos : list (trans_type * option chrono_type))
               (opt_final_chronos : option (list (trans_type * option chrono_type))),
          ResetChrono t chronos (Some new_chronos) ->
          ResetAllChronos new_chronos transs opt_final_chronos ->  
          ResetAllChronos chronos (t :: transs) opt_final_chronos
    | ResetAllChronos_err :
        forall (t : trans_type)
               (transs : list trans_type),
          ResetChrono t chronos None ->
          ResetAllChronos chronos (t :: transs) None.
    
    (*** Correctness proof : reset_all_chronos ***)
    Theorem reset_all_chronos_correct :
      forall (chronos : list (trans_type * option chrono_type))
             (transs : list trans_type)
             (opt_final_chronos : option (list (trans_type * option chrono_type))),
        reset_all_chronos chronos transs = opt_final_chronos ->
        ResetAllChronos chronos transs opt_final_chronos.
    Proof.
      intros chronos transs.  
      functional induction (reset_all_chronos chronos transs)
                 using  reset_all_chronos_ind; intros.
      (* Base case, transs = [] *)
      - rewrite <- H; apply ResetAllChronos_nil.
      (* Case reset_chrono returns Some value *)
      - rewrite <- H; apply ResetAllChronos_cons with (new_chronos := new_chronos).
        + apply reset_chrono_correct; auto.
        + apply IHo; auto.
      (* Error case, reset_chrono returns None *)
      - rewrite <- H; apply ResetAllChronos_err; apply reset_chrono_correct; auto.
    Qed.

    (*** Completeness proof : reset_all_chronos ***)
    Theorem reset_all_chronos_complete :
      forall (chronos : list (trans_type * option chrono_type))
             (transs : list trans_type)
             (opt_final_chronos : option (list (trans_type * option chrono_type))),
        ResetAllChronos chronos transs opt_final_chronos ->
        reset_all_chronos chronos transs = opt_final_chronos.
    Proof.
      intros chronos transs opt_final_chronos H; elim H; intros.
      (* ResetAllChronos_nil *)
      - simpl; auto.
      (* ResetAllChronos_cons *)
      - apply reset_chrono_complete in H0.
        unfold reset_all_chronos; rewrite H0; auto.
      (* ResetAllChronos_err *)
      - apply reset_chrono_complete in H0.
        unfold reset_all_chronos; rewrite H0; auto.
    Qed.

    (* Lemma : Proves that reset_all_chronos preserves
     *         the structure of the chronos passed as argument.  
     *)
    Lemma reset_all_chronos_same_struct :
      forall (chronos : list (trans_type * option chrono_type))
             (transs : list trans_type)
             (reset_chronos : list (trans_type * option chrono_type)),
        reset_all_chronos chronos transs = Some reset_chronos ->
        ChronosHaveSameStruct chronos reset_chronos.
    Proof.
      intros chronos transs.
      functional induction (reset_all_chronos chronos transs)
                 using reset_all_chronos_ind; intros.
      - injection H; intros; rewrite H0; unfold ChronosHaveSameStruct; auto.
      - apply reset_chrono_same_struct in e0.
        apply IHo in H.
        unfold ChronosHaveSameStruct.
        unfold ChronosHaveSameStruct in e0.
        unfold ChronosHaveSameStruct in H.
        transitivity (fst (split new_chronos)); [auto | auto].
      - inversion H.
    Qed.
    
    (* Lemma : Proves that reset_all_chronos returns no error 
     *         if all transitions of the list transs
     *         are referenced in chronos.
     *)
    Lemma reset_all_chronos_no_error :
      forall (chronos : list (trans_type * option chrono_type))
             (transs : list trans_type),
        incl transs (fst (split chronos)) ->
        exists v : list (trans_type * option chrono_type),
          reset_all_chronos chronos transs = Some v.
    Proof.
      unfold incl.
      intros chronos transs;
        functional induction (reset_all_chronos chronos transs)
                   using reset_all_chronos_ind;
        intros.
      (* Base case, transs = []. *)
      - exists chronos0; auto.
      (* Case reset_chrono returns new_chronos. *)
      - apply IHo; intros.
        apply (in_cons t) in H0.
        apply H in H0.
        apply reset_chrono_same_struct in e0.
        unfold ChronosHaveSameStruct in e0.
        rewrite <- e0.
        auto.
      (* Case reset_chrono returns None, 
       * impossible regarding the hypothesis 
       *)
      - assert (H' := (in_eq t tail)).
        apply H in H'.
        apply (reset_chrono_no_error t) in H'.
        elim H'; intros; rewrite e0 in H0; inversion H0.
    Qed.

End Chrono.

(*==============================================================*)
(*================= LIST SENSITIZED SECTION  ===================*)
(*==============================================================*)
Section ListSensitized.

  (*  
   * Function : Returns true if transition t is 
   *            sensitized by marking m, false otherwise.
   *
   *            The difference with the check_all_edges function (SPN.v)
   *            is that only one marking "m" is considered instead
   *            of two (one steady and one decreasing).
   *)
  Definition is_sensitized
             (neighbours_t : neighbours_type)
             (pre test inhib : weight_type)
             (m : marking_type)
             (t : trans_type) : option bool :=
    match (check_pre_or_test (pre t) m (pre_pl neighbours_t) true) with
    | Some check_pre_result =>  
      match (check_pre_or_test (test t) m (test_pl neighbours_t) true) with
      | Some check_test_result =>
        match check_inhib (inhib t) m (inhib_pl neighbours_t) true with
        | Some check_inhib_result =>
          Some (check_pre_result && check_test_result && check_inhib_result)
        (* Case of error!! *)
        | None => None
        end
      (* Case of error!! *)
      | None => None
      end
    (* Case of error!! *)
    | None => None
    end.

  Functional Scheme is_sensitized_ind := Induction for is_sensitized Sort Prop.
  
  (*** Formal specification : is_sensitized ***)
  Inductive IsSensitized
            (neighbours_t : neighbours_type)
            (pre test inhib : weight_type)
            (m : marking_type)
            (t : trans_type) : option bool -> Prop :=
  | IsSensitized_some :
      forall (check_pre_result check_test_result check_inhib_result : bool),
        CheckPreOrTest (pre t) m (pre_pl neighbours_t) true (Some check_pre_result) /\
        CheckPreOrTest (test t) m (test_pl neighbours_t) true (Some check_test_result) /\
        CheckInhib (inhib t) m (inhib_pl neighbours_t) true (Some check_inhib_result) ->
        IsSensitized neighbours_t pre test inhib m t
                     (Some (check_pre_result && check_test_result && check_inhib_result))
  | IsSensitized_err :
      CheckPreOrTest (pre t) m (pre_pl neighbours_t) true None \/
      CheckPreOrTest (test t) m (test_pl neighbours_t) true None \/
      CheckInhib (inhib t) m (inhib_pl neighbours_t) true None ->
      IsSensitized neighbours_t pre test inhib m t None.

  (*** Correctness proof : is_sensitized *)
  Theorem is_sensitized_correct :
    forall (neighbours_t : neighbours_type)
           (pre test inhib: weight_type)
           (m : marking_type)
           (t : trans_type)
           (optionb : option bool),
      is_sensitized neighbours_t pre test inhib m t = optionb ->
      IsSensitized neighbours_t pre test inhib m t optionb.
  Proof.
    intros neighbours_t pre test inhib m t.
    functional induction (is_sensitized neighbours_t pre test inhib m t)
               using is_sensitized_ind; intros.
    (* Case check_pre, check_test and check_inhib returned some value. *)
    - rewrite <- H; apply IsSensitized_some.
      split; [apply check_pre_or_test_correct; auto |
              split; [apply check_pre_or_test_correct; auto |
                      apply check_inhib_correct; auto]].            
    (* Case of error 1. check_inhib returns None. *)
    - rewrite <- H; apply IsSensitized_err.
      apply check_inhib_correct in e1; auto.
    (* Case of error 2. check_test returns None.  *)
    - rewrite <- H; apply IsSensitized_err.
      apply check_pre_or_test_correct in e0; auto.
    (* Case of error 3. check_pre returns None. *)
    - rewrite <- H; apply IsSensitized_err.
      apply check_pre_or_test_correct in e; auto.
  Qed.

  (*** Completeness proof : is_sensitized ***)
  Theorem is_sensitized_compl :
    forall (neighbours_t : neighbours_type)
           (pre test inhib: weight_type)
           (m : marking_type)
           (t : trans_type)
           (optionb : option bool),
      IsSensitized neighbours_t pre test inhib m t optionb ->
      is_sensitized neighbours_t pre test inhib m t = optionb.
  Proof.
    intros; elim  H; intros.
    (* Case IsSensitized_some *)
    - unfold is_sensitized.
      elim H0; clear H0; intros.
      elim H1; clear H1; intros.
      repeat (((apply check_pre_or_test_compl in H0; rewrite H0) ||
               (apply check_pre_or_test_compl in H1; rewrite H1) ||
               (apply check_inhib_compl in H2; rewrite H2));
              auto).
    (* Case IsSensitized_err *)
    - unfold is_sensitized.
      elim H0; clear H0; intros.
      + apply check_pre_or_test_compl in H0; rewrite H0; auto.
      + elim H0; clear H0; intros.
        -- case (check_pre_or_test (pre t) m (pre_pl neighbours_t) true).
           ++ intro; apply check_pre_or_test_compl in H0; rewrite H0; auto.
           ++ auto.
        -- case (check_pre_or_test (pre t) m (pre_pl neighbours_t) true).
           +++ case (check_pre_or_test (test t) m (test_pl neighbours_t) true);
                 [ apply check_inhib_compl in H0; rewrite H0; auto | intro; auto ].
           +++ auto.
  Qed.

  (* Lemma : Proves that is_sensitized returns no error if
   *         the places in (pre_pl neighbours_t), (inhib_pl neighbours_t) 
   *         and (test_pl neighbours_t) are referenced in marking m.  
   *
   *)
  Lemma is_sensitized_no_error :
    forall (neighbours_t : neighbours_type)
           (pre test inhib : weight_type)
           (m : marking_type)
           (t : trans_type),
      PlacesAreRefInMarking (pre_pl neighbours_t) m ->
      PlacesAreRefInMarking (test_pl neighbours_t) m ->
      PlacesAreRefInMarking (inhib_pl neighbours_t) m ->
      exists v : bool,
        is_sensitized neighbours_t pre test inhib m t = Some v.
  Proof.
    unfold PlacesAreRefInMarking.
    intros neighbours_t pre test inhib m t.
    functional induction (is_sensitized neighbours_t pre test inhib m t)
               using is_sensitized_ind; intros.
    (* Case all went well. *)
    - exists (check_pre_result && check_test_result && check_inhib_result); auto.
    (* Case check_inhib = None, impossible regarding hypothesis. *)
    - apply check_inhib_no_error with (inhib_arcs_t := inhib t)
                                      (check_result := true) in H1.
      elim H1; intros.
      rewrite e1 in H2; inversion H2.
    (* Case check_test = None, impossible regarding hypothesis. *)
    - apply check_pre_or_test_no_error with (pre_or_test_arcs_t := test t)
                                            (check_result := true) in H0.
      elim H0; intros.
      rewrite e0 in H2; inversion H2.
    (* Case check_pre = None, impossible regarding hypothesis. *)
    - apply check_pre_or_test_no_error with (pre_or_test_arcs_t := pre t)
                                            (check_result := true) in H.
      elim H; intros.
      rewrite e in H2; inversion H2.
  Qed.
  
  (* 
   * Useless fonction for SPN but useful for 
   *
   * -  _asynchronous_ Petri nets
   * -  STPN (and SITPN by extension) 
   *
   * Needed to list sensitized transitions, to increment 
   * time counters for these transitions at the beginning of the cycle.
   * 
   * Needed to list disabled transitions, to reset
   * time counters for these transitions at the beginning of the cycle.    
   *)

  (*  
   * Function :  Returns the list of sensitized transitions
   *             contained in transs.
   *             
   *             Raises an error (None value) if get_neighbours or
   *             is_sensitized return None.
   *)
  Fixpoint list_sensitized_aux 
           (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type) 
           (m : marking_type)
           (sensitized_transs : list trans_type)
           (transs : list trans_type) :
    option (list trans_type) :=
    match transs with
    | t :: tail =>
      (* Checks if t has neighbours *)
      match get_neighbours lneighbours t with
      (* Case t has Some neighbours *)
      | Some neighbours_t =>
        (* Checks if t is sensitized. *)
        match is_sensitized neighbours_t pre test inhib m t with
        (* Case t is sensitized. *)
        | Some true =>
          list_sensitized_aux lneighbours pre test inhib m (t :: sensitized_transs) tail
        (* Case t is not sensitized. *)
        | Some false =>
          list_sensitized_aux lneighbours pre test inhib m sensitized_transs tail
        (* Error case!!! *)
        | None => None
        end
      (* Error case!!! *)
      | None => None
      end
    (* Recursion base case. *)
    | [] => Some sensitized_transs
    end.

  (*** Formal specification : list_sensitized_aux ***)
  Inductive ListSensitizedAux
            (lneighbours : list (trans_type * neighbours_type))
            (pre test inhib : weight_type) 
            (m : marking_type)
            (sensitized_transs : list trans_type) :
    list trans_type -> (* sometranss *)
    option (list trans_type) -> (* opt_sensitized_transs *)
    Prop :=
  | ListSensitizedAux_nil :
      ListSensitizedAux lneighbours pre test inhib m sensitized_transs []
                        (Some sensitized_transs)      
  | ListSensitizedAux_get_neighbours_err :
      forall (transs : list trans_type)
             (t : trans_type),
        GetNeighbours lneighbours t None ->
        ListSensitizedAux lneighbours pre test inhib m sensitized_transs (t :: transs) None      
  | ListSensitizedAux_is_sensitized_err :
      forall (transs : list trans_type)
             (t : trans_type)
             (neighbours_t : neighbours_type),
        GetNeighbours lneighbours t (Some neighbours_t) ->
        IsSensitized neighbours_t pre test inhib m t None ->
        ListSensitizedAux lneighbours pre test inhib m sensitized_transs (t :: transs) None
  | ListSensitizedAux_is_sensitized_true :
      forall (transs : list trans_type)
             (t : trans_type)
             (neighbours_t : neighbours_type)
             (opt_sensitized_transs : option (list trans_type)),
        GetNeighbours lneighbours t (Some neighbours_t) ->
        IsSensitized neighbours_t pre test inhib m t (Some true) ->
        ListSensitizedAux lneighbours pre test inhib m (t :: sensitized_transs) transs
                          opt_sensitized_transs ->
        ListSensitizedAux lneighbours pre test inhib m sensitized_transs (t :: transs)
                          opt_sensitized_transs
  | ListSensitizedAux_is_sensitized_false :
      forall (transs : list trans_type)
             (t : trans_type)
             (neighbours_t : neighbours_type)
             (opt_sensitized_transs : option (list trans_type)),
        GetNeighbours lneighbours t (Some neighbours_t) ->
        IsSensitized neighbours_t pre test inhib m t (Some false) ->
        ListSensitizedAux lneighbours pre test inhib m sensitized_transs transs
                          opt_sensitized_transs ->
        ListSensitizedAux lneighbours pre test inhib m sensitized_transs (t :: transs)
                          opt_sensitized_transs.
  
  Functional Scheme list_sensitized_aux_ind := Induction for list_sensitized_aux Sort Prop.

  (*** Correctness proof : list_sensitized_aux ***)
  Theorem list_sensitized_aux_correct :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)
           (m : marking_type)
           (sensitized_transs transs : list trans_type)
           (opt_sensitized_transs : option (list trans_type)),
      list_sensitized_aux lneighbours pre test inhib m
                          sensitized_transs transs = opt_sensitized_transs ->
      ListSensitizedAux lneighbours pre test inhib m
                        sensitized_transs transs opt_sensitized_transs.
  Proof.
    intros lneighbours pre test inhib m sensitized_transs transs.
    functional induction (list_sensitized_aux lneighbours pre test inhib m
                                              sensitized_transs transs)
               using list_sensitized_aux_ind; intros.
    (* Case transs = [] *)
    - rewrite <- H; apply ListSensitizedAux_nil.
    (* Case is_sensitized = true *)
    - apply ListSensitizedAux_is_sensitized_true with (neighbours_t := neighbours_t).
      + apply get_neighbours_correct; auto.
      + apply is_sensitized_correct; auto.
      + rewrite <- H; apply IHo; auto.
    (* Case is_sensitized = false *)
    - apply ListSensitizedAux_is_sensitized_false with (neighbours_t := neighbours_t).
      + apply get_neighbours_correct; auto.
      + apply is_sensitized_correct; auto. 
      + rewrite <- H; apply IHo; auto.        
    (* Error case, is_sensitized = None *)
    - rewrite <- H; apply ListSensitizedAux_is_sensitized_err with (neighbours_t := neighbours_t).
      + apply get_neighbours_correct; auto.
      + apply is_sensitized_correct; auto.
    (* Error case, get_neighbours = None *)
    - rewrite <- H; apply ListSensitizedAux_get_neighbours_err.
      + apply get_neighbours_correct; auto.
  Qed.

  (*** Completeness proof : list_sensitized_aux ***)
  Theorem list_sensitized_aux_complete :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)
           (m : marking_type)
           (sensitized_transs transs : list trans_type)
           (opt_sensitized_transs : option (list trans_type)),
      ListSensitizedAux lneighbours pre test inhib m
                        sensitized_transs transs opt_sensitized_transs ->
      list_sensitized_aux lneighbours pre test inhib m
                          sensitized_transs transs = opt_sensitized_transs.
  Proof.
    intros; elim H; intros.
    (* Case ListSensitizedAux_nil *)
    - simpl; auto.
    (* Case ListSensitizedAux_get_neighbours_err *)
    - simpl; apply get_neighbours_compl in H0; rewrite H0; auto.
    (* Case ListSensitizedAux_is_sensitized_err *)
    - simpl;
        apply get_neighbours_compl in H0; rewrite H0;
        apply is_sensitized_compl in H1; rewrite H1; auto.
    (* Case ListSensitizedAux_is_sensitized_true *)
    - simpl;
        apply get_neighbours_compl in H0; rewrite H0;
        apply is_sensitized_compl in H1; rewrite H1; auto.
    (* Case ListSensitizedAux_is_sensitized_false *)
    - simpl;
        apply get_neighbours_compl in H0; rewrite H0;
        apply is_sensitized_compl in H1; rewrite H1; auto.
  Qed.

  (*  
   * Lemma : If list_sensitized_aux returns Some final_sensitized then
   *         all transitions in final_sensitized are in sensitized_transs ++ transs.
   *)
  Lemma list_sensitized_aux_incl_transs :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)
           (m : marking_type)
           (sensitized_transs transs final_sensitized : list trans_type),
      list_sensitized_aux lneighbours pre test inhib m sensitized_transs transs =
      Some final_sensitized ->
      incl final_sensitized (sensitized_transs ++ transs).
  Proof.
    unfold incl.
    intros lneighbours pre test inhib m sensitized_transs transs.
    functional induction (list_sensitized_aux lneighbours pre test inhib m sensitized_transs transs)
               using list_sensitized_aux_ind; intros.
    (* Base case, transs = []. *)
    - injection H; intros.
      rewrite <- H1 in H0.
      rewrite <- app_nil_end; auto.
    (* Case is_sensitized = true. *)
    - generalize (IHo final_sensitized H a H0); intro.
      apply in_app_or in H1.
      elim H1; intros.
      + apply in_or_app.
        apply in_inv in H2.
        elim H2; intros.
        -- rewrite H3; right; apply in_eq.
        -- left; auto.
      + apply in_or_app.
        apply (in_cons t) in H2.
        right; auto.      
    (* Case is_sensitized = false. *)
    - generalize (IHo final_sensitized H a H0); intro.
      apply in_app_or in H1.
      elim H1; intros.
      + apply or_introl with (B := In a (t :: tail)) in H2.
        apply in_or_app in H2.
        auto.
      + apply (in_cons t) in H2.
        apply or_intror with (A := In a sensitized_transs) in H2.
        apply in_or_app in H2.
        auto.
    (* Case is_sensitized returns an error,
     * then contradiction.
     *)
    - inversion H.
    (* Case get_neighbours returns an error,
     * then contradiction.
     *)
    - inversion H.
  Qed.
  
  (* Lemma : list_sensitized_aux returns no error if 
   *         all transition t in transs are referenced in lneighbours
   *         and if all neighbour places referenced in lneighbours are
   *         referenced in the marking m. 
   *)
  Lemma list_sensitized_aux_no_error :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)
           (m : marking_type)
           (sensitized_transs transs : list trans_type),
      TransAreRefInLneighbours transs lneighbours ->
      (forall (t : trans_type) (neighbours : neighbours_type),
          In (t, neighbours) lneighbours ->
          (PlacesAreRefInMarking neighbours.(pre_pl) m /\
           PlacesAreRefInMarking neighbours.(inhib_pl) m /\
           PlacesAreRefInMarking neighbours.(test_pl) m)) ->
      exists v : list trans_type,
        list_sensitized_aux lneighbours pre test inhib m sensitized_transs transs = Some v.
  Proof.
    unfold TransAreRefInLneighbours.
    unfold PlacesAreRefInMarking.
    intros lneighbours pre test inhib m sensitized_transs transs.
    functional induction (list_sensitized_aux lneighbours pre test inhib m
                                              sensitized_transs transs)
               using list_sensitized_aux_ind;
      intros.
    (* Base case, transs = []. *)
    - exists sensitized_transs; auto.
    (* Case is_sensitized = true. *)
    - apply IHo.
      + intros.
        apply (in_cons t) in H1.
        apply (H t0) in H1; auto.
      + intros.
        apply (H0 t0 neighbours) in H1; auto.
    (* Case is_sensitized = false. *)
    - apply IHo; intros.
      + apply (in_cons t) in H1; apply H in H1; auto.
      + apply (H0 t0 neighbours H1).
    (* Case is_sensitized = None,
     * impossible regarding hypothesis.
     *)
    - assert (H1 := (in_eq t tail)).
      apply get_neighbours_in in e0.
      generalize ((H0 t neighbours_t) e0); intros.
      elim H2; intros; clear H2.
      elim H4; intros; clear H4.
      (* Applies spn_is_firable_no_error to create a contradiction. *)
      apply (is_sensitized_no_error neighbours_t pre test inhib m t H3 H5) in H2.
      elim H2; intros; rewrite H4 in e1; inversion e1.
    (* Case get_neighbours = None, 
     * impossible regarding the hypotheses.
     *)
    - assert (H1 := (in_eq t tail)).
      apply H in H1.
      apply get_neighbours_no_error in H1.
      elim H1; intros.
      rewrite H2 in e0; inversion e0.
  Qed.

  (*
   * Function : Wrapper around list_sensitized_aux.
   *)
  Definition list_sensitized 
             (lneighbours : list (trans_type * neighbours_type))
             (pre test inhib : weight_type) 
             (m : marking_type)
             (transs : list trans_type) : option (list trans_type) :=
    list_sensitized_aux lneighbours pre test inhib m [] transs.

  (*** Formal specification : list_sensitized ***)
  Inductive ListSensitized
            (lneighbours : list (trans_type * neighbours_type))
            (pre test inhib : weight_type) 
            (m : marking_type) :
    list trans_type ->
    option (list trans_type) -> Prop :=
  | ListSensitized_cons :
      forall (transs : list trans_type)
             (opt_sensitized_transs : option (list trans_type)),
        ListSensitizedAux lneighbours pre test inhib m [] transs opt_sensitized_transs ->
        ListSensitized lneighbours pre test inhib m transs opt_sensitized_transs.

  Functional Scheme list_sensitized_ind := Induction for list_sensitized Sort Prop.

  (*** Correctness proof : list_sensitized ***)
  Theorem list_sensitized_correct :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)
           (m : marking_type)
           (transs : list trans_type)
           (opt_sensitized_transs : option (list trans_type)),
      list_sensitized lneighbours pre test inhib m transs = opt_sensitized_transs ->
      ListSensitized lneighbours pre test inhib m transs opt_sensitized_transs.
  Proof.
    intros lneighbours pre test inhib m transs.
    functional induction (list_sensitized lneighbours pre test inhib m transs)
               using list_sensitized_ind; intros.
    apply ListSensitized_cons.
    apply list_sensitized_aux_correct; auto.  
  Qed.

  (*** Completeness proof : list_sensitized ***)
  Theorem list_sensitized_complete :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)
           (m : marking_type)
           (transs : list trans_type)
           (opt_sensitized_transs : option (list trans_type)),
      ListSensitized lneighbours pre test inhib m transs opt_sensitized_transs ->
      list_sensitized lneighbours pre test inhib m transs = opt_sensitized_transs.
  Proof.
    intros; elim H; intros.
    unfold list_sensitized; apply list_sensitized_aux_complete in H0; rewrite H0; auto. 
  Qed.

  (*  
   * Lemma : All transitions in sensitized_transs (returned by list_sensitized_aux)
   *         are in transs.
   *)
  Lemma list_sensitized_incl_transs :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)
           (m : marking_type)
           (transs sensitized_transs : list trans_type),
      list_sensitized lneighbours pre test inhib m transs = Some sensitized_transs ->
      incl sensitized_transs transs.
  Proof.
    intros lneighbours pre test inhib m transs.
    functional induction (list_sensitized lneighbours pre test inhib m transs)
               using list_sensitized_ind; intros.
    generalize (list_sensitized_aux_incl_transs
                  lneighbours pre test inhib m
                  [] transs sensitized_transs H); intros.
    simpl in H0.
    auto.
  Qed.
  
  (* Lemma : list_sensitized returns no error if 
   *         all transition t in transs are referenced in lneighbours
   *         and if all neighbour places referenced in lneighbours are
   *         referenced in the marking m. 
   *)
  Lemma list_sensitized_no_error :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)
           (m : marking_type)
           (transs : list trans_type),
      incl transs (fst (split lneighbours)) ->
      (forall (t : trans_type) (neighbours : neighbours_type),
          In (t, neighbours) lneighbours ->
          (incl neighbours.(pre_pl) (fst (split m)) /\
           incl neighbours.(inhib_pl) (fst (split m)) /\
           incl neighbours.(test_pl) (fst (split m)))) ->
      exists v : list trans_type,
        list_sensitized lneighbours pre test inhib m transs = Some v.
  Proof.
    intros lneighbours pre test inhib m transs; intros.
    unfold list_sensitized.
    apply list_sensitized_aux_no_error; [auto | auto].
  Qed.
  
End ListSensitized.

(*============================================================*)
(*================= LIST DISABLED SECTION  ===================*)
(*============================================================*)
Section ListDisabled.
  
  (*  
   * Function :  Returns the list of disabled transitions
   *             contained in transs.
   *             
   *             Raises an error (None value) if get_neighbours or
   *             is_sensitized return None.
   *)
  Fixpoint list_disabled_aux 
           (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type) 
           (m : marking_type)
           (disabled_transs : list trans_type)
           (transs : list trans_type) :
    option (list trans_type) :=
    match transs with
    | t :: tail =>
      (* Checks if t has neighbours *)
      match get_neighbours lneighbours t with
      (* Case t has Some neighbours *)
      | Some neighbours_t =>
        (* Checks if t is sensitized. *)
        match is_sensitized neighbours_t pre test inhib m t with
        (* Case t is sensitized. *)
        | Some true =>
          list_disabled_aux lneighbours pre test inhib m disabled_transs tail
        (* Case t is disabled. *)
        | Some false =>
          list_disabled_aux lneighbours pre test inhib m (t :: disabled_transs) tail
        (* Error case!!! *)
        | None => None
        end
      (* Error case!!! *)
      | None => None
      end
    (* Recursion base case. *)
    | [] => Some disabled_transs
    end.

  (*** Formal specification : list_disabled_aux ***)
  Inductive ListDisabledAux
            (lneighbours : list (trans_type * neighbours_type))
            (pre test inhib : weight_type) 
            (m : marking_type)
            (disabled_transs : list trans_type) :
    list trans_type -> (* sometranss *)
    option (list trans_type) -> (* opt_disabled_transs *)
    Prop :=
  | ListDisabledAux_nil :
      ListDisabledAux lneighbours pre test inhib m disabled_transs []
                        (Some disabled_transs)      
  | ListDisabledAux_get_neighbours_err :
      forall (transs : list trans_type)
             (t : trans_type),
        GetNeighbours lneighbours t None ->
        ListDisabledAux lneighbours pre test inhib m disabled_transs (t :: transs) None      
  | ListDisabledAux_is_sensitized_err :
      forall (transs : list trans_type)
             (t : trans_type)
             (neighbours_t : neighbours_type),
        GetNeighbours lneighbours t (Some neighbours_t) ->
        IsSensitized neighbours_t pre test inhib m t None ->
        ListDisabledAux lneighbours pre test inhib m disabled_transs (t :: transs) None
  | ListDisabledAux_is_disabled_false :
      forall (transs : list trans_type)
             (t : trans_type)
             (neighbours_t : neighbours_type)
             (opt_disabled_transs : option (list trans_type)),
        GetNeighbours lneighbours t (Some neighbours_t) ->
        IsSensitized neighbours_t pre test inhib m t (Some true) ->
        ListDisabledAux lneighbours pre test inhib m disabled_transs transs
                        opt_disabled_transs ->
        ListDisabledAux lneighbours pre test inhib m disabled_transs (t :: transs)
                        opt_disabled_transs
  | ListDisabledAux_is_disabled_true :
      forall (transs : list trans_type)
             (t : trans_type)
             (neighbours_t : neighbours_type)
             (opt_disabled_transs : option (list trans_type)),
        GetNeighbours lneighbours t (Some neighbours_t) ->
        IsSensitized neighbours_t pre test inhib m t (Some false) ->
        ListDisabledAux lneighbours pre test inhib m (t :: disabled_transs) transs
                        opt_disabled_transs ->
        ListDisabledAux lneighbours pre test inhib m disabled_transs (t :: transs)
                        opt_disabled_transs.
  
  Functional Scheme list_disabled_aux_ind := Induction for list_disabled_aux Sort Prop.

  (*** Correctness proof : list_disabled_aux ***)
  Theorem list_disabled_aux_correct :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)
           (m : marking_type)
           (disabled_transs transs : list trans_type)
           (opt_disabled_transs : option (list trans_type)),
      list_disabled_aux lneighbours pre test inhib m
                          disabled_transs transs = opt_disabled_transs ->
      ListDisabledAux lneighbours pre test inhib m
                        disabled_transs transs opt_disabled_transs.
  Proof.
    intros lneighbours pre test inhib m disabled_transs transs.
    functional induction (list_disabled_aux lneighbours pre test inhib m
                                              disabled_transs transs)
               using list_disabled_aux_ind; intros.
    (* Case transs = [] *)
    - rewrite <- H; apply ListDisabledAux_nil.
    (* Case is_sensitized = true *)
    - apply ListDisabledAux_is_disabled_false with (neighbours_t := neighbours_t).
      + apply get_neighbours_correct; auto.
      + apply is_sensitized_correct; auto.
      + rewrite <- H; apply IHo; auto.
    (* Case is_sensitized = false *)
    - apply ListDisabledAux_is_disabled_true with (neighbours_t := neighbours_t).
      + apply get_neighbours_correct; auto.
      + apply is_sensitized_correct; auto. 
      + rewrite <- H; apply IHo; auto.        
    (* Error case, is_sensitized = None *)
    - rewrite <- H; apply ListDisabledAux_is_sensitized_err with (neighbours_t := neighbours_t).
      + apply get_neighbours_correct; auto.
      + apply is_sensitized_correct; auto.
    (* Error case, get_neighbours = None *)
    - rewrite <- H; apply ListDisabledAux_get_neighbours_err.
      + apply get_neighbours_correct; auto.
  Qed.

  (*** Completeness proof : list_disabled_aux ***)
  Theorem list_disabled_aux_complete :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)
           (m : marking_type)
           (disabled_transs transs : list trans_type)
           (opt_disabled_transs : option (list trans_type)),
      ListDisabledAux lneighbours pre test inhib m
                        disabled_transs transs opt_disabled_transs ->
      list_disabled_aux lneighbours pre test inhib m
                          disabled_transs transs = opt_disabled_transs.
  Proof.
    intros; elim H; intros.
    (* Case ListDisabledAux_nil *)
    - simpl; auto.
    (* Case ListDisabledAux_get_neighbours_err *)
    - simpl; apply get_neighbours_compl in H0; rewrite H0; auto.
    (* Case ListDisabledAux_is_sensitized_err *)
    - simpl;
        apply get_neighbours_compl in H0; rewrite H0;
          apply is_sensitized_compl in H1; rewrite H1; auto.
    (* Case ListDisabledAux_is_disabled_false *)
    - simpl;
        apply get_neighbours_compl in H0; rewrite H0;
          apply is_sensitized_compl in H1; rewrite H1; auto.
    (* Case ListDisabledAux_is_disabled_true *)
    - simpl;
        apply get_neighbours_compl in H0; rewrite H0;
          apply is_sensitized_compl in H1; rewrite H1; auto.
  Qed.

  (*  
   * Lemma : If all transitions in transs are ref in lneighbours then 
   *         all transitions in disabled_transs (returned by list_disabled_aux)
   *         are in lneighbours.
   *)
  Lemma list_disabled_aux_incl_lneighbours :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)
           (m : marking_type)
           (disabled_transs transs final_disabled : list trans_type),
      incl transs (fst (split lneighbours)) ->
      incl disabled_transs (fst (split lneighbours)) ->
      list_disabled_aux lneighbours pre test inhib m disabled_transs transs =
      Some final_disabled ->
      incl final_disabled (fst (split lneighbours)).
  Proof.
    unfold incl.
    intros lneighbours pre test inhib m disabled_transs transs.
    functional induction (list_disabled_aux lneighbours pre test inhib m disabled_transs transs)
               using list_disabled_aux_ind; intros.
    (* Base case, transs = []. *)
    - injection H1; intros.
      rewrite <- H3 in H2.
      apply H0 in H2.
      auto.
    (* Case everything went well. *)
    - apply IHo with (final_disabled := final_disabled).
      + intros.
        apply (in_cons t) in H3.
        apply H in H3; auto.
      + intros.
        apply (H0 a0 H3).
      + auto.
      + auto.
    (* Case is_sensitized = false. *)
    - apply IHo with (final_disabled := final_disabled).
      + intros.
        apply (in_cons t) in H3.
        apply H in H3; auto.
      + intros.
        apply in_inv in H3.
        elim H3; intros.
        -- cut (In a0 (t :: tail)); intros;
             [apply H in H5; auto | rewrite H4; apply in_eq].
        -- apply H0 in H4; auto.
      + auto.
      + auto.
    (* Case is_sensitized returns an error,
     * then contradiction.
     *)
     - inversion H1.
    (* Case get_neighbours returns an error,
     * then contradiction.
     *)
    - inversion H1.
  Qed.

  (*  
   * Lemma : If list_disabled_aux returns Some final_disabled then
   *         all transitions in final_disabled are in disabled_transs ++ transs.
   *)
  Lemma list_disabled_aux_incl_transs :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)
           (m : marking_type)
           (disabled_transs transs final_disabled : list trans_type),
      list_disabled_aux lneighbours pre test inhib m disabled_transs transs =
      Some final_disabled ->
      incl final_disabled (disabled_transs ++ transs).
  Proof.
    unfold incl.
    intros lneighbours pre test inhib m disabled_transs transs.
    functional induction (list_disabled_aux lneighbours pre test inhib m disabled_transs transs)
               using list_disabled_aux_ind; intros.
    (* Base case, transs = []. *)
    - injection H; intros.
      rewrite <- H1 in H0.
      rewrite <- app_nil_end; auto.
    (* Case everything went well. *)
    - generalize (IHo final_disabled H a H0); intro.
      apply in_app_or in H1.
      elim H1; intros.
      + apply or_introl with (B := In a (t :: tail)) in H2.
        apply in_or_app in H2.
        auto.
      + apply (in_cons t) in H2.
        apply or_intror with (A := In a disabled_transs) in H2.
        apply in_or_app in H2.
        auto.
    (* Case is_sensitized = false. *)
    - generalize (IHo final_disabled H a H0); intro.
      apply in_app_or in H1.
      elim H1; intros.
      + apply in_or_app.
        apply in_inv in H2.
        elim H2; intros.
        -- rewrite H3; right; apply in_eq.
        -- left; auto.
      + apply in_or_app.
        apply (in_cons t) in H2.
        right; auto.
    (* Case is_sensitized returns an error,
     * then contradiction.
     *)
    - inversion H.
    (* Case get_neighbours returns an error,
     * then contradiction.
     *)
    - inversion H.
  Qed.
  
  (* Lemma : list_disabled_aux returns no error if 
   *         all transition t in transs are referenced in lneighbours
   *         and if all neighbour places referenced in lneighbours are
   *         referenced in the marking m. 
   *)
  Lemma list_disabled_aux_no_error :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)
           (m : marking_type)
           (disabled_transs transs : list trans_type),
      incl transs (fst (split lneighbours)) ->
      (forall (t : trans_type) (neighbours : neighbours_type),
          In (t, neighbours) lneighbours ->
          (incl neighbours.(pre_pl) (fst (split m)) /\
           incl neighbours.(inhib_pl) (fst (split m)) /\
           incl neighbours.(test_pl) (fst (split m)))) ->
      exists v : list trans_type,
        list_disabled_aux lneighbours pre test inhib m disabled_transs transs = Some v.
  Proof.
    unfold incl.
    intros lneighbours pre test inhib m disabled_transs transs.
    functional induction (list_disabled_aux lneighbours pre test inhib m
                                            disabled_transs transs)
               using list_disabled_aux_ind;
      intros.
    (* Base case, transs = []. *)
    - exists disabled_transs; auto.
    (* Case is_sensitized = true. *)
    - apply IHo.
      + intros.
        apply (in_cons t) in H1.
        apply (H a) in H1; auto.
      + intros.
        apply (H0 t0 neighbours) in H1; auto.
    (* Case is_sensitized = false. *)
    - apply IHo; intros.
      + apply (in_cons t) in H1; apply H in H1; auto.
      + apply (H0 t0 neighbours H1).
    (* Case is_sensitized = None,
     * impossible regarding hypothesis.
     *)
    - assert (H1 := (in_eq t tail)).
      apply get_neighbours_in in e0.
      generalize ((H0 t neighbours_t) e0); intros.
      elim H2; intros; clear H2.
      elim H4; intros; clear H4.
      (* Applies spn_is_firable_no_error to create a contradiction. *)
      apply (is_sensitized_no_error neighbours_t pre test inhib m t H3 H5) in H2.
      elim H2; intros; rewrite H4 in e1; inversion e1.
    (* Case get_neighbours = None, 
     * impossible regarding the hypotheses.
     *)
    - assert (H1 := (in_eq t tail)).
      apply H in H1.
      apply get_neighbours_no_error in H1.
      elim H1; intros.
      rewrite H2 in e0; inversion e0.
  Qed.
  
  (*
   * Function : Wrapper around list_disabled_aux.
   *)
  Definition list_disabled 
             (lneighbours : list (trans_type * neighbours_type))
             (pre test inhib : weight_type) 
             (m : marking_type)
             (transs : list trans_type) : option (list trans_type) :=
    list_disabled_aux lneighbours pre test inhib m [] transs.

  (*** Formal specification : list_disabled ***)
  Inductive ListDisabled
            (lneighbours : list (trans_type * neighbours_type))
            (pre test inhib : weight_type) 
            (m : marking_type) :
    list trans_type ->
    option (list trans_type) -> Prop :=
  | ListDisabled_cons :
      forall (transs : list trans_type)
             (opt_disabled_transs : option (list trans_type)),
        ListDisabledAux lneighbours pre test inhib m [] transs opt_disabled_transs ->
        ListDisabled lneighbours pre test inhib m transs opt_disabled_transs.

  Functional Scheme list_disabled_ind := Induction for list_disabled Sort Prop.

  (*** Correctness proof : list_disabled ***)
  Theorem list_disabled_correct :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)
           (m : marking_type)
           (transs : list trans_type)
           (opt_disabled_transs : option (list trans_type)),
      list_disabled lneighbours pre test inhib m transs = opt_disabled_transs ->
      ListDisabled lneighbours pre test inhib m transs opt_disabled_transs.
  Proof.
    intros lneighbours pre test inhib m transs.
    functional induction (list_disabled lneighbours pre test inhib m transs)
               using list_disabled_ind; intros.
    apply ListDisabled_cons.
    apply list_disabled_aux_correct; auto.  
  Qed.

  (*** Completeness proof : list_disabled ***)
  Theorem list_disabled_complete :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)
           (m : marking_type)
           (transs : list trans_type)
           (opt_disabled_transs : option (list trans_type)),
      ListDisabled lneighbours pre test inhib m transs opt_disabled_transs ->
      list_disabled lneighbours pre test inhib m transs = opt_disabled_transs.
  Proof.
    intros; elim H; intros.
    unfold list_disabled; apply list_disabled_aux_complete in H0; rewrite H0; auto. 
  Qed.

  (*  
   * Lemma : If all transitions in transs are ref in lneighbours then 
   *         all transitions in disabled_transs (returned by list_disabled)
   *         are in lneighbours.
   *)
  Lemma list_disabled_incl_lneighbours :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)
           (m : marking_type)
           (transs disabled_transs : list trans_type),
      incl transs (fst (split lneighbours)) ->
      list_disabled lneighbours pre test inhib m transs = Some disabled_transs ->
      incl disabled_transs (fst (split lneighbours)).
  Proof.
    unfold incl.
    intros lneighbours pre test inhib m transs.
    functional induction (list_disabled lneighbours pre test inhib m transs)
               using list_disabled_ind;
      intros.
    cut (incl [] (fst (split lneighbours))); intros.
    - generalize (list_disabled_aux_incl_lneighbours
                    lneighbours pre test inhib m
                    [] transs disabled_transs
                    H H2 H0).
      intros.
      apply H3 in H1.
      auto.
    - unfold incl; intros; elim H2.
  Qed.

  (*  
   * Lemma : All transitions in disabled_transs (returned by list_disabled_aux)
   *         are in transs.
   *)
  Lemma list_disabled_incl_transs :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)
           (m : marking_type)
           (transs disabled_transs : list trans_type),
      list_disabled lneighbours pre test inhib m transs = Some disabled_transs ->
      incl disabled_transs transs.
  Proof.
    intros lneighbours pre test inhib m transs.
    functional induction (list_disabled lneighbours pre test inhib m transs)
               using list_disabled_ind; intros.
    generalize (list_disabled_aux_incl_transs
                  lneighbours pre test inhib m
                  [] transs disabled_transs H); intros.
    simpl in H0.
    auto.
  Qed.
      
  (* Lemma : list_disabled returns no error if 
   *         all transition t in transs are referenced in lneighbours
   *         and if all neighbour places referenced in lneighbours are
   *         referenced in the marking m. 
   *)
  Lemma list_disabled_no_error :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)
           (m : marking_type)
           (transs : list trans_type),
      incl transs (fst (split lneighbours)) ->
      (forall (t : trans_type) (neighbours : neighbours_type),
          In (t, neighbours) lneighbours ->
          (incl neighbours.(pre_pl) (fst (split m)) /\
           incl neighbours.(inhib_pl) (fst (split m)) /\
           incl neighbours.(test_pl) (fst (split m)))) ->
      exists v : list trans_type,
        list_disabled lneighbours pre test inhib m transs = Some v.
  Proof.
    intros lneighbours pre test inhib m transs; intros.
    unfold list_disabled.
    apply list_disabled_aux_no_error; [auto | auto].
  Qed.
  
End ListDisabled.

(*===============================================================*)
(*================= FIRING ALGORITHM for STPN ===================*)
(*===============================================================*)
Section FireStpn.

  (*  
   * Function : Returns true if transition t is firable according
   *            to "STPN standards", meaning that t is sensitized and
   *            its time counter value is in the firable interval.
   * 
   *            Raises an error (None value) if spn_is_firable or get_chronos 
   *            returns None.
   *)
  Definition stpn_is_firable
             (t : trans_type)
             (neighbours_t : neighbours_type)
             (pre test inhib: weight_type)
             (steadym decreasingm : marking_type)
             (chronos : list (trans_type * option chrono_type)) : option bool :=
    match spn_is_firable t neighbours_t pre test inhib steadym decreasingm with
    (* If t is firable according to "SPN standards", then checks its chrono. *)
    | Some true =>
      match get_chrono chronos t with
      (* Case t is referenced in chronos. *)
      | Some opt_chrono => Some (check_chrono opt_chrono)
      (* Error case!!! *)
      | None => None
      end
    (* t is not firable according to SPN. *)
    | Some false => Some false
    (* Error case!!! *)
    | None => None
    end.

  Functional Scheme stpn_is_firable_ind := Induction for stpn_is_firable Sort Prop.
  
  (*** Formal specification : stpn_is_firable ***)
  Inductive StpnIsFirable
            (t : trans_type)
            (neighbours_t : neighbours_type)
            (pre test inhib: weight_type)
            (steadym decreasingm : marking_type)
            (chronos : list (trans_type * option chrono_type)) :
    option bool -> Prop :=
  | StpnIsFirable_spn_err :
      SpnIsFirable t neighbours_t pre test inhib steadym decreasingm None ->
      StpnIsFirable t neighbours_t pre test inhib steadym decreasingm chronos None
  | StpnIsFirable_spn_false :
      SpnIsFirable t neighbours_t pre test inhib steadym decreasingm (Some false) ->
      StpnIsFirable t neighbours_t pre test inhib steadym decreasingm chronos (Some false)
  | StpnIsFirable_get_chrono_err :
      SpnIsFirable t neighbours_t pre test inhib steadym decreasingm (Some true) ->
      GetChrono chronos t None ->
      StpnIsFirable t neighbours_t pre test inhib steadym decreasingm chronos None
  | StpnIsFirable_cons_true :
      forall (opt_chrono : option chrono_type),
        SpnIsFirable t neighbours_t pre test inhib steadym decreasingm (Some true) ->
        GetChrono chronos t (Some opt_chrono) ->
        CheckChrono opt_chrono ->
        StpnIsFirable t neighbours_t pre test inhib steadym decreasingm chronos (Some true)
  | StpnIsFirable_cons_false :
      forall (opt_chrono : option chrono_type),
        SpnIsFirable t neighbours_t pre test inhib steadym decreasingm (Some true) ->
        GetChrono chronos t (Some opt_chrono) ->
        ~CheckChrono opt_chrono ->
        StpnIsFirable t neighbours_t pre test inhib steadym decreasingm chronos (Some false).

  (*** Correctness proof : stpn_is_firable ***)
  Theorem stpn_is_firable_correct :
    forall (t : trans_type)
           (neighbours_t : neighbours_type)
           (pre test inhib: weight_type)
           (steadym decreasingm : marking_type)
           (chronos : list (trans_type * option chrono_type))
           (optionb : option bool),
      stpn_is_firable t neighbours_t pre test inhib steadym decreasingm chronos = optionb ->
      StpnIsFirable t neighbours_t pre test inhib steadym decreasingm chronos optionb.
  Proof.
    intros t neighbours_t pre test inhib steadym decreasingm chronos.
    functional induction (stpn_is_firable t neighbours_t pre test inhib steadym decreasingm chronos)
               using stpn_is_firable_ind; intros.
    (* General case, all went well. *)
    - dependent induction optionb.
      dependent induction a.
      + apply StpnIsFirable_cons_true with (opt_chrono := opt_chrono).
        -- apply spn_is_firable_correct; auto.
        -- apply get_chrono_correct; auto.
        -- injection H; intros.
           apply check_chrono_correct; auto.
      + apply StpnIsFirable_cons_false with (opt_chrono := opt_chrono).
        -- apply spn_is_firable_correct; auto.
        -- apply get_chrono_correct; auto.
        -- injection H; intros.
           intro; apply check_chrono_complete in H1; rewrite H1 in H0; inversion H0.
      + inversion H.
    (* Error case, get_chrono returns None. *)
    - rewrite <- H; apply StpnIsFirable_get_chrono_err.
      + apply spn_is_firable_correct; auto.
      + apply get_chrono_correct; auto.
    (* Case spn_is_firable returns false. *)
    - rewrite <- H; apply StpnIsFirable_spn_false.
      + apply spn_is_firable_correct; auto.
    (* Error case, spn_is_firable returns None. *)
    - rewrite <- H; apply StpnIsFirable_spn_err.
      + apply spn_is_firable_correct; auto.
  Qed.

  (*** Completeness proof : stpn_is_firable ***)
  Theorem stpn_is_firable_compl :
    forall (t : trans_type)
           (neighbours_t : neighbours_type)
           (pre test inhib: weight_type)
           (steadym decreasingm : marking_type)
           (chronos : list (trans_type * option chrono_type))
           (optionb : option bool),
      StpnIsFirable t neighbours_t pre test inhib steadym decreasingm chronos optionb ->
      stpn_is_firable t neighbours_t pre test inhib steadym decreasingm chronos = optionb.
  Proof.  
    intros t neighbours_t pre test inhib steadym decreasingm chronos optionb H.
    elim H; intros.
    (* Case StpnIsFirable_spn_err *)
    - apply spn_is_firable_compl in H0.
      unfold stpn_is_firable; rewrite H0; auto.
    (* Case StpnIsFirable_spn_false *)
    - apply spn_is_firable_compl in H0.
      unfold stpn_is_firable; rewrite H0; auto.
    (* Case StpnIsFirable_get_chrono_err *)
    - apply spn_is_firable_compl in H0; apply get_chrono_compl in H1.
      unfold stpn_is_firable; rewrite H0; rewrite H1; auto.
    (* Case StpnIsFirable_cons_true *)
    - apply spn_is_firable_compl in H0;
        apply get_chrono_compl in H1;
        apply check_chrono_complete in H2.
      unfold stpn_is_firable; rewrite H0; rewrite H1; rewrite H2; auto.
    (* Case StpnIsFirable_cons_false *)
    - apply spn_is_firable_compl in H0;
        apply get_chrono_compl in H1.
      assert (H' := (conj (check_chrono_complete opt_chrono) (check_chrono_correct opt_chrono))).
      apply iff_to_and in H'; apply not_iff_compat in H'; apply H' in H2.
      apply not_true_is_false in H2.
      unfold stpn_is_firable; rewrite H0; rewrite H1; rewrite H2; auto.
  Qed.

  (* Lemma : Proves that stpn_is_firable returns no error if
   *         the places in (pre_pl neighbours_t), (inhib_pl neighbours_t) 
   *         and (test_pl neighbours_t) are referenced in markings steadym
   *         and decreasingm, and if t is referenced in chronos.  
   *
   *)
  Lemma stpn_is_firable_no_error :
    forall (t : trans_type)
           (neighbours_t : neighbours_type)
           (pre test inhib : weight_type)
           (steadym decreasingm : marking_type)
           (chronos : list (trans_type * option chrono_type)),
      In t (fst (split chronos)) ->
      PlacesAreRefInMarking (pre_pl neighbours_t) decreasingm ->
      PlacesAreRefInMarking (test_pl neighbours_t) steadym ->
      PlacesAreRefInMarking (inhib_pl neighbours_t) steadym ->
      exists v : bool,
        stpn_is_firable t neighbours_t pre test inhib steadym decreasingm chronos = Some v.
  Proof.
    intros t neighbours_t pre test inhib steadym decreasingm chronos.
    functional induction (stpn_is_firable t neighbours_t pre test inhib steadym decreasingm chronos)
               using stpn_is_firable_ind; intros.
    (* General case, all went well. *)
    - exists (check_chrono opt_chrono); auto.
    (* Case get_chrono = None, impossible regarding the hypotheses. *)
    - generalize (get_chrono_no_error chronos t H); intros.
      elim H3; intros; rewrite H4 in e1; inversion e1.
    (* Case spn_is_firable = false. *)
    - exists false; auto.
    (* Case spn_is_firable = None, impossible regarding the hypotheses. *)
    - generalize (spn_is_firable_no_error t neighbours_t pre test inhib steadym decreasingm
                                          H0 H1 H2); intros.
      elim H3; intros; rewrite H4 in e; inversion e.
  Qed.      

  (********************************************************************)
  (********************************************************************)
  
  (* Function : Given 1 priority group of transitions (a list pgroup), 
   *            returns 1 list of transitions "fired_pre_group" 
   *            and marking "decreasingm" accordingly ...
   *
   *            Returns a couple (list of transitions, marking)
   *            For each sensitized transition of the list,
   *            the marking of the pre-condition places are updated (the 
   *            transition is fired). "decreasingm" is then the resulting marking.
   *)
  Fixpoint stpn_fire_pre_aux
           (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)  
           (steadym : marking_type)
           (decreasingm : marking_type)
           (chronos : list (trans_type * option chrono_type))
           (fired_pre_group pgroup : list trans_type) {struct pgroup} :
    option ((list trans_type) * marking_type) :=
    match pgroup with
    | t :: tail =>
      match get_neighbours lneighbours t with
      (* t is referenced in lneighbours. *)
      | Some neighbours_t =>
        match stpn_is_firable t neighbours_t pre test inhib steadym decreasingm chronos with
        (* If t is firable, then updates marking for pre places of t. *)
        | Some true =>
          match update_marking_pre t pre decreasingm (pre_pl neighbours_t) with
          (* Adds t at the end of fired_pre_group, and continues with new marking. *)
          | Some marking' =>
            stpn_fire_pre_aux lneighbours pre test inhib steadym marking' chronos
                              (fired_pre_group ++ [t]) tail
          (* Error, something went wrong with update_marking_pre!!! *)
          | None => None
          end
        (* Else t is not firable, then continues without adding it to fired_pre_group. *)
        | Some false =>
          stpn_fire_pre_aux lneighbours pre test inhib steadym decreasingm chronos
                            fired_pre_group tail
        (* Error, something went wrong with stpn_is_firable!!! *)
        | None => None
        end
      (* Error, t is not referenced in lneighbours!!! *)
      | None => None
      end
    | [] => Some (fired_pre_group, decreasingm)
    end.

  Functional Scheme stpn_fire_pre_aux_ind := Induction for stpn_fire_pre_aux Sort Prop.
  
  (*** Formal specification : spn_fire_pre_aux ***)
  Inductive StpnFirePreAux
            (lneighbours : list (trans_type * neighbours_type))
            (pre test inhib : weight_type) 
            (steadym : marking_type) 
            (decreasingm : marking_type)
            (chronos : list (trans_type * option chrono_type))
            (fired_pre_group : list trans_type) :
    list trans_type -> option (list trans_type * marking_type) -> Prop :=
  | StpnFirePreAux_nil :
      StpnFirePreAux lneighbours pre test inhib steadym decreasingm chronos fired_pre_group []
                     (Some (fired_pre_group, decreasingm))
  (* Case get_neighbours returns an error. *)
  | StpnFirePreAux_neighbours_err :
      forall (t : trans_type) (pgroup : list trans_type),
        GetNeighbours lneighbours t None ->
        StpnFirePreAux lneighbours pre test inhib steadym decreasingm chronos fired_pre_group (t :: pgroup) None
  (* Case stpn_is_firable returns an error. *)
  | StpnFirePreAux_firable_err :
      forall (t : trans_type) (pgroup : list trans_type) (neighbours_t : neighbours_type),
        GetNeighbours lneighbours t (Some neighbours_t) ->
        StpnIsFirable t neighbours_t pre test inhib steadym decreasingm chronos None ->
        StpnFirePreAux lneighbours pre test inhib steadym decreasingm chronos fired_pre_group (t :: pgroup) None
  (* Case stpn_is_firable returns false. *)
  | StpnFirePreAux_firable_false :
      forall (t : trans_type)
             (pgroup : list trans_type)
             (neighbours_t : neighbours_type)
             (option_final_couple : option (list trans_type * marking_type)),
        GetNeighbours lneighbours t (Some neighbours_t) ->
        StpnIsFirable t neighbours_t pre test inhib steadym decreasingm chronos (Some false) ->
        StpnFirePreAux lneighbours pre test inhib steadym decreasingm chronos fired_pre_group pgroup
                       option_final_couple ->
        StpnFirePreAux lneighbours pre test inhib steadym decreasingm chronos fired_pre_group (t :: pgroup)
                       option_final_couple
  (* Case update_marking_pre returns an error. *)
  | StpnFirePreAux_update_err :
      forall (t : trans_type)
             (neighbours_t : neighbours_type)
             (pgroup : list trans_type),
        GetNeighbours lneighbours t (Some neighbours_t) ->
        StpnIsFirable t neighbours_t pre test inhib steadym decreasingm chronos (Some true) ->
        UpdateMarkingPre t pre decreasingm (pre_pl neighbours_t) None ->
        StpnFirePreAux lneighbours pre test inhib steadym decreasingm chronos fired_pre_group (t :: pgroup) None
  (* General case, all went well. *)
  | StpnFirePreAux_cons :
      forall (t : trans_type)
             (neighbours_t : neighbours_type)
             (pgroup : list trans_type)
             (modifiedm : marking_type)
             (option_final_couple : option (list trans_type * marking_type)),
        GetNeighbours lneighbours t (Some neighbours_t) ->
        StpnIsFirable t neighbours_t pre test inhib steadym decreasingm chronos (Some true) ->
        UpdateMarkingPre t pre decreasingm (pre_pl neighbours_t) (Some modifiedm) ->
        StpnFirePreAux lneighbours pre test inhib steadym modifiedm chronos (fired_pre_group ++ [t]) pgroup
                       option_final_couple ->
        StpnFirePreAux lneighbours pre test inhib steadym decreasingm chronos fired_pre_group (t :: pgroup)
                       option_final_couple.

  (*** Correctness proof : stpn_fire_pre_aux ***)
  Theorem stpn_fire_pre_aux_correct :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type) 
           (steadym : marking_type) 
           (decreasingm : marking_type)
           (chronos : list (trans_type * option chrono_type))
           (fired_pre_group : list trans_type)
           (pgroup : list trans_type)
           (option_final_couple : option (list trans_type * marking_type)),
      stpn_fire_pre_aux lneighbours pre test inhib steadym decreasingm chronos fired_pre_group pgroup = option_final_couple ->
      StpnFirePreAux lneighbours pre test inhib steadym decreasingm chronos fired_pre_group pgroup option_final_couple.
  Proof.
    intros lneighbours pre test inhib steadym decreasingm chronos fired_pre_group pgroup.
    functional induction (stpn_fire_pre_aux lneighbours pre test inhib steadym decreasingm chronos fired_pre_group pgroup)
               using stpn_fire_pre_aux_ind; intros.
    (* Case pgroup = [] *)
    - rewrite <- H; apply StpnFirePreAux_nil.
    (* General case, all went well. *)
    - apply StpnFirePreAux_cons with (modifiedm := marking')
                                     (neighbours_t := neighbours_t).
      + apply get_neighbours_correct; auto.
      + apply stpn_is_firable_correct; auto.
      + apply update_marking_pre_correct; auto.
      + apply IHo; auto.
    (* Case update_marking_pre error. *)
    - rewrite <- H; apply StpnFirePreAux_update_err with (neighbours_t := neighbours_t).
      + apply get_neighbours_correct; auto.
      + apply stpn_is_firable_correct; auto.
      + apply update_marking_pre_correct; auto.
    (* Case spn_is_firable returns false. *)
    - apply StpnFirePreAux_firable_false with (neighbours_t := neighbours_t).
      + apply get_neighbours_correct; auto.
      + apply stpn_is_firable_correct; auto.
      + apply IHo; auto.
    (* Case spn_is_firable returns an error. *)
    - rewrite <- H; apply StpnFirePreAux_firable_err with (neighbours_t := neighbours_t).
      + apply get_neighbours_correct; auto.
      + apply stpn_is_firable_correct; auto.
    (* Case get_neighbours returns an error. *)
    - rewrite <- H; apply StpnFirePreAux_neighbours_err.
      apply get_neighbours_correct; auto.
  Qed.

  (*** Completeness proof : stpn_fire_pre_aux ***)
  Theorem stpn_fire_pre_aux_compl :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type) 
           (steadym : marking_type) 
           (decreasingm : marking_type)
           (chronos : list (trans_type * option chrono_type))
           (fired_pre_group : list trans_type)
           (pgroup : list trans_type)
           (option_final_couple : option (list trans_type * marking_type)),
      StpnFirePreAux lneighbours pre test inhib steadym decreasingm chronos fired_pre_group pgroup option_final_couple ->
      stpn_fire_pre_aux lneighbours pre test inhib steadym decreasingm chronos fired_pre_group pgroup = option_final_couple.
  Proof.
    intros; elim H; intros.
    (* Case StpnFirePreAux_nil *)
    - simpl; auto.
    (* Case StpnFirePreAux_neighbours_err *)
    - simpl; apply get_neighbours_compl in H0; rewrite H0; auto.
    (* Case StpnFirePreAux_firable_err *)
    - simpl;
      apply get_neighbours_compl in H0; rewrite H0;
      apply stpn_is_firable_compl in H1; rewrite H1; auto.
    (* Case StpnFirePreAux_firable_false *)
    - simpl;
      apply get_neighbours_compl in H0; rewrite H0;
      apply stpn_is_firable_compl in H1; rewrite H1; rewrite H3; auto.
    (* Case StpnFirePreAux_update_err *)
    - simpl;
      apply get_neighbours_compl in H0; rewrite H0;
      apply stpn_is_firable_compl in H1; rewrite H1; auto;
      apply update_marking_pre_compl in H2; rewrite H2; auto.
    (* Case StpnFirePreAux_cons *)
    - simpl;
      apply get_neighbours_compl in H0; rewrite H0;
      apply stpn_is_firable_compl in H1; rewrite H1; auto;
      apply update_marking_pre_compl in H2; rewrite H2; auto.
  Qed.

  (* Lemma : Proves that stpn_fire_pre preserves
   *         the structure of the marking decreasingm
   *         passed as argument.
   *
   *         stpn_fire_pre returns a marking decreasedm
   *         which has the same structure as decreasingm. 
   *)
  Lemma stpn_fire_pre_aux_same_struct :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type) 
           (steadym : marking_type) 
           (decreasingm : marking_type)
           (chronos : list (trans_type * option chrono_type))
           (fired_pre_group : list trans_type)
           (pgroup : list trans_type)
           (pre_fired_transitions : list trans_type)
           (decreasedm : marking_type),
      stpn_fire_pre_aux lneighbours pre test inhib steadym decreasingm chronos fired_pre_group pgroup =
      Some (pre_fired_transitions, decreasedm) ->
      MarkingHaveSameStruct decreasingm decreasedm.
  Proof.
    intros lneighbours pre test inhib steadym decreasingm chronos fired_pre_group pgroup.
    functional induction (stpn_fire_pre_aux lneighbours pre test inhib
                                            steadym decreasingm
                                            chronos fired_pre_group pgroup)
               using stpn_fire_pre_aux_ind;
      intros.
    - injection H; intros.
      rewrite H0.
      unfold MarkingHaveSameStruct; auto.
    - apply IHo in H.
      apply update_marking_pre_same_struct in e3.
      unfold MarkingHaveSameStruct.
      unfold MarkingHaveSameStruct in e3.
      unfold MarkingHaveSameStruct in H.
      rewrite <- H; rewrite e3; auto.
    - inversion H.
    - apply IHo in H; auto.
    - inversion H.
    - inversion H.
  Qed.

  (*  
   * Lemma : If all transitions in pgroup are in lneighbours then 
   *         all transitions in final_fired_pre_group (returned by stpn_fire_pre_aux)
   *         are in lneighbours.
   *)
  Lemma stpn_fire_pre_aux_final_fired_in_lneighbours :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type) 
           (steadym : marking_type) 
           (decreasingm : marking_type)
           (chronos : list (trans_type * option chrono_type))
           (fired_pre_group : list trans_type)
           (pgroup : list trans_type)
           (final_fired_pre_group : list trans_type)
           (finalm : marking_type),
      incl pgroup (fst (split lneighbours)) ->
      incl fired_pre_group (fst (split lneighbours)) ->
      stpn_fire_pre_aux lneighbours pre test inhib steadym decreasingm chronos fired_pre_group pgroup =
      Some (final_fired_pre_group, finalm) ->
      incl final_fired_pre_group (fst (split lneighbours)).
  Proof.
    unfold incl.
    intros lneighbours pre test inhib steadym decreasingm chronos fired_pre_group pgroup.
    functional induction (stpn_fire_pre_aux lneighbours pre test inhib steadym decreasingm chronos fired_pre_group pgroup)
               using stpn_fire_pre_aux_ind;
      intros.
    (* Base case, pgroup = []. *)
    - injection H1; intros.
      rewrite <- H4 in H2.
      apply H0 in H2.
      auto.
    (* Case everything went well. *)
    - apply IHo with (final_fired_pre_group := final_fired_pre_group)
                     (finalm := finalm).
      + intros.
        apply (in_cons t) in H3.
        apply H in H3; auto.
      + intros.
        apply in_app_or in H3.
        elim H3; intros.
        -- apply H0 in H4; auto.
        -- apply in_inv in H4.
           elim H4; intros.
           { cut (In a0 (t :: tail)); intros;
               [apply H in H6; auto | rewrite H5; apply in_eq].
           }
           { elim H5. }
      + auto.
      + auto.
    (* Case update_marking_pre returns an error,
     * then contradiction.
     *)
    - inversion H1.
    (* Case stpn_is_firable = false. *)
    - apply IHo with (final_fired_pre_group := final_fired_pre_group)
                     (finalm := finalm).
      + intros.
        apply (in_cons t) in H3.
        apply H in H3; auto.
      + intros.
        apply H0 in H3.
        auto.
      + auto.
      + auto.
    (* Case stpn_is_firable returns an error,
     * then contradiction.
     *)
    - inversion H1.
    (* Case get_neighbours returns an error,
     * then contradiction.
     *)
    - inversion H1.
  Qed.
  
  (*  
   * Lemma : If all transitions in pgroup are ref in chronos then 
   *         all transitions in final_fired_pre_group (returned by stpn_fire_pre_aux)
   *         are ref in chronos.
   *)
  Lemma stpn_fire_pre_aux_final_fired_in_chronos :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type) 
           (steadym : marking_type) 
           (decreasingm : marking_type)
           (chronos : list (trans_type * option chrono_type))
           (fired_pre_group : list trans_type)
           (pgroup : list trans_type)
           (final_fired_pre_group : list trans_type)
           (finalm : marking_type),
      incl pgroup (fst (split chronos)) ->
      incl fired_pre_group (fst (split chronos)) ->
      stpn_fire_pre_aux lneighbours pre test inhib steadym decreasingm chronos
                        fired_pre_group pgroup =
      Some (final_fired_pre_group, finalm) ->
      incl final_fired_pre_group (fst (split chronos)).
  Proof.
    unfold incl.
    intros lneighbours pre test inhib steadym decreasingm chronos fired_pre_group pgroup.
    functional induction (stpn_fire_pre_aux lneighbours pre test inhib steadym decreasingm chronos fired_pre_group pgroup)
               using stpn_fire_pre_aux_ind;
      intros.
    (* Base case, pgroup = []. *)
    - injection H1; intros.
      rewrite <- H4 in H2.
      apply H0 in H2.
      auto.
    (* Case everything went well. *)
    - apply IHo with (final_fired_pre_group := final_fired_pre_group)
                     (finalm := finalm).
      + intros.
        apply (in_cons t) in H3.
        apply H in H3; auto.
      + intros.
        apply in_app_or in H3.
        elim H3; intros.
        -- apply H0 in H4; auto.
        -- apply in_inv in H4.
           elim H4; intros.
           { cut (In a0 (t :: tail)); intros;
               [apply H in H6; auto | rewrite H5; apply in_eq].
           }
           { elim H5. }
      + auto.
      + auto.
    (* Case update_marking_pre returns an error,
     * then contradiction.
     *)
    - inversion H1.
    (* Case stpn_is_firable = false. *)
    - apply IHo with (final_fired_pre_group := final_fired_pre_group)
                     (finalm := finalm).
      + intros.
        apply (in_cons t) in H3.
        apply H in H3; auto.
      + intros.
        apply H0 in H3.
        auto.
      + auto.
      + auto.
    (* Case stpn_is_firable returns an error,
     * then contradiction.
     *)
    - inversion H1.
    (* Case get_neighbours returns an error,
     * then contradiction.
     *)
    - inversion H1.
  Qed.
  
  (* Lemma : stpn_fire_pre_aux returns no error if 
   *         all transition t in pgroup are referenced in lneighbours
   *         and if all neighbour places referenced in lneighbours are
   *         referenced in the markings steadym and decreasingm. 
   *)
  Lemma stpn_fire_pre_aux_no_error :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type) 
           (steadym : marking_type) 
           (decreasingm : marking_type)
           (chronos : list (trans_type * option chrono_type))
           (fired_pre_group : list trans_type)
           (pgroup : list trans_type),
      incl pgroup (fst (split chronos)) ->
      incl pgroup (fst (split lneighbours)) ->
      (forall (t : trans_type) (neighbours : neighbours_type),
          In (t, neighbours) lneighbours ->
          (incl neighbours.(pre_pl) (fst (split decreasingm)) /\
           incl neighbours.(inhib_pl) (fst (split steadym)) /\
           incl neighbours.(test_pl) (fst (split steadym)))) ->
      exists v : (list trans_type * marking_type),
        stpn_fire_pre_aux lneighbours pre test inhib steadym decreasingm chronos fired_pre_group pgroup = Some v.
  Proof.
    unfold incl.
    intros lneighbours pre test inhib steadym decreasingm chronos fired_pre_group pgroup.
    functional induction (stpn_fire_pre_aux lneighbours pre test inhib steadym decreasingm chronos
                                           fired_pre_group pgroup)
               using stpn_fire_pre_aux_ind;
      intros.
    (* Base case, pgroup = []. *)
    - exists (fired_pre_group, decreasingm); auto.
    (* Case stpn_is_firable = true. *)
    - apply IHo.
      + intros.
        apply (in_cons t) in H2.
        apply (H a) in H2; auto.
      + intros.
        apply (in_cons t) in H2.
        apply (H0 a) in H2; auto.
      + intros.
        apply (H1 t0 neighbours) in H2.
        apply update_marking_pre_same_struct in e3.
        unfold MarkingHaveSameStruct in e3.
        rewrite <- e3; auto.
    (* Case update_marking_pre = None,
     * impossible regarding hypothesis.
     *)
    - assert (H' := in_eq t tail).
      apply get_neighbours_in in e0.
      generalize ((H1 t neighbours_t) e0).
      intros.
      elim H2; intros.
      apply (update_marking_pre_no_error t pre (pre_pl neighbours_t) decreasingm) in H3.
      elim H3; intros.
      rewrite H5 in e3; inversion e3.
    (* Case stpn_is_firable = false. *)
    - apply IHo; intros.
      + apply (H a (in_cons t a tail H2)).
      + apply (H0 a (in_cons t a tail H2)).
      + apply (H1 t0 neighbours H2).
    (* Case stpn_is_firable = None, 
     * impossible regarding the hypotheses. 
     *)
    - assert (H' := in_eq t tail).
      apply get_neighbours_in in e0.
      generalize ((H1 t neighbours_t) e0); intros.
      generalize (H t H'); intros.
      elim H2; intros; clear H2.
      elim H5; intros; clear H5.
      (* Applies stpn_is_firable_no_error to create a contradiction. *)
      apply (stpn_is_firable_no_error t neighbours_t pre test inhib
                                      steadym decreasingm chronos0 H3 H4 H6) in H2.
      elim H2; intros.
      rewrite H5 in e1.
      inversion e1.
    (* Case get_neighbours = None, 
     * impossible regarding the hypotheses.
     *)
    - assert (H' := in_eq t tail).
      apply H0 in H'.
      apply get_neighbours_no_error in H'.
      elim H'; intros.
      rewrite H2 in e0; inversion e0.
  Qed.
  
  (*****************************************************)
  (*****************************************************)
  
  (*  
   * Function : Wrapper function around stpn_fire_pre_aux.
   *)
  Definition stpn_fire_pre
             (lneighbours : list (trans_type * neighbours_type))
             (pre test inhib : weight_type) 
             (steadym : marking_type) 
             (decreasingm : marking_type)
             (chronos : list (trans_type * option chrono_type))
             (pgroup : list trans_type) :
    option (list trans_type * marking_type) :=
    stpn_fire_pre_aux lneighbours pre test inhib steadym decreasingm chronos [] pgroup.

  Functional Scheme stpn_fire_pre_ind := Induction for stpn_fire_pre Sort Prop.

  (*** Formal specification : stpn_fire_pre ***)
  Inductive StpnFirePre
            (lneighbours : list (trans_type * neighbours_type))
            (pre test inhib : weight_type) 
            (steadym : marking_type) 
            (decreasingm : marking_type)
            (chronos : list (trans_type * option chrono_type))
            (pgroup : list trans_type) : option (list trans_type * marking_type) -> Prop :=
  | StpnFirePre_cons :
      forall (option_final_couple : option (list trans_type * marking_type)),
        StpnFirePreAux lneighbours pre test inhib steadym decreasingm chronos [] pgroup
                       option_final_couple ->
        StpnFirePre lneighbours pre test inhib steadym decreasingm chronos pgroup
                    option_final_couple.

  (*** Correctness proof : stpn_fire_pre ***)
  Theorem stpn_fire_pre_correct :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type) 
           (steadym decreasingm : marking_type)
           (chronos : list (trans_type * option chrono_type))
           (pgroup : list trans_type)
           (option_final_couple : option (list trans_type * marking_type)),
      stpn_fire_pre lneighbours pre test inhib steadym decreasingm chronos pgroup = option_final_couple ->
      StpnFirePre lneighbours pre test inhib steadym decreasingm chronos pgroup option_final_couple.
  Proof.
    intros; unfold stpn_fire_pre in H.
    apply StpnFirePre_cons; apply stpn_fire_pre_aux_correct in H; auto.
  Qed.

  (*** Completeness proof : stpn_fire_pre ***)
  Theorem stpn_fire_pre_compl :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type) 
           (steadym decreasingm : marking_type)
           (chronos : list (trans_type * option chrono_type))
           (pgroup : list trans_type)
           (option_final_couple : option (list trans_type * marking_type)),
      StpnFirePre lneighbours pre test inhib steadym decreasingm chronos pgroup option_final_couple ->
      stpn_fire_pre lneighbours pre test inhib steadym decreasingm chronos pgroup = option_final_couple.
  Proof.
    intros; elim H; intros.
    unfold stpn_fire_pre; apply stpn_fire_pre_aux_compl in H0; auto. 
  Qed.

  (* Lemma : Proves that stpn_fire_pre preserves
   *         the structure of the marking decreasingm
   *         passed as argument.
   *
   *         stpn_fire_pre returns a marking decreasedm
   *         which has the same structure as decreasingm. 
   *)
  Lemma stpn_fire_pre_same_struct :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type) 
           (steadym : marking_type) 
           (decreasingm : marking_type)
           (chronos : list (trans_type * option chrono_type))
           (pgroup : list trans_type)
           (pre_fired_transitions : list trans_type)
           (decreasedm : marking_type),
      stpn_fire_pre lneighbours pre test inhib steadym decreasingm chronos pgroup =
      Some (pre_fired_transitions, decreasedm) ->
      MarkingHaveSameStruct decreasingm decreasedm.
  Proof.
    intros lneighbours pre test inhib steadym decreasingm chronos pgroup; intros.
    unfold stpn_fire_pre in H.
    apply stpn_fire_pre_aux_same_struct in H; auto.
  Qed.

  (*  
   * Lemma : If all transitions in pgroup are in lneighbours then 
   *         all transitions in final_fired_pre_group (returned by stpn_fire_pre)
   *         are in lneighbours.
   *)
  Lemma stpn_fire_pre_final_fired_in_lneighbours :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type) 
           (steadym : marking_type) 
           (decreasingm : marking_type)
           (chronos : list (trans_type * option chrono_type))
           (pgroup : list trans_type)
           (final_fired_pre_group : list trans_type)
           (finalm : marking_type),
      incl pgroup (fst (split lneighbours)) ->
      stpn_fire_pre lneighbours pre test inhib steadym decreasingm chronos pgroup =
      Some (final_fired_pre_group, finalm) ->
      incl final_fired_pre_group (fst (split lneighbours)).
  Proof.
    unfold incl.
    intros lneighbours pre test inhib steadym decreasingm chronos pgroup.
    functional induction (stpn_fire_pre lneighbours pre test inhib steadym decreasingm chronos pgroup)
               using stpn_fire_pre_ind;
      intros.
    (* This hypothesis is needed to apply spn_fire_pre_aux_final_fired_in_lneighbours. 
     * Corresponds to the hypothesis "incl pre_fired_group (fst (split lneighbours))"
     * but in that case, pre_fired_group = [].
     *)
    cut (incl [] (fst (split lneighbours))); intros.
    - generalize (stpn_fire_pre_aux_final_fired_in_lneighbours
                    lneighbours pre test inhib
                    steadym decreasingm chronos
                    [] pgroup
                    final_fired_pre_group finalm
                    H H2 H0).
      intros.
      apply H3 in H1.
      auto.
    - unfold incl; intros; elim H2.
  Qed.

  (*  
   * Lemma : If all transitions in pgroup are ref in chronos then 
   *         all transitions in final_fired_pre_group (returned by stpn_fire_pre)
   *         are ref in chronos.
   *)
  Lemma stpn_fire_pre_final_fired_in_chronos :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type) 
           (steadym : marking_type) 
           (decreasingm : marking_type)
           (chronos : list (trans_type * option chrono_type))
           (pgroup : list trans_type)
           (final_fired_pre_group : list trans_type)
           (finalm : marking_type),
      incl pgroup (fst (split chronos)) ->
      stpn_fire_pre lneighbours pre test inhib steadym decreasingm chronos pgroup =
      Some (final_fired_pre_group, finalm) ->
      incl final_fired_pre_group (fst (split chronos)).
  Proof.
    unfold incl.
    intros lneighbours pre test inhib steadym decreasingm chronos pgroup.
    functional induction (stpn_fire_pre lneighbours pre test inhib
                                        steadym decreasingm chronos pgroup)
               using stpn_fire_pre_ind; intros.
    (* This hypothesis is needed to apply stpn_fire_pre_aux_final_fired_in_chronos. 
     * Corresponds to the hypothesis "incl pre_fired_group (fst (split chronos))"
     * but in that case, pre_fired_group = [].
     *)
    cut (incl [] (fst (split chronos))); intros.
    - generalize (stpn_fire_pre_aux_final_fired_in_chronos
                    lneighbours pre test inhib
                    steadym decreasingm chronos
                    [] pgroup
                    final_fired_pre_group finalm
                    H H2 H0).
      intros.
      apply H3 in H1.
      auto.
    - unfold incl; intros; elim H2.
  Qed.
  
  (* Lemma : stpn_fire_pre returns no error if 
   *         all transition t in pgroup are referenced in lneighbours
   *         and if all neighbour places referenced in lneighbours are
   *         referenced in the markings steadym and decreasingm. 
   *)
  Lemma stpn_fire_pre_no_error :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type) 
           (steadym : marking_type) 
           (decreasingm : marking_type)
           (chronos : list (trans_type * option chrono_type))
           (pgroup : list trans_type),
      incl pgroup (fst (split chronos)) ->
      incl pgroup (fst (split lneighbours)) ->
      (forall (t : trans_type) (neighbours : neighbours_type),
          In (t, neighbours) lneighbours ->
          (incl neighbours.(pre_pl) (fst (split decreasingm)) /\
           incl neighbours.(inhib_pl) (fst (split steadym)) /\
           incl neighbours.(test_pl) (fst (split steadym)))) ->
      exists v : (list trans_type * marking_type),
        stpn_fire_pre lneighbours pre test inhib steadym decreasingm chronos pgroup = Some v.
  Proof.
    intros lneighbours pre test inhib steadym decreasingm chronos pgroup; intros.
    unfold spn_fire_pre.
    apply stpn_fire_pre_aux_no_error; [auto | auto | auto].
  Qed.
  
  (***********************************************************************)
  (***********************************************************************)
  
  (*
   * Function : Returns the list of pre-fired transitions and a marking.
   *
   *            Applies stpn_fire_pre over all priority group of transitions. 
   *            Begin with initial marking; End with half fired marking.  
   *            "pre_fired_transitions" is empty at first. 
   *)
  Fixpoint stpn_map_fire_pre_aux
           (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)
           (steadym decreasingm : marking_type)
           (chronos : list (trans_type * option chrono_type))
           (pre_fired_transitions : list trans_type)
           (priority_groups : list (list trans_type)) :
    option (list trans_type * marking_type) :=
    match priority_groups with
    (* Loops over all priority group of transitions (prgroup) and
     * calls stpn_fire_pre. *)
    | pgroup :: pgroups_tail =>
      match stpn_fire_pre lneighbours pre test inhib steadym decreasingm chronos pgroup with
      (* If stpn_fire_pre succeeds, then adds the fired transitions
       * in pre_fired_transitions list. *)
      | Some (pre_fired_trs, decreasedm) =>
        stpn_map_fire_pre_aux lneighbours pre test inhib steadym decreasedm chronos
                              (pre_fired_transitions ++ pre_fired_trs) pgroups_tail
      (* Error, stpn_fire_pre failed!!! *)
      | None => None
      end
    | [] => Some (pre_fired_transitions, decreasingm)
    end.

  Functional Scheme stpn_map_fire_pre_aux_ind := Induction for stpn_map_fire_pre_aux Sort Prop.
  
  (*** Formal specification : stpn_map_fire_pre_aux ***)
  Inductive StpnMapFirePreAux
            (lneighbours : list (trans_type * neighbours_type))
            (pre test inhib : weight_type)
            (steadym decreasingm : marking_type)
            (chronos : list (trans_type * option chrono_type))
            (pre_fired_transitions : list trans_type) :
    list (list trans_type) -> option (list trans_type * marking_type) -> Prop :=
  | StpnMapFirePreAux_nil :
      StpnMapFirePreAux lneighbours pre test inhib steadym decreasingm chronos pre_fired_transitions []
                        (Some (pre_fired_transitions, decreasingm))
  | StpnMapFirePreAux_cons :
      forall (pgroup pre_fired_trs : list trans_type)
             (decreasedm : marking_type)
             (priority_groups : list (list trans_type))
             (option_final_couple : option (list trans_type * marking_type)),
        StpnFirePre lneighbours pre test inhib steadym decreasingm chronos pgroup
                    (Some (pre_fired_trs, decreasedm)) ->
        StpnMapFirePreAux lneighbours pre test inhib steadym decreasedm chronos (pre_fired_transitions ++ pre_fired_trs)
                          priority_groups
                          option_final_couple ->
        StpnMapFirePreAux lneighbours pre test inhib steadym decreasingm chronos pre_fired_transitions
                          (pgroup :: priority_groups)
                          option_final_couple
  | StpnMapFirePreAux_err :
      forall (pgroup : list trans_type)
             (priority_groups : list (list trans_type)),
        StpnFirePre lneighbours pre test inhib steadym decreasingm chronos pgroup None ->
        StpnMapFirePreAux lneighbours pre test inhib steadym decreasingm chronos pre_fired_transitions
                          (pgroup :: priority_groups) None.

  (*** Correctness proof : stpn_map_fire_pre_aux ***)
  Theorem stpn_map_fire_pre_aux_correct :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)
           (steadym decreasingm : marking_type)
           (chronos : list (trans_type * option chrono_type))
           (priority_groups : list (list trans_type))
           (pre_fired_transitions : list trans_type)
           (option_final_couple : option (list trans_type * marking_type)),
      stpn_map_fire_pre_aux lneighbours pre test inhib steadym decreasingm chronos
                            pre_fired_transitions priority_groups = option_final_couple ->
      StpnMapFirePreAux lneighbours pre test inhib steadym decreasingm chronos
                        pre_fired_transitions priority_groups option_final_couple.
  Proof.
    intros lneighbours pre test inhib steadym decreasingm chronos priority_groups
           pre_fired_transitions.
    functional induction (stpn_map_fire_pre_aux lneighbours pre test inhib steadym decreasingm
                                                chronos
                                                pre_fired_transitions
                                                priority_groups)
               using stpn_map_fire_pre_aux_ind; intros.
    (* Case priority_groups = [] *)
    - rewrite <- H; apply StpnMapFirePreAux_nil.
    (* General case *)
    - apply StpnMapFirePreAux_cons with (pre_fired_trs := pre_fired_trs)
                                       (decreasedm := decreasedm).
      + apply stpn_fire_pre_correct; auto.
      + apply IHo; rewrite H; auto.
    (* Case of error *)
    - rewrite <- H; apply StpnMapFirePreAux_err.
      apply stpn_fire_pre_correct; auto.
  Qed.

  (*** Completeness proof : stpn_map_fire_pre_aux ***)
  Theorem stpn_map_fire_pre_aux_compl :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)
           (steadym decreasingm : marking_type)
           (chronos : list (trans_type * option chrono_type))           
           (priority_groups : list (list trans_type))
           (pre_fired_transitions : list trans_type)
           (option_final_couple : option (list trans_type * marking_type)),
      StpnMapFirePreAux lneighbours pre test inhib steadym decreasingm chronos
                        pre_fired_transitions priority_groups option_final_couple ->
      stpn_map_fire_pre_aux lneighbours pre test inhib steadym decreasingm chronos
                            pre_fired_transitions priority_groups = option_final_couple.
  Proof.
    intros; elim H; intros.
    (* Case StpnMapFirePreAux_nil *)
    - simpl; auto.
    (* Case StpnMapFirePreAux_cons *)
    - simpl; apply stpn_fire_pre_compl in H0; rewrite H0; rewrite H2; auto.
    (* Case StpnMapFirePreAux_err *)
    - simpl; apply stpn_fire_pre_compl in H0; rewrite H0; auto.
  Qed.

  (* Lemma : Proves that stpn_map_fire_pre_aux preserves
   *         the structure of the marking decreasingm
   *         passed as argument. 
   *)
  Lemma stpn_map_fire_pre_aux_same_struct :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)
           (steadym decreasingm : marking_type)
           (chronos : list (trans_type * option chrono_type))
           (pre_fired_transitions : list trans_type)
           (priority_groups : list (list trans_type))
           (final_pre_fired : list trans_type)
           (intermediatem : marking_type),
      stpn_map_fire_pre_aux lneighbours pre test inhib steadym decreasingm chronos
                            pre_fired_transitions priority_groups =
      Some (final_pre_fired, intermediatem) ->
      MarkingHaveSameStruct decreasingm intermediatem.
  Proof.
    intros lneighbours pre test inhib steadym decreasingm chronos
           pre_fired_transitions
           priority_groups.
    functional induction (stpn_map_fire_pre_aux lneighbours
                                               pre test inhib
                                               steadym decreasingm
                                               chronos
                                               pre_fired_transitions priority_groups)
               using stpn_map_fire_pre_aux_ind;
      intros.
    - injection H; intros.
      rewrite H0.
      unfold MarkingHaveSameStruct; auto.
    - apply IHo in H.
      apply stpn_fire_pre_same_struct in e0.
      unfold MarkingHaveSameStruct.
      unfold MarkingHaveSameStruct in e0.
      unfold MarkingHaveSameStruct in H.
      rewrite <- H; rewrite e0; auto.
    - inversion H.
  Qed.

  (*  
   * Lemma : If all transitions in priority_groups are in lneighbours
   *         then all transitions in final_pre_fired (returned by stpn_map_fire_pre_aux) 
   *         are in lneighbours.
   *)
  Lemma stpn_map_fire_pre_aux_final_fired_in_lneighbours :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)
           (steadym decreasingm : marking_type)
           (chronos : list (trans_type * option chrono_type))
           (pre_fired_transitions : list trans_type)
           (priority_groups : list (list trans_type))
           (final_pre_fired : list trans_type)
           (intermediatem : marking_type),
      PriorityGroupsAreRefInLneighbours priority_groups lneighbours ->
      incl pre_fired_transitions (fst (split lneighbours)) ->
      stpn_map_fire_pre_aux lneighbours pre test inhib steadym decreasingm chronos
                            pre_fired_transitions priority_groups =
      Some (final_pre_fired, intermediatem) ->
      incl final_pre_fired (fst (split lneighbours)).
  Proof.
    unfold PriorityGroupsAreRefInLneighbours.
    unfold incl.
    intros lneighbours pre test inhib steadym decreasingm chronos
           pre_fired_transitions priority_groups.
    functional induction (stpn_map_fire_pre_aux lneighbours pre test inhib
                                                steadym decreasingm
                                                chronos
                                                pre_fired_transitions
                                                priority_groups)
               using stpn_map_fire_pre_aux_ind;
      intros.
    (* Base case, priority_groups = []. *)
    - injection H1; intros.
      rewrite <- H4 in H2; apply H0 in H2; auto.
    (* Case stpn_fire_pre returns Some value. *)
    - apply IHo with (final_pre_fired := final_pre_fired)
                     (intermediatem := intermediatem).
      + intros.
        apply (in_cons pgroup) in H3.
        generalize (H pgroup0 H3); intros.
        apply H5 in H4; auto.
      + intros.
        generalize (H pgroup); intros.
        apply in_eq_impl in H4.
        (*  
         * We need to use the lemma saying
         * that all transitions in pre_fired_trs are
         * referenced in lneighbours.
         *)
        generalize (stpn_fire_pre_final_fired_in_lneighbours
                      lneighbours pre test inhib
                      steadym decreasingm
                      chronos0
                      pgroup
                      pre_fired_trs
                      decreasedm H4 e0).
        intros.
        apply in_app_or in H3; elim H3; intros;
          [apply H0 in H6; auto | apply H5 in H6; auto].
      + auto.
      + auto.
    (* Case stpn_fire_pre returns an error,
     * then contradiction.
     *)
    - inversion H1.
  Qed.

  (*  
   * Lemma : If all transitions in priority_groups are ref in chronos
   *         then all transitions in final_pre_fired (returned by stpn_map_fire_pre_aux) 
   *         are ref in chronos.
   *)
  Lemma stpn_map_fire_pre_aux_final_fired_in_chronos :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)
           (steadym decreasingm : marking_type)
           (chronos : list (trans_type * option chrono_type))
           (pre_fired_transitions : list trans_type)
           (priority_groups : list (list trans_type))
           (final_pre_fired : list trans_type)
           (intermediatem : marking_type),
      PriorityGroupsAreRefInChronos priority_groups chronos ->
      incl pre_fired_transitions (fst (split chronos)) ->
      stpn_map_fire_pre_aux lneighbours pre test inhib steadym decreasingm chronos
                            pre_fired_transitions priority_groups =
      Some (final_pre_fired, intermediatem) ->
      incl final_pre_fired (fst (split chronos)).
  Proof.
    unfold PriorityGroupsAreRefInChronos.
    unfold incl.
    intros lneighbours pre test inhib steadym decreasingm chronos
           pre_fired_transitions priority_groups.
    functional induction (stpn_map_fire_pre_aux lneighbours pre test inhib
                                                steadym decreasingm
                                                chronos
                                                pre_fired_transitions
                                                priority_groups)
               using stpn_map_fire_pre_aux_ind;
      intros.
    (* Base case, priority_groups = []. *)
    - injection H1; intros.
      rewrite <- H4 in H2; apply H0 in H2; auto.
    (* Case stpn_fire_pre returns Some value. *)
    - apply IHo with (final_pre_fired := final_pre_fired)
                     (intermediatem := intermediatem).
      + intros.
        apply (in_cons pgroup) in H3.
        generalize (H pgroup0 H3); intros.
        apply H5 in H4; auto.
      + intros.
        generalize (H pgroup); intros.
        apply in_eq_impl in H4.
        (*  
         * We need to use the lemma saying
         * that all transitions in pre_fired_trs are
         * referenced in chronos.
         *)
        generalize (stpn_fire_pre_final_fired_in_chronos
                      lneighbours pre test inhib
                      steadym decreasingm
                      chronos0
                      pgroup
                      pre_fired_trs
                      decreasedm H4 e0).
        intros.
        apply in_app_or in H3; elim H3; intros;
          [apply H0 in H6; auto | apply H5 in H6; auto].
      + auto.
      + auto.
    (* Case stpn_fire_pre returns an error,
     * then contradiction.
     *)
    - inversion H1.
  Qed.

  (*
   * Lemma : stpn_map_fire_pre_aux returns no error if 
   *         forall pgroup of transitions in priority_groups,
   *         transitions are referenced in chronos and
   *         transitions are referenced in lneighbours and
   *         neighbours places (of these transitions) are referenced 
   *         in markings steadym and decreasingm.
   *)
  Lemma stpn_map_fire_pre_aux_no_error :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)
           (steadym decreasingm : marking_type)
           (chronos : list (trans_type * option chrono_type))
           (priority_groups : list (list trans_type))
           (pre_fired_transitions : list trans_type),
      PriorityGroupsAreRefInChronos priority_groups chronos ->
      PriorityGroupsAreRefInLneighbours priority_groups lneighbours ->
      (forall (t : trans_type) (neighbours : neighbours_type),
          In (t, neighbours) lneighbours ->
          (incl neighbours.(pre_pl) (fst (split decreasingm)) /\
           incl neighbours.(inhib_pl) (fst (split steadym)) /\
           incl neighbours.(test_pl) (fst (split steadym)))) ->
      exists v : (list trans_type * marking_type),
        stpn_map_fire_pre_aux lneighbours pre test inhib steadym decreasingm
                              chronos pre_fired_transitions priority_groups = Some v.
  Proof.
    unfold PriorityGroupsAreRefInChronos.
    unfold PriorityGroupsAreRefInLneighbours.
    unfold incl.
    intros lneighbours pre test inhib steadym decreasingm
           chronos priority_groups pre_fired_transitions.
    functional induction (stpn_map_fire_pre_aux lneighbours pre test inhib steadym decreasingm
                                                chronos pre_fired_transitions priority_groups)
               using stpn_map_fire_pre_aux_ind;
      intros.
    (* Base case, priority_groups = []. *)
    - exists (pre_fired_transitions, decreasingm); auto.
    (* Case stpn_fire_pre = Some v *)
    - apply IHo.
      + intros.
        apply (in_cons pgroup) in H2.
        generalize (H pgroup0 H2); intro; auto.
      + intros.
        apply (in_cons pgroup) in H2.
        generalize (H0 pgroup0 H2); intro; auto.
      + apply stpn_fire_pre_same_struct in e0.
        unfold MarkingHaveSameStruct in e0.
        rewrite <- e0.
        auto.
    (* Case stpn_fire_pre = None, impossible regarding the hypotheses. *)
    - assert (H' := in_eq pgroup pgroups_tail).      
      generalize (H pgroup H'); intro.
      generalize (H0 pgroup H'); intro.
      generalize (stpn_fire_pre_no_error lneighbours pre test inhib
                                         steadym decreasingm
                                         chronos0 pgroup H2 H3 H1).
      intro; elim H4; intros; rewrite H5 in e0; inversion e0.
  Qed.
  
  (***********************************************************************)
  (***********************************************************************)
  
  (*
   * Function : Wrapper around stpn_map_fire_pre_aux function. 
   *            Update the marking by consuming
   *            the tokens in pre-condition places.            
   *)
  Definition stpn_map_fire_pre
             (lneighbours : list (trans_type * neighbours_type))
             (pre test inhib : weight_type)
             (m : marking_type)
             (chronos : list (trans_type * option chrono_type))
             (priority_groups : list (list trans_type)) :
    option (list trans_type * marking_type) :=
    stpn_map_fire_pre_aux lneighbours pre test inhib m m chronos [] priority_groups.

  Functional Scheme stpn_map_fire_pre_ind := Induction for stpn_map_fire_pre Sort Prop.
  
  (*** Formal specification : stpn_map_fire_pre ***)
  Inductive StpnMapFirePre
            (lneighbours : list (trans_type * neighbours_type))
            (pre test inhib : weight_type)
            (m : marking_type)
            (chronos : list (trans_type * option chrono_type))
            (priority_groups : list (list trans_type)) :
    option (list trans_type * marking_type) -> Prop :=
  | StpnMapFirePre_cons :
      forall (option_final_couple : option (list trans_type * marking_type)),
        StpnMapFirePreAux lneighbours pre test inhib m m chronos [] priority_groups
                          option_final_couple ->
        StpnMapFirePre lneighbours pre test inhib m chronos priority_groups option_final_couple.

  (*** Correctness proof : stpn_map_fire_pre ***)
  Theorem stpn_map_fire_pre_correct :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)
           (m : marking_type)
           (chronos : list (trans_type * option chrono_type))
           (priority_groups : list (list trans_type))
           (option_final_couple : option (list trans_type * marking_type)),
      stpn_map_fire_pre lneighbours pre test inhib m chronos priority_groups = option_final_couple ->
      StpnMapFirePre lneighbours pre test inhib m chronos priority_groups option_final_couple.  
  Proof.
    intros lneighbours pre test inhib m chronos priority_groups option_final_couple H.
    apply StpnMapFirePre_cons.
    apply stpn_map_fire_pre_aux_correct.
    auto.
  Qed.

  (*** Completeness proof : stpn_map_fire_pre ***)
  Theorem stpn_map_fire_pre_compl :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)
           (m : marking_type)
           (chronos : list (trans_type * option chrono_type))
           (priority_groups : list (list trans_type))
           (option_final_couple : option (list trans_type * marking_type)),
      StpnMapFirePre lneighbours pre test inhib m chronos priority_groups
                     option_final_couple ->
      stpn_map_fire_pre lneighbours pre test inhib m chronos priority_groups = option_final_couple.
  Proof.
    intros; elim H; intros.
    unfold stpn_map_fire_pre.
    apply stpn_map_fire_pre_aux_compl; auto.
  Qed.

  (*  
   * Lemma : If all transitions in priority_groups are in lneighbours
   *         then all transitions in final_pre_fired (returned by stpn_map_fire_pre) 
   *         are in lneighbours.
   *)
  Lemma stpn_map_fire_pre_final_fired_in_lneighbours :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)
           (m : marking_type)
           (chronos : list (trans_type * option chrono_type))
           (priority_groups : list (list trans_type))
           (final_pre_fired : list trans_type)
           (intermediatem : marking_type),
      PriorityGroupsAreRefInLneighbours priority_groups lneighbours ->
      stpn_map_fire_pre lneighbours pre test inhib m chronos priority_groups =
      Some (final_pre_fired, intermediatem) ->
      incl final_pre_fired (fst (split lneighbours)).
  Proof.
    unfold PriorityGroupsAreRefInLneighbours.
    unfold incl.
    intros lneighbours pre test inhib m chronos priority_groups.
    functional induction (stpn_map_fire_pre lneighbours pre test inhib m chronos priority_groups)
               using stpn_map_fire_pre_ind; intros.
    cut (forall t : trans_type, In t [] -> In t (fst (split lneighbours))); intros.
    - generalize (stpn_map_fire_pre_aux_final_fired_in_lneighbours
                    lneighbours pre test inhib m m chronos [] priority_groups
                    final_pre_fired intermediatem
                    H H2 H0).
      intros.
      apply H3 in H1; auto.
    - elim H2.
  Qed.

  (*  
   * Lemma : If all transitions in priority_groups are ref in chronos
   *         then all transitions in final_pre_fired (returned by stpn_map_fire_pre) 
   *         are ref in chronos.
   *)
  Lemma stpn_map_fire_pre_final_fired_in_chronos :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)
           (m : marking_type)
           (chronos : list (trans_type * option chrono_type))
           (priority_groups : list (list trans_type))
           (final_pre_fired : list trans_type)
           (intermediatem : marking_type),
      PriorityGroupsAreRefInChronos priority_groups chronos ->
      stpn_map_fire_pre lneighbours pre test inhib m chronos priority_groups =
      Some (final_pre_fired, intermediatem) ->
      incl final_pre_fired (fst (split chronos)).
  Proof.
    unfold PriorityGroupsAreRefInChronos.
    unfold incl.
    intros lneighbours pre test inhib m chronos priority_groups.
    functional induction (stpn_map_fire_pre lneighbours pre test inhib m chronos priority_groups)
               using stpn_map_fire_pre_ind; intros.
    cut (forall t : trans_type, In t [] -> In t (fst (split chronos))); intros.
    - generalize (stpn_map_fire_pre_aux_final_fired_in_chronos
                    lneighbours pre test inhib m m chronos [] priority_groups
                    final_pre_fired intermediatem
                    H H2 H0).
      intros.
      apply H3 in H1; auto.
    - elim H2.
  Qed.
  
  (*
   * Lemma : stpn_map_fire_pre returns no error if 
   *         forall pgroup of transitions in priority_groups,
   *         transitions are referenced in chronos and
   *         transitions are referenced in lneighbours and
   *         neighbours places (of these transitions) are referenced 
   *         in markings steadym and decreasingm.
   *)
  Lemma stpn_map_fire_pre_no_error :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)
           (m : marking_type)
           (chronos : list (trans_type * option chrono_type))
           (priority_groups : list (list trans_type)),
      PriorityGroupsAreRefInChronos priority_groups chronos ->
      PriorityGroupsAreRefInLneighbours priority_groups lneighbours ->
      (forall (t : trans_type) (neighbours : neighbours_type),
          In (t, neighbours) lneighbours ->
          (PlacesAreRefInMarking neighbours.(pre_pl) m /\
           PlacesAreRefInMarking neighbours.(inhib_pl) m /\
           PlacesAreRefInMarking neighbours.(test_pl) m)) ->
      exists v : (list trans_type * marking_type),
        stpn_map_fire_pre lneighbours pre test inhib m chronos priority_groups = Some v.
  Proof.
    intros lneighbours pre test inhib m chronos priority_groups.
    unfold stpn_map_fire_pre; intros.
    apply stpn_map_fire_pre_aux_no_error; [ auto | auto | auto ].
  Qed.

  (* Lemma : Proves that stpn_map_fire_pre preserves
   *         the structure of the marking m
   *         passed as argument. 
   *)
  Lemma stpn_map_fire_pre_same_struct :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)
           (m : marking_type)
           (chronos : list (trans_type * option chrono_type))
           (priority_groups : list (list trans_type))
           (final_pre_fired : list trans_type)
           (intermediatem : marking_type),
      stpn_map_fire_pre lneighbours pre test inhib m chronos priority_groups =
      Some (final_pre_fired, intermediatem) ->
      MarkingHaveSameStruct m intermediatem.
  Proof.
    intros lneighbours pre test inhib m chronos priority_groups.
    functional induction (stpn_map_fire_pre lneighbours pre test inhib m chronos priority_groups)
               using stpn_map_fire_pre_ind; intros.
    apply stpn_map_fire_pre_aux_same_struct in H; auto.
  Qed.

  (***********************************************************************)
  (***********************************************************************)
  
  (* 
   * Function : Returns a tuplet (fired transitions (at this cycle), 
   *                              final marking, 
   *                              final chronos).
   *            
   *            Raises an error (None value) if stpn_map_fire_pre, reset_all_chronos,
   *            list_disabled, or fire_post return None.            
   *
   *            This function has the same structure has spn_fire, except
   *            that stpn_fire adds some instructions to reset chronos
   *            between the pre-firing and the post-firing phases.
   *
   *            
   *)
  Definition stpn_fire  
             (lneighbours : list (trans_type * neighbours_type))
             (pre test inhib post : weight_type)
             (m : marking_type)
             (chronos : list (trans_type * option chrono_type))
             (transs : list trans_type)
             (priority_groups : list (list trans_type)) :
    option ((list trans_type) * marking_type * (list (trans_type * option chrono_type))) :=
    (* Pre-fires the transitions in priority_groups. *)
    match stpn_map_fire_pre lneighbours pre test inhib m chronos priority_groups with
    | Some (pre_fired_transitions, intermediatem) =>
      (* Resets chronos for all pre-fired transitions. *)
      match reset_all_chronos chronos pre_fired_transitions with
      | Some updated_chronos =>
        (* Lists transitions disabled by the pre-firing, and resets their chronos. *)
        match list_disabled lneighbours pre test inhib m transs with
        | Some disabled_transs =>
          match reset_all_chronos updated_chronos disabled_transs with
          | Some final_chronos =>
            (* Post-fires the pre-fired transitions, then returns the final tuplet. *)
            match fire_post lneighbours post intermediatem pre_fired_transitions with
            | Some finalm => Some (pre_fired_transitions, finalm, final_chronos)
            (* Error, fire_post failed!!! *)
            | None => None
            end
          (* Error, reset_all_chronos failed!!! *)
          | None => None
          end
        (* Error, list_disabled failed!!! *)
        | None => None
        end
      (* Error, reset_all_chronos failed!!! *)
      | None => None
      end
    (* Error, stpn_map_fire_pre failed!!! *)
    | None => None
    end.

  Functional Scheme stpn_fire_ind := Induction for stpn_fire Sort Prop.
  
  (*** Formal specification : stpn_fire ***)
  Inductive StpnFire
            (lneighbours : list (trans_type * neighbours_type))
            (pre test inhib post : weight_type)
            (m : marking_type)
            (chronos : list (trans_type * option chrono_type))
            (transs : list trans_type)
            (priority_groups : list (list trans_type)) :
    option ((list trans_type) * marking_type * (list (trans_type * option chrono_type))) ->
    Prop :=
  | StpnFire_fire_pre_err :
      StpnMapFirePre lneighbours pre test inhib m chronos priority_groups None ->
      StpnFire lneighbours pre test inhib post m chronos transs priority_groups None
  | StpnFire_reset_chronos_err1 :
      forall (pre_fired_transitions : list trans_type)
             (intermediatem : marking_type),
        StpnMapFirePre lneighbours pre test inhib m chronos priority_groups
                       (Some (pre_fired_transitions, intermediatem)) ->
        ResetAllChronos chronos pre_fired_transitions None ->
        StpnFire lneighbours pre test inhib post m chronos transs priority_groups None
  | StpnFire_list_disabled_err :
      forall (pre_fired_transitions : list trans_type)
             (intermediatem : marking_type)
             (updated_chronos : list (trans_type * option chrono_type)),
        StpnMapFirePre lneighbours pre test inhib m chronos priority_groups
                       (Some (pre_fired_transitions, intermediatem)) ->
        ResetAllChronos chronos pre_fired_transitions (Some updated_chronos) ->
        ListDisabled lneighbours pre test inhib m transs None -> 
        StpnFire lneighbours pre test inhib post m chronos transs priority_groups None
  | StpnFire_reset_chronos_err2 :
      forall (pre_fired_transitions : list trans_type)
             (intermediatem : marking_type)
             (updated_chronos : list (trans_type * option chrono_type))
             (disabled_transs : list trans_type),
        StpnMapFirePre lneighbours pre test inhib m chronos priority_groups
                       (Some (pre_fired_transitions, intermediatem)) ->
        ResetAllChronos chronos pre_fired_transitions (Some updated_chronos) ->
        ListDisabled lneighbours pre test inhib m transs (Some disabled_transs) -> 
        ResetAllChronos updated_chronos disabled_transs None ->
        StpnFire lneighbours pre test inhib post m chronos transs priority_groups None
  | StpnFire_fire_post_err :
      forall (pre_fired_transitions : list trans_type)
             (intermediatem : marking_type)
             (updated_chronos : list (trans_type * option chrono_type))
             (disabled_transs : list trans_type)
             (final_chronos : list (trans_type * option chrono_type)),
        StpnMapFirePre lneighbours pre test inhib m chronos priority_groups
                       (Some (pre_fired_transitions, intermediatem)) ->
        ResetAllChronos chronos pre_fired_transitions (Some updated_chronos) ->
        ListDisabled lneighbours pre test inhib m transs (Some disabled_transs) -> 
        ResetAllChronos updated_chronos disabled_transs (Some final_chronos) ->
        FirePost lneighbours post intermediatem pre_fired_transitions None ->
        StpnFire lneighbours pre test inhib post m chronos transs priority_groups None
  | StpnFire_cons :
      forall (pre_fired_transitions : list trans_type)
             (intermediatem : marking_type)
             (updated_chronos : list (trans_type * option chrono_type))
             (disabled_transs : list trans_type)
             (final_chronos : list (trans_type * option chrono_type))
             (finalm : marking_type),
        StpnMapFirePre lneighbours pre test inhib m chronos priority_groups
                       (Some (pre_fired_transitions, intermediatem)) ->
        ResetAllChronos chronos pre_fired_transitions (Some updated_chronos) ->
        ListDisabled lneighbours pre test inhib m transs (Some disabled_transs) -> 
        ResetAllChronos updated_chronos disabled_transs (Some final_chronos) ->
        FirePost lneighbours post intermediatem pre_fired_transitions (Some finalm) ->
        StpnFire lneighbours pre test inhib post m chronos transs priority_groups
                 (Some (pre_fired_transitions, finalm, final_chronos)).

  (*** Correctness proof : stpn_fire ***)
  Theorem stpn_fire_correct :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib post : weight_type)
           (m : marking_type)
           (chronos : list (trans_type * option chrono_type))
           (transs : list trans_type)
           (priority_groups : list (list trans_type))
           (opt_final_tuplet : option ((list trans_type) *
                                       marking_type *
                                       (list (trans_type * option chrono_type)))),
      stpn_fire lneighbours pre test inhib post m chronos transs priority_groups =
      opt_final_tuplet ->
      StpnFire lneighbours pre test inhib post m chronos transs priority_groups opt_final_tuplet.
  Proof.
    intros lneighbours pre test inhib post m chronos transs priority_groups.
    functional induction (stpn_fire lneighbours pre test inhib post m
                                    chronos transs priority_groups)
               using stpn_fire_ind; intros.
    (* General case, all went well. *)
    - rewrite <- H; apply StpnFire_cons with (intermediatem := intermediatem)
                                             (updated_chronos := updated_chronos)
                                             (disabled_transs := disabled_transs).
      + apply stpn_map_fire_pre_correct in e; auto.
      + apply reset_all_chronos_correct in e1; auto.
      + apply list_disabled_correct in e2; auto.
      + apply reset_all_chronos_correct in e3; auto.
      + apply fire_post_correct in e4; auto.
    (* Error case, fire_post returns None. *)
    - rewrite <- H; apply StpnFire_fire_post_err
                      with (pre_fired_transitions := pre_fired_transitions)
                           (intermediatem := intermediatem)
                           (updated_chronos := updated_chronos)
                           (disabled_transs := disabled_transs)
                           (final_chronos := final_chronos).
      + apply stpn_map_fire_pre_correct in e; auto.
      + apply reset_all_chronos_correct in e1; auto.
      + apply list_disabled_correct in e2; auto.
      + apply reset_all_chronos_correct in e3; auto.
      + apply fire_post_correct in e4; auto.
    (* Error case, 2nd reset_all_chronos returns None. *)
    - rewrite <- H; apply StpnFire_reset_chronos_err2
                      with (pre_fired_transitions := pre_fired_transitions)
                           (intermediatem := intermediatem)
                           (updated_chronos := updated_chronos)
                           (disabled_transs := disabled_transs).
      + apply stpn_map_fire_pre_correct in e; auto.
      + apply reset_all_chronos_correct in e1; auto.
      + apply list_disabled_correct in e2; auto.
      + apply reset_all_chronos_correct in e3; auto.
    (* Error case, list_disabled returns None. *)
    - rewrite <- H; apply StpnFire_list_disabled_err
                      with (pre_fired_transitions := pre_fired_transitions)
                           (intermediatem := intermediatem)
                           (updated_chronos := updated_chronos).
      + apply stpn_map_fire_pre_correct in e; auto.
      + apply reset_all_chronos_correct in e1; auto.
      + apply list_disabled_correct in e2; auto.
    (* Error case, 1st reset_all_chronos returns None. *)
    - rewrite <- H; apply StpnFire_reset_chronos_err1
                      with (pre_fired_transitions := pre_fired_transitions)
                           (intermediatem := intermediatem).
      + apply stpn_map_fire_pre_correct in e; auto.
      + apply reset_all_chronos_correct in e1; auto.
    (* Error case, stpn_map_fire_pre returns None. *)
    - rewrite <- H; apply StpnFire_fire_pre_err.
      + apply stpn_map_fire_pre_correct in e; auto.
  Qed.

  (*** Completeness proof : stpn_fire ***)
  Theorem stpn_fire_compl :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib post : weight_type)
           (m : marking_type)
           (chronos : list (trans_type * option chrono_type))
           (transs : list trans_type)
           (priority_groups : list (list trans_type))
           (opt_final_tuplet : option ((list trans_type) *
                                       marking_type *
                                       (list (trans_type * option chrono_type)))),
      StpnFire lneighbours pre test inhib post m chronos transs priority_groups opt_final_tuplet ->
      stpn_fire lneighbours pre test inhib post m chronos transs priority_groups = opt_final_tuplet.
  Proof.
    intros lneighbours pre test inhib post m chronos transs priority_groups opt_final_tuplet H.
    elim H; intros.
    (* Case StpnFire_fire_pre_err *)
    - unfold stpn_fire.
      apply stpn_map_fire_pre_compl in H0; rewrite H0; auto.
    (* Case StpnFire_reset_chronos_err1 *)
    - unfold stpn_fire.
      apply stpn_map_fire_pre_compl in H0; rewrite H0.
      apply reset_all_chronos_complete in H1; rewrite H1; auto.
    (* Case StpnFire_list_disabled_err *)
    - unfold stpn_fire.
      apply stpn_map_fire_pre_compl in H0; rewrite H0.
      apply reset_all_chronos_complete in H1; rewrite H1.
      apply list_disabled_complete in H2; rewrite H2; auto.
    (* Case StpnFire_reset_chronos_err2 *)
    - unfold stpn_fire.
      apply stpn_map_fire_pre_compl in H0; rewrite H0.
      apply reset_all_chronos_complete in H1; rewrite H1.
      apply list_disabled_complete in H2; rewrite H2.
      apply reset_all_chronos_complete in H3; rewrite H3; auto.
    (* Case StpnFire_reset_chronos_err2 *)
    - unfold stpn_fire.
      apply stpn_map_fire_pre_compl in H0; rewrite H0.
      apply reset_all_chronos_complete in H1; rewrite H1.
      apply list_disabled_complete in H2; rewrite H2.
      apply reset_all_chronos_complete in H3; rewrite H3.
      apply fire_post_compl in H4; rewrite H4; auto.
    (* Case StpnFire_cons *)
    - unfold stpn_fire.
      apply stpn_map_fire_pre_compl in H0; rewrite H0.
      apply reset_all_chronos_complete in H1; rewrite H1.
      apply list_disabled_complete in H2; rewrite H2.
      apply reset_all_chronos_complete in H3; rewrite H3.
      apply fire_post_compl in H4; rewrite H4; auto.      
  Qed.

  (* Lemma : Proves that stpn_fire preserves
   *         the structure of the marking m
   *         passed as argument. 
   *)  
  Lemma stpn_fire_same_struct_marking :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib post : weight_type)
           (m : marking_type)
           (chronos : list (trans_type * option chrono_type))
           (transs : list trans_type)
           (priority_groups : list (list trans_type))
           (fired_transitions : list (trans_type))
           (newm : marking_type)
           (new_chronos : list (trans_type * option chrono_type)),
      stpn_fire lneighbours pre test inhib post m chronos transs priority_groups =
      Some (fired_transitions, newm, new_chronos) ->
      MarkingHaveSameStruct m newm.
  Proof.
    intros lneighbours pre test inhib post m chronos transs priority_groups.
    functional induction (stpn_fire lneighbours pre test inhib post m
                                    chronos transs priority_groups)
               using stpn_fire_ind;
      intros.
    injection H; intros; rewrite <- H1; auto.
    generalize (stpn_map_fire_pre_same_struct
                  lneighbours pre test inhib m chronos priority_groups
                  pre_fired_transitions intermediatem e); intro.
    - generalize (fire_post_same_struct
                    lneighbours post intermediatem
                    pre_fired_transitions finalm e4); intro.
      unfold MarkingHaveSameStruct in H3; unfold MarkingHaveSameStruct in H4.
      unfold MarkingHaveSameStruct.
      transitivity (fst (split intermediatem)); [auto | auto].
    - inversion H.
    - inversion H.
    - inversion H.
    - inversion H.
    - inversion H.
  Qed.

  (* Lemma : Proves that stpn_fire preserves
   *         the structure of the chronos
   *         passed as argument. 
   *)  
  Lemma stpn_fire_same_struct_chronos :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib post : weight_type)
           (m : marking_type)
           (chronos : list (trans_type * option chrono_type))
           (transs : list trans_type)
           (priority_groups : list (list trans_type))
           (fired_transitions : list (trans_type))
           (newm : marking_type)
           (new_chronos : list (trans_type * option chrono_type)),
      stpn_fire lneighbours pre test inhib post m chronos transs priority_groups =
      Some (fired_transitions, newm, new_chronos) ->
      ChronosHaveSameStruct chronos new_chronos.
  Proof.
    intros lneighbours pre test inhib post m chronos transs priority_groups.
    functional induction (stpn_fire lneighbours pre test inhib post m
                                    chronos transs priority_groups)
               using stpn_fire_ind; intros.
    - injection H; intros; rewrite <- H0; auto.
      generalize (reset_all_chronos_same_struct
                    chronos pre_fired_transitions updated_chronos e1); intro.
      generalize (reset_all_chronos_same_struct
                    updated_chronos disabled_transs final_chronos e3); intro.
      unfold ChronosHaveSameStruct in H3; unfold ChronosHaveSameStruct in H4.
      unfold ChronosHaveSameStruct.
      transitivity (fst (split updated_chronos)); [auto | auto].
    - inversion H.
    - inversion H.
    - inversion H.
    - inversion H.
    - inversion H.
  Qed.
  
  (*  
   * Lemma : Proves that stpn_fire returns no error if :
   *         - All transitions in transs are ref in chronos and lneighbours.
   *         - All pgroups in priority_groups are ref in chronos and lneighbours.
   *         - All places in lneighbours are ref in m.
   *)
  Lemma stpn_fire_no_error :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib post : weight_type)
           (m : marking_type)
           (chronos : list (trans_type * option chrono_type))
           (transs : list trans_type)
           (priority_groups : list (list trans_type)),
      incl transs (fst (split chronos)) ->
      incl transs (fst (split lneighbours)) ->
      PriorityGroupsAreRefInChronos priority_groups chronos ->
      PriorityGroupsAreRefInLneighbours priority_groups lneighbours ->
      (forall (t : trans_type) (neighbours : neighbours_type),
          In (t, neighbours) lneighbours ->
          (incl neighbours.(pre_pl) (fst (split m)) /\
           incl neighbours.(inhib_pl) (fst (split m)) /\
           incl neighbours.(test_pl) (fst (split m)))) ->
      (forall (t : trans_type) (neighbours : neighbours_type),
          In (t, neighbours) lneighbours ->
          incl neighbours.(post_pl) (fst (split m))) ->
      exists v : (list trans_type * marking_type * list (trans_type * option chrono_type)),
        stpn_fire lneighbours pre test inhib post m chronos transs priority_groups = Some v.
  Proof.
    unfold incl.
    unfold PriorityGroupsAreRefInChronos.
    unfold PriorityGroupsAreRefInLneighbours.
    intros lneighbours pre test inhib post m chronos transs priority_groups.
    functional induction (stpn_fire lneighbours pre test inhib post m
                                    chronos transs priority_groups)
               using stpn_fire_ind;
      intros.
    (* GENERAL CASE, all functions returned Some value. *)
    - exists (pre_fired_transitions, finalm, final_chronos); auto.
    (* CASE fire_post returns None, 
     * impossible according to the hypotheses.
     *)
    (* First we need the hypothesis that said that
     * all transitions in the list pre_fired_transitions
     * are referenced in lneighbours.
     *)
    - generalize (stpn_map_fire_pre_final_fired_in_lneighbours
                    lneighbours
                    pre test inhib m chronos priority_groups
                    pre_fired_transitions intermediatem
                    H2 e); intros.
      (* Then we need transform our hypotheses,  
       * using the fact that intermediate marking
       * have the same structure as the first marking.
       *)
      apply stpn_map_fire_pre_same_struct in e.
      unfold MarkingHaveSameStruct in e.
      rewrite e in H4.
      generalize (fire_post_no_error lneighbours post intermediatem pre_fired_transitions H5 H4).
      intros.
      elim H6; intros.
      rewrite H7 in e4.
      inversion e4.
    (* CASE 2nd call to reset_all_chronos returns None,
     * impossible according to the hypotheses.
     *)
    (*  
     * To deduce (incl disabled_transs (fst (split updated_chronos)))
     * and apply reset_all_chronos_no_error, we need to ensure :
     *
     * - (incl disabled_transs transs), then use incl_tran
     *   to deduce incl disabled (fst (split chronos).
     * - ChronosHaveSameStruct chronos updated_chronos,
     *   then rewrite (fst (split chronos) in (fst (split updated_chronos).
     *)
    - generalize (list_disabled_incl_transs
                    lneighbours pre test inhib m transs disabled_transs e2); intros.
      generalize (incl_tran H5 H); intros.
      generalize (reset_all_chronos_same_struct
                    chronos pre_fired_transitions updated_chronos e1); intros.
      unfold ChronosHaveSameStruct in H7.
      rewrite H7 in H6.
      generalize (reset_all_chronos_no_error
                    updated_chronos disabled_transs H6); intros.
      elim H8; intros; rewrite H9 in e3; inversion e3.
    (* CASE list_disabled returns None,
     * impossible according to the hypotheses.
     *)
    - generalize (list_disabled_no_error
                    lneighbours pre test inhib m transs
                    H0 H3); intros.
      elim H5; intros; rewrite H6 in e2; inversion e2.
    (* CASE 1st reset_all_chronos returns None,
     * impossible according to the hypotheses.
     *)
    (* We need (incl pre_fired_transitions chronos) 
     * in order to apply reset_all_chronos_no_error.
     *)
    - generalize (stpn_map_fire_pre_final_fired_in_chronos
                    lneighbours pre test inhib m chronos priority_groups
                    pre_fired_transitions intermediatem
                    H1 e); intros.
      generalize (reset_all_chronos_no_error
                    chronos pre_fired_transitions H5); intros.
      elim H6; intros; rewrite H7 in e1; inversion e1.
    (* CASE stpn_map_fire_pre returns None,
     * impossible according to the hypotheses.
     *)
    - generalize (stpn_map_fire_pre_no_error
                    lneighbours pre test inhib m chronos priority_groups
                    H1 H2 H3); intros.
      elim H5; intros.
      rewrite H6 in e.
      inversion e.
  Qed.  
  
End FireStpn.

(*
 * Helper functions to access the different elements
 * of a tuplet. 
 *)
Section Tuplet.
  
  Context {A : Type} {B : Type} {C : Type}.

  Definition fst_tuplet (tuplet : A * B * C) := match tuplet with
                                                | (x, y, z) => x
                                                end.
  Definition snd_tuplet (tuplet : A * B * C) := match tuplet with
                                                | (x, y, z) => y
                                                end.
  Definition trd_tuplet (tuplet : A * B * C) := match tuplet with
                                                | (x, y, z) => z
                                                end.
End Tuplet.

(*==========================================================*)
(*================= STPN CYCLE EVOLUTION ===================*)
(*==========================================================*)

Section AnimateStpn.
  
  (*  
   * Function : Returns the resulting Petri net after all the sensitized
   *            transitions - with right chrono value - in stpn have been fired.
   *            Also returns the list of fired transitions.
   *)
  Definition stpn_cycle (stpn : STPN) : option ((list trans_type) * STPN)  :=
    match stpn with
    | mk_STPN
        chronos
        (mk_SPN places transs pre post test inhib marking priority_groups lneighbours) =>
      (* Lists all sensitized transitions. *)
      match list_sensitized lneighbours pre test inhib marking transs with
      | Some sensitized_transs =>           
        (* Increments all chronos for the sensitized transitions. *)
        match increment_all_chronos chronos sensitized_transs with
        | Some updated_chronos =>
          match stpn_fire lneighbours pre test inhib post marking updated_chronos transs priority_groups with
          | Some (fired_transitions, nextm, next_chronos) =>
            Some (fired_transitions,
                  (mk_STPN
                     next_chronos
                     (mk_SPN places transs pre post test inhib nextm priority_groups lneighbours)))
          (* Error, stpn_fire failed!!! *)
          | None => None
          end
        (* Error, increment_all_chronos failed!!! *)
        | None => None
        end
      (* Error, list_sensitized failed. *)
      | None => None
      end
    end.

  Functional Scheme stpn_cycle_ind := Induction for stpn_cycle Sort Prop.
  
  (* Formal specification : stpn_cycle *)
  Inductive StpnCycle (stpn : STPN) :
    option ((list trans_type) * STPN) -> Prop :=
  | StpnCycle_list_sensitized_err :
      forall (chronos : list (trans_type * option chrono_type))
             (places : list place_type)
             (transs : list trans_type)
             (pre post test inhib : weight_type)
             (marking : marking_type)
             (priority_groups : list (list trans_type))
             (lneighbours : list (trans_type * neighbours_type)),
        stpn = (mk_STPN
                  chronos
                  (mk_SPN places transs pre post test inhib marking priority_groups lneighbours)) ->
        ListSensitized lneighbours pre test inhib marking transs None ->
        StpnCycle stpn None
  | StpnCycle_increment_chronos_err :
      forall (chronos : list (trans_type * option chrono_type))
             (places : list place_type)
             (transs : list trans_type)
             (pre post test inhib : weight_type)
             (marking : marking_type)
             (priority_groups : list (list trans_type))
             (lneighbours : list (trans_type * neighbours_type))
             (sensitized_transs : list trans_type),
        stpn = (mk_STPN
                  chronos
                  (mk_SPN places transs pre post test inhib marking priority_groups lneighbours)) ->
        ListSensitized lneighbours pre test inhib marking transs (Some sensitized_transs) ->
        IncrementAllChronos chronos sensitized_transs None ->
        StpnCycle stpn None
  | StpnCycle_fire_err :
      forall (chronos : list (trans_type * option chrono_type))
             (places : list place_type)
             (transs : list trans_type)
             (pre post test inhib : weight_type)
             (marking : marking_type)
             (priority_groups : list (list trans_type))
             (lneighbours : list (trans_type * neighbours_type))
             (sensitized_transs : list trans_type)
             (updated_chronos : list (trans_type * option chrono_type)),
        stpn = (mk_STPN
                  chronos
                  (mk_SPN places transs pre post test inhib marking priority_groups lneighbours)) ->
        ListSensitized lneighbours pre test inhib marking transs (Some sensitized_transs) ->
        IncrementAllChronos chronos sensitized_transs (Some updated_chronos) ->
        StpnFire lneighbours pre test inhib post marking updated_chronos transs priority_groups None -> 
        StpnCycle stpn None
  | StpnCycle_cons :
      forall (chronos : list (trans_type * option chrono_type))
             (places : list place_type)
             (transs : list trans_type)
             (pre post test inhib : weight_type)
             (marking : marking_type)
             (priority_groups : list (list trans_type))
             (lneighbours : list (trans_type * neighbours_type))
             (sensitized_transs : list trans_type)
             (updated_chronos : list (trans_type * option chrono_type))
             (fired_transitions : list trans_type)
             (nextm : marking_type)
             (next_chronos : list (trans_type * option chrono_type)),
        stpn = (mk_STPN
                  chronos
                  (mk_SPN places transs pre post test inhib marking priority_groups lneighbours)) ->
        ListSensitized lneighbours pre test inhib marking transs (Some sensitized_transs) ->
        IncrementAllChronos chronos sensitized_transs (Some updated_chronos) ->
        StpnFire lneighbours pre test inhib post marking updated_chronos transs priority_groups
                 (Some (fired_transitions, nextm, next_chronos)) -> 
        StpnCycle stpn (Some (fired_transitions,
                              (mk_STPN
                                 next_chronos
                                 (mk_SPN places transs pre post test inhib nextm priority_groups lneighbours)))).

  (*** Correctness proof : stpn_cycle ***)
  Theorem stpn_cycle_correct :
    forall (stpn : STPN)
           (opt_final_couple : option ((list trans_type) * STPN)),
      stpn_cycle stpn = opt_final_couple ->
      StpnCycle stpn opt_final_couple.
  Proof.
    intro stpn.
    functional induction (stpn_cycle stpn) using stpn_cycle_ind; intros.
    (* General case, all went well. *)
    - rewrite <- H; apply StpnCycle_cons with (chronos := chronos0)
                                              (marking := marking)
                                              (sensitized_transs := sensitized_transs)
                                              (updated_chronos := updated_chronos).
      + auto.
      + apply list_sensitized_correct; auto.
      + apply increment_all_chronos_correct; auto.
      + apply stpn_fire_correct; auto.
    (* Error case, stpn_fire returns None. *)
    - rewrite <- H; apply StpnCycle_fire_err with (places := places)
                                                  (transs := transs)
                                                  (pre := pre)
                                                  (post := post)
                                                  (test := test)
                                                  (inhib := inhib)
                                                  (priority_groups := priority_groups)
                                                  (lneighbours := lneighbours)
                                                  (chronos := chronos0)
                                                  (marking := marking)
                                                  (sensitized_transs := sensitized_transs)
                                                  (updated_chronos := updated_chronos).
      + auto.
      + apply list_sensitized_correct; auto.
      + apply increment_all_chronos_correct; auto.
      + apply stpn_fire_correct; auto.
    (* Error case, increment_all_chronos returns None. *)
    - rewrite <- H; apply StpnCycle_increment_chronos_err with (places := places)
                                                               (transs := transs)
                                                               (pre := pre)
                                                               (post := post)
                                                               (test := test)
                                                               (inhib := inhib)
                                                               (priority_groups := priority_groups)
                                                               (lneighbours := lneighbours)
                                                               (chronos := chronos0)
                                                               (marking := marking)
                                                               (sensitized_transs := sensitized_transs).
      + auto.
      + apply list_sensitized_correct; auto.
      + apply increment_all_chronos_correct; auto.
    (* Error case, list_sensitized returns None. *)
    - rewrite <- H; apply StpnCycle_list_sensitized_err with (places := places)
                                                               (transs := transs)
                                                               (pre := pre)
                                                               (post := post)
                                                               (test := test)
                                                               (inhib := inhib)
                                                               (priority_groups := priority_groups)
                                                               (lneighbours := lneighbours)
                                                               (chronos := chronos0)
                                                               (marking := marking).
      + auto.
      + apply list_sensitized_correct; auto.
  Qed.

  (*** Completeness proof : stpn_cycle ***)
  Theorem stpn_cycle_compl :
    forall (stpn : STPN)
           (opt_final_couple : option ((list trans_type) * STPN)),
      StpnCycle stpn opt_final_couple ->
      stpn_cycle stpn = opt_final_couple.
  Proof.
    intros; elim H; intros; unfold stpn_cycle; rewrite H0.
    (* Case StpnCycle_list_sensitized_err *)
    - apply list_sensitized_complete in H1; rewrite H1; auto.
    (* Case StpnCycle_increment_chronos_err *)
    - apply list_sensitized_complete in H1; rewrite H1.
      apply increment_all_chronos_complete in H2; rewrite H2; auto.
    (* Case StpnCycle_fire_err *)
    - apply list_sensitized_complete in H1; rewrite H1.
      apply increment_all_chronos_complete in H2; rewrite H2.
      apply stpn_fire_compl in H3; rewrite H3; auto.
    (* Case StpnCycle_cons *)
    - apply list_sensitized_complete in H1; rewrite H1.
      apply increment_all_chronos_complete in H2; rewrite H2.
      apply stpn_fire_compl in H3; rewrite H3; auto.
  Qed.

  (*  
   * Lemma : For all stpn with properties NoUnknownInPriorityGroups
   *         and NoUnknownTransInChronos then transitions
   *         in stpn.(priority_groups) are referenced in stpn.(chronos).
   *         
   *         Useful to apply stpn_fire_no_error while proving spn_cycle_no_error.
   *)
  Lemma priority_groups_in_chronos :
    forall (stpn : STPN),
      NoUnknownInPriorityGroups stpn ->
      NoUnknownTransInChronos stpn ->
      PriorityGroupsAreRefInChronos stpn.(priority_groups) stpn.(chronos).
  Proof.
    unfold NoUnknownInPriorityGroups.
    unfold NoUnknownTransInChronos.
    unfold PriorityGroupsAreRefInChronos.
    intros.
    generalize (in_concat t pgroup (priority_groups stpn) H2 H1); intro.
    rewrite <- H in H3.
    rewrite H0 in H3.
    auto.
  Qed.
  
  (*  
   * Theorem : For all stpn verifying the predicate IsWellStructuredStpn,
   *           stpn_cycle raises no error (alays returns Some value). 
   *)
  Theorem stpn_cycle_no_error :
    forall (stpn : STPN),
      IsWellStructuredStpn stpn ->
      exists v : ((list trans_type) * STPN),
        stpn_cycle stpn = Some v.
  Proof.
    unfold IsWellStructuredStpn; intro.
    functional induction (stpn_cycle stpn) using stpn_cycle_ind;
      set (stpn := {| chronos := chronos0;
                      spn := {| places := places;
                                transs := transs;
                                pre := pre;
                                post := post;
                                test := test;
                                inhib := inhib;
                                marking := marking;
                                priority_groups := priority_groups;
                                lneighbours := lneighbours |}
                   |});
      intros;
      unfold IsWellStructuredSpn in H;
      decompose [and] H; clear H.
    (* Case all went well, spn_fire returns Some value. *)
    - exists ((fired_transitions,
               {|
                 chronos := next_chronos;
                 spn := {|
                         places := places;
                         transs := transs;
                         pre := pre;
                         post := post;
                         test := test;
                         inhib := inhib;
                         marking := nextm;
                         priority_groups := priority_groups;
                         lneighbours := lneighbours |} |})).
      auto.            
    (* CASE stpn_fire returns None, impossible
     * regarding the hypotheses.
     *)
    - unfold NoUnknownTransInChronos in H0.
      unfold NoUnknownTransInLNeighbours in H8.
      (* Deduces the hypotheses needed to apply stpn_fire_no_error 
       * from the properties embedded in IsWellStructuredStpn.
       *)
      assert (H' : incl (SPN.transs stpn) (fst (split (chronos stpn))))
        by (rewrite H0; unfold incl; intros ; auto).
      assert (H'' : incl (SPN.transs stpn) (fst (split (SPN.lneighbours stpn))))
        by (rewrite H8; unfold incl; intros ; auto).
      generalize (priority_groups_in_chronos stpn H3 H0); intro.
      generalize (priority_groups_in_lneighbours stpn H3 H8); intro.
      generalize (pre_places_in_marking stpn H11 H7); intro.
      generalize (post_places_in_marking stpn H11 H7); intro.
      (* Then, ensures that chronos0 and updated_chronos have same structure. *)
      generalize (increment_all_chronos_same_struct
                    chronos0 sensitized_transs updated_chronos e2); intros.
      (* Rewrites chronos0 with updated_chronos in some hypotheses.  *)
      unfold ChronosHaveSameStruct in H14.
      simpl in H'.
      rewrite H14 in H'.
      simpl in H.
      unfold PriorityGroupsAreRefInChronos in H.
      rewrite H14 in H.
      (* Finally, applies lemma stpn_fire_no_error. *)
      generalize (stpn_fire_no_error
                    lneighbours pre test inhib post marking updated_chronos transs priority_groups
                    H' H'' H H10 H12 H13).
      intro; elim H15; intros.
      rewrite H16 in e3.
      inversion e3.
    (* CASE increment_all_chronos returns None, impossible
     * regarding the hypotheses. 
     *)
    - unfold NoUnknownTransInChronos in H0.
      generalize (list_sensitized_incl_transs
                    lneighbours pre test inhib marking transs sensitized_transs e1); intro.
      assert (H' : incl (SPN.transs stpn) (fst (split (chronos stpn))))
        by (rewrite H0; unfold incl; intros ; auto).
      generalize (incl_tran H H'); intro.
      generalize (increment_all_chronos_no_error
                    chronos0 sensitized_transs H10); intro.
      elim H12; intros.
      rewrite H13 in e2; inversion e2.
    (* CASE list_sensitized returns None, impossible
     * regarding the hypotheses. 
     *)
    - unfold NoUnknownTransInLNeighbours in H8.
      assert (H'' : incl (SPN.transs stpn) (fst (split (SPN.lneighbours stpn))))
        by (rewrite H8; unfold incl; intros ; auto).
      generalize (pre_places_in_marking stpn H11 H7); intro.
      unfold PlacesAreRefInMarking in H.
      generalize (list_sensitized_no_error
                    lneighbours pre test inhib marking transs
                    H'' H); intro.
      elim H10; intros; rewrite H12 in e1; inversion e1.
  Qed.

  (*  
   * Theorem : For all stpn verifying the property IsWellStructuredStpn,
   *           stpn_cycle returns a new stpn (next_stpn) verifying the relation
   *           IsWellStructuredStpn.
   *)
  Theorem stpn_cycle_well_structured :
    forall (stpn : STPN)
           (fired_transitions : list trans_type)
           (next_stpn : STPN),
      IsWellStructuredStpn stpn ->
      stpn_cycle stpn = Some (fired_transitions, next_stpn) ->
      IsWellStructuredStpn next_stpn.
  Proof.
    intro.
    functional induction (stpn_cycle stpn) using stpn_cycle_ind; intros.
    (* GENERAL CASE. *)
    - unfold IsWellStructuredStpn; unfold IsWellStructuredSpn.
      unfold IsWellStructuredStpn in H; unfold IsWellStructuredSpn in H.
      injection H0; clear H0; intros.
      unfold NoUnmarkedPlace in H.
      unfold NoUnknownTransInChronos in H.
      (*  
       * We need to ensure that stpn_fire preserves the structure
       * of marking and chronos.
       *)
      generalize (stpn_fire_same_struct_marking
                    lneighbours pre test inhib post
                    marking updated_chronos transs priority_groups
                    fired_transitions nextm next_chronos e3); intro.
      generalize (stpn_fire_same_struct_chronos
                    lneighbours pre test inhib post
                    marking updated_chronos transs priority_groups
                    fired_transitions nextm next_chronos e3); intro.
      generalize (increment_all_chronos_same_struct
                    chronos0 sensitized_transs updated_chronos e2); intro.
      (*  
       * Then, we need to rewrite chronos with updated_chronos, and
       * marking with nextm.
       *)
      unfold MarkingHaveSameStruct in H2;
        unfold ChronosHaveSameStruct in H3;
        unfold ChronosHaveSameStruct in H4.
      simpl in H.
      rewrite H2 in H.
      rewrite H4 in H.
      rewrite H3 in H.
      unfold NoUnknownTransInChronos;
        unfold NoUnmarkedPlace.
      rewrite <- H0.
      simpl.
      auto.
    (* CASE stpn_fire returns None. *)
    - inversion H0.
    (* CASE increment_all_chronos returns None. *)
    - inversion H0.
    (* CASE list_sensitized returns None. *)
    - inversion H0.
  Qed.
  
  (*******************************************)
  (******** ANIMATING DURING N CYCLES ********)
  (*******************************************)
  
  (*  
   * Function : Returns the list of (transitions_fired(i), marking(i), chronos(i))
   *            for each cycle i, from 0 to n, representing the evolution
   *            of the Petri net stpn.
   *)
  Fixpoint stpn_animate 
           (stpn : STPN)
           (n : nat)
           (stpn_evolution : list (list trans_type *
                                   marking_type *
                                   list (trans_type * option chrono_type))) :
    option (list (list trans_type * marking_type * list (trans_type * option chrono_type))) :=
    match n with
    (* Base case, returns the list storing the evolution. *)
    | O => Some stpn_evolution
    | S n' =>
      match (stpn_cycle stpn) with
      (* Adds a new evolution step at the end of the list. *)
      | Some (fired_trans_at_n, stpn_at_n) =>
        stpn_animate stpn_at_n n' (stpn_evolution ++ [(fired_trans_at_n,
                                                       (marking stpn_at_n),
                                                       (chronos stpn_at_n))])
      (* Error, stpn_cycle failed!!! *)
      | None => None
      end
    end.

  Functional Scheme stpn_animate_ind := Induction for stpn_animate Sort Prop.
  
  (*** Formal specification : stpn_animate ***)
  Inductive StpnAnimate (stpn : STPN) :
    nat ->
    list (list trans_type * marking_type * list (trans_type * option chrono_type)) ->
    option (list (list trans_type * marking_type * list (trans_type * option chrono_type))) ->
    Prop :=
  | StpnAnimate_0 :
      forall (stpn_evolution : list (list trans_type *
                                     marking_type *
                                     list (trans_type * option chrono_type))),
        StpnAnimate stpn 0 stpn_evolution (Some stpn_evolution) 
  | StpnAnimate_cons :
      forall (n : nat)
             (fired_trans_at_n : list trans_type)
             (stpn_at_n : STPN)
             (stpn_evolution : list (list trans_type *
                                     marking_type *
                                     list (trans_type * option chrono_type)))
             (opt_evolution : option (list (list trans_type *
                                            marking_type *
                                            list (trans_type * option chrono_type)))),
        StpnCycle stpn (Some (fired_trans_at_n, stpn_at_n)) ->
        StpnAnimate stpn_at_n
                    n
                    (stpn_evolution ++ [(fired_trans_at_n,
                                         (marking stpn_at_n),
                                         (chronos stpn_at_n))])
                    opt_evolution ->
        StpnAnimate stpn
                    (S n)
                    stpn_evolution
                    opt_evolution
  | StpnAnimate_err :
      forall (n : nat)
             (stpn_evolution : list (list trans_type *
                                     marking_type *
                                     list (trans_type * option chrono_type))),
        StpnCycle stpn None ->
        StpnAnimate stpn (S n) stpn_evolution None.
  
  (*** Correctness proof : stpn_animate***)
  Theorem stpn_animate_correct :
    forall (stpn :STPN)
           (n : nat)
           (stpn_evolution : list (list trans_type * marking_type * list (trans_type * option chrono_type)))
           (opt_evolution : option (list (list trans_type * marking_type * list (trans_type * option chrono_type)))),
      stpn_animate stpn n stpn_evolution = opt_evolution ->
      StpnAnimate stpn n stpn_evolution opt_evolution.
  Proof.                                                                                
    intros stpn n stpn_evolution.
    functional induction (stpn_animate stpn n stpn_evolution) using stpn_animate_ind; intros.
    (* Case n = 0 *)
    - rewrite <- H; apply StpnAnimate_0.
    (* General case *)
    - intros; rewrite <- H.
      apply StpnAnimate_cons with (fired_trans_at_n := fired_trans_at_n)
                                  (stpn_at_n := stpn_at_n).
      + apply stpn_cycle_correct in e0; auto.
      + apply IHo; auto.
    (* Error case, stpn_cycle returns None. *)
    - rewrite <- H; apply StpnAnimate_err.
      apply stpn_cycle_correct in e0; auto.
  Qed.

  (*** Completeness proof : stpn_animate ***)
  Theorem stpn_animate_compl :
    forall (stpn : STPN)
           (n : nat)
           (stpn_evolution : list (list trans_type *
                                   marking_type *
                                   list (trans_type * option chrono_type)))
           (opt_evolution : option (list (list trans_type *
                                          marking_type *
                                          list (trans_type * option chrono_type)))),
      StpnAnimate stpn n stpn_evolution opt_evolution ->
      stpn_animate stpn n stpn_evolution = opt_evolution.
  Proof.
    intros; elim H; intros.
    (* Case StpnAnimate_0 *)
    - simpl; auto.
    (* Case StpnAnimate_cons *)
    - simpl. apply stpn_cycle_compl in H0; rewrite H0.
      rewrite H2; auto.
    (* Case StpnAnimate_err *)
    - apply stpn_cycle_compl in H0.
      simpl.
      rewrite H0; auto.
  Qed.

  (*  
   * Theorem :  For all stpn verifying the property IsWellStructuredStpn,
   *            and for all number n of evolution cycles, stpn_animate returns no error.
   *)
  Theorem stpn_animate_no_error :
    forall (stpn : STPN)
           (n : nat),
      IsWellStructuredStpn stpn ->
      exists (v : list (list trans_type * marking_type * list (trans_type * option chrono_type))),
        stpn_animate stpn n [] = Some v.
  Proof.
    do 2 intro.
    functional induction (stpn_animate stpn n [])
               using stpn_animate_ind;
      intros.
    (* Base case, n = 0. *)
    - exists stpn_evolution; auto.
    (* General case. *)
    - apply IHo.
      apply (stpn_cycle_well_structured stpn fired_trans_at_n stpn_at_n H e0).
    (* Error case, impossible regarding the hypotheses. *)
    - generalize (stpn_cycle_no_error stpn H); intro.
      elim H0; intros.
      rewrite H1 in e0; inversion e0.
  Qed.

End AnimateStpn.
