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

(*===============================================*)
(*============ PROPERTIES ON STPN ===============*)
(*===============================================*)

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
