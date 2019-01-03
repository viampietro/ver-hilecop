Require Export SPN.

(*========================================================*)
(*=== TYPES FOR GENERALIZED, EXTENDED, SYNCHRONOUS AND ===*)
(*=== TEMPORAL PETRI NETS.                             ===*)
(*========================================================*)

(* 
 * Defines the time interval structure associated with transitions.
 * Firing of transitions must happen when cnt >= min_t and cnt <= max_t.
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
 * Defines the structure of stpn. 
 * Basically, same structure as an spn with chronos associated to transitions.
 * (One chrono by transition)
 *
 *)
Structure STPN : Set :=
  mk_STPN {
      spn : SPN;
      chronos : list (trans_type * option chrono_type)       
    }.

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
           (t : trans_type)
           (chronos : list (trans_type * option chrono_type)) {struct chronos} :
    option (option chrono_type) :=
    match chronos with
    | (t', opt_chrono) :: tail => if t =? t' then
                                    Some opt_chrono
                                  else get_chrono t tail
    (* Case of error!!! *)
    | [] => None
    end.

    Functional Scheme get_chrono_ind := Induction for get_chrono Sort Prop. 

    (*** Formal specification : get_chrono ***)
    Inductive GetChrono (t : trans_type) :
      list (trans_type * option chrono_type) -> option (option chrono_type) -> Prop :=
    | GetChrono_err :
        GetChrono t [] None
    | GetChrono_hd_true :
        forall (chronos : list (trans_type * option chrono_type))
               (t' : trans_type)
               (opt_chrono : option chrono_type),
          t = t' ->
          GetChrono t ((t', opt_chrono) :: chronos) (Some opt_chrono)
    | GetChrono_hd_false :
        forall (chronos : list (trans_type * option chrono_type))
               (t' : trans_type)
               (opt_chrono : option chrono_type)
               (opt_opt_chrono : option (option chrono_type)),
          t <> t' ->
          GetChrono t chronos opt_opt_chrono ->
          GetChrono t ((t', opt_chrono) :: chronos) opt_opt_chrono.
          
    (*** Correctness proof : get_chrono ***)
    Theorem get_chrono_correct :
      forall (t : trans_type)
             (chronos : list (trans_type * option chrono_type))
             (opt_opt_chrono : option (option chrono_type)),
        get_chrono t chronos = opt_opt_chrono ->
        GetChrono t chronos opt_opt_chrono.
    Proof.
      intros t chronos.
      functional induction (get_chrono t chronos) using get_chrono_ind; intros.
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
      forall (t : trans_type)
             (chronos : list (trans_type * option chrono_type))
             (opt_opt_chrono : option (option chrono_type)),
        GetChrono t chronos opt_opt_chrono ->
        get_chrono t chronos = opt_opt_chrono.
    Proof.
      intros t chronos opt_opt_chrono H.
      induction H.
      (* Case GetChrono_err *)
      - simpl; auto.
      (* Case GetChrono_hd_true *)
      - simpl; apply Nat.eqb_eq in H; rewrite H; auto.
      (* Case GetChrono_hd_false *)
      - simpl; apply Nat.eqb_neq in H; rewrite H; auto.
    Qed.
    
    (* 
     * Function : Returns true if chrono and chrono' are equal.
     *            Two chronos are equal only if their max_is_infinite attribute
     *            values are the same.
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
      match get_chrono t chronos with
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
          GetChrono t chronos None ->
          IncrementChrono t chronos None
    | IncrementChrono_some :
        forall (chronos : list (trans_type * option chrono_type))
               (opt_chrono : option chrono_type)
               (cnt : nat)
               (min_t max_t : nat_star)
               (max_is_infinite : bool)
               (min_t_le_max_t : (int min_t) <= (int max_t))
               (final_chronos : list (trans_type * option chrono_type)),
          GetChrono t chronos (Some opt_chrono) ->
          opt_chrono = Some (mk_chrono cnt min_t max_t max_is_infinite min_t_le_max_t) ->
          ReplaceChrono (mk_chrono cnt min_t max_t max_is_infinite min_t_le_max_t)
                        (mk_chrono (cnt + 1) min_t max_t max_is_infinite min_t_le_max_t)
                        chronos
                        final_chronos ->
          IncrementChrono t chronos (Some final_chronos)
    | IncrementChrono_none :
        forall (chronos : list (trans_type * option chrono_type))
               (opt_chrono : option chrono_type),
          GetChrono t chronos (Some opt_chrono) ->
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
      - rewrite <- H; apply IncrementChrono_some with (opt_chrono := (Some {| cnt := cnt0;
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
    
    (*  
     * Function : Returns an option to a list of pair (trans, option chrono_type),
     *            where all chronos associated to transition in the list 
     *            sensitized_transs have been incremented.
     *            
     *            Raises an error (None value) if an incrementation
     *            went wrong for one of the transition of the list.
     * 
     *)
    Fixpoint increment_all_chronos
             (chronos : list (trans_type * option chrono_type))
             (sensitized_transs : list trans_type) :
      option (list (trans_type * option chrono_type)) :=
      match sensitized_transs with
      | t :: tail =>
        match increment_chrono t chronos with
        (* If increment_chrono returns Some new_chronos, 
         * then passes new_chronos as argument of recursive call.
         *)
        | Some new_chronos =>
          increment_all_chronos new_chronos tail
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
               (sensitized_transs : list trans_type)
               (new_chronos : list (trans_type * option chrono_type))
               (opt_final_chronos : option (list (trans_type * option chrono_type))),
          IncrementChrono t chronos (Some new_chronos) ->
          IncrementAllChronos new_chronos sensitized_transs opt_final_chronos ->  
          IncrementAllChronos chronos (t :: sensitized_transs) opt_final_chronos
    | IncrementAllChronos_err :
        forall (t : trans_type)
               (sensitized_transs : list trans_type),
          IncrementChrono t chronos None ->
          IncrementAllChronos chronos (t :: sensitized_transs) None.
    
    (*** Correctness proof : increment_all_chronos ***)
    Theorem increment_all_chronos_correct :
      forall (chronos : list (trans_type * option chrono_type))
             (sensitized_transs : list trans_type)
             (opt_final_chronos : option (list (trans_type * option chrono_type))),
        increment_all_chronos chronos sensitized_transs = opt_final_chronos ->
        IncrementAllChronos chronos sensitized_transs opt_final_chronos.
    Proof.
      intros chronos sensitized_transs.  
      functional induction (increment_all_chronos chronos sensitized_transs)
                 using  increment_all_chronos_ind; intros.
      (* Base case, sensitized_transs = [] *)
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
             (sensitized_transs : list trans_type)
             (opt_final_chronos : option (list (trans_type * option chrono_type))),
        IncrementAllChronos chronos sensitized_transs opt_final_chronos ->
        increment_all_chronos chronos sensitized_transs = opt_final_chronos.
    Proof.
      intros chronos sensitized_transs opt_final_chronos H; elim H; intros.
      (* IncrementAllChronos_nil *)
      - simpl; auto.
      (* IncrementAllChronos_cons *)
      - apply increment_chrono_complete in H0.
        unfold increment_all_chronos; rewrite H0; auto.
      (* IncrementAllChronos_err *)
      - apply increment_chrono_complete in H0.
        unfold increment_all_chronos; rewrite H0; auto.
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
      match get_chrono t chronos with
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
          GetChrono t chronos None ->
          ResetChrono t chronos None
    | ResetChrono_some :
        forall (chronos : list (trans_type * option chrono_type))
               (opt_chrono : option chrono_type)
               (cnt : nat)
               (min_t max_t : nat_star)
               (max_is_infinite : bool)
               (min_t_le_max_t : (int min_t) <= (int max_t))
               (final_chronos : list (trans_type * option chrono_type)),
          GetChrono t chronos (Some opt_chrono) ->
          opt_chrono = Some (mk_chrono cnt min_t max_t max_is_infinite min_t_le_max_t) ->
          ReplaceChrono (mk_chrono cnt min_t max_t max_is_infinite min_t_le_max_t)
                        (mk_chrono 0 min_t max_t max_is_infinite min_t_le_max_t)
                        chronos
                        final_chronos ->
          ResetChrono t chronos (Some final_chronos)
    | ResetChrono_none :
        forall (chronos : list (trans_type * option chrono_type))
               (opt_chrono : option chrono_type),
          GetChrono t chronos (Some opt_chrono) ->
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
      - rewrite <- H; apply ResetChrono_some with (opt_chrono := (Some {| cnt := cnt0;
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
     *            sensitized_transs have been set to zero.
     *            
     *            Raises an error (None value) if a reseting
     *            went wrong for one of the transition of the list.
     * 
     *)
    Fixpoint reset_all_chronos
             (chronos : list (trans_type * option chrono_type))
             (sensitized_transs : list trans_type) :
      option (list (trans_type * option chrono_type)) :=
      match sensitized_transs with
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
    Inductive ResetAllChronos
              (chronos : list (trans_type * option chrono_type)) :       
      list trans_type ->
      option (list (trans_type * option chrono_type)) ->
      Prop :=      
    | ResetAllChronos_nil :
        ResetAllChronos chronos [] (Some chronos)
    | ResetAllChronos_cons :
        forall (t : trans_type)
               (sensitized_transs : list trans_type)
               (new_chronos : list (trans_type * option chrono_type))
               (opt_final_chronos : option (list (trans_type * option chrono_type))),
          ResetChrono t chronos (Some new_chronos) ->
          ResetAllChronos new_chronos sensitized_transs opt_final_chronos ->  
          ResetAllChronos chronos (t :: sensitized_transs) opt_final_chronos
    | ResetAllChronos_err :
        forall (t : trans_type)
               (sensitized_transs : list trans_type),
          ResetChrono t chronos None ->
          ResetAllChronos chronos (t :: sensitized_transs) None.
    
    (*** Correctness proof : reset_all_chronos ***)
    Theorem reset_all_chronos_correct :
      forall (chronos : list (trans_type * option chrono_type))
             (sensitized_transs : list trans_type)
             (opt_final_chronos : option (list (trans_type * option chrono_type))),
        reset_all_chronos chronos sensitized_transs = opt_final_chronos ->
        ResetAllChronos chronos sensitized_transs opt_final_chronos.
    Proof.
      intros chronos sensitized_transs.  
      functional induction (reset_all_chronos chronos sensitized_transs)
                 using  reset_all_chronos_ind; intros.
      (* Base case, sensitized_transs = [] *)
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
             (sensitized_transs : list trans_type)
             (opt_final_chronos : option (list (trans_type * option chrono_type))),
        ResetAllChronos chronos sensitized_transs opt_final_chronos ->
        reset_all_chronos chronos sensitized_transs = opt_final_chronos.
    Proof.
      intros chronos sensitized_transs opt_final_chronos H; elim H; intros.
      (* ResetAllChronos_nil *)
      - simpl; auto.
      (* ResetAllChronos_cons *)
      - apply reset_chrono_complete in H0.
        unfold reset_all_chronos; rewrite H0; auto.
      (* ResetAllChronos_err *)
      - apply reset_chrono_complete in H0.
        unfold reset_all_chronos; rewrite H0; auto.
    Qed.

End Chrono.

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

Functional Scheme is_sensitized_ind :=
  Induction for is_sensitized Sort Prop.

(*** Formal specification : is_sensitized ***)
Inductive is_sensitized_spec
          (neighbours_t : neighbours_type)
          (pre test inhib : weight_type)
          (m : marking_type)
          (t : trans_type) : Prop :=
| is_sensitized_cons :   
    check_pre_or_test_spec (pre t) m (pre_pl neighbours_t) 
    /\ check_pre_or_test_spec (test t) m (test_pl neighbours_t)
    /\ check_inhib_spec (inhib t) m (inhib_pl neighbours_t) ->
    is_sensitized_spec neighbours_t pre test inhib m t.

(*** Correctness proof : is_sensitized ***)
Theorem is_sensitized_correct :
  forall (neighbours_t : neighbours_type)
         (pre test inhib : weight_type)
         (m : marking_type)
         (t : trans_type),
  is_sensitized neighbours_t pre test inhib m t = true ->
  is_sensitized_spec neighbours_t pre test inhib m t.
Proof.
  intros neighbours_t pre test inhib m t;
  functional induction (is_sensitized neighbours_t pre test inhib m t)
             using is_sensitized_ind;
  intros.
  apply is_sensitized_cons.
  do 2 (apply andb_true_iff in H; elim H;  clear H; intros).
  split.
  - apply check_pre_or_test_correct; auto.
  - split; [apply check_pre_or_test_correct; auto | apply check_inhib_correct; auto].
Qed.

(*** Completeness proof : is_sensitized ***)
Theorem is_sensitized_complete :
  forall (neighbours_t : neighbours_type)
         (pre test inhib : weight_type)
         (m : marking_type)
         (t : trans_type),
  is_sensitized_spec neighbours_t pre test inhib m t ->
  is_sensitized neighbours_t pre test inhib m t = true.
Proof.
  intros places pre test inhib m_steady t H. elim H.
  intro.
  elim H0; intros; clear H0.
  elim H2; intros; clear H2.
  unfold is_sensitized.
  apply andb_true_iff. split.
  apply andb_true_iff. split.
  - apply check_pre_or_test_compl in H1; auto.
  - apply check_pre_or_test_compl in H0; auto.
  - apply check_inhib_compl in H3; auto.
Qed.

Lemma not_is_sensitized_iff :
  forall (neighbours_t : neighbours_type)
         (pre test inhib : weight_type)
         (m : marking_type)
         (t : trans_type),
  ~is_sensitized_spec neighbours_t pre test inhib m t <->
  is_sensitized neighbours_t pre test inhib m t = false.
Proof.
  intros. rewrite <- not_true_iff_false. apply not_iff_compat. split.
  - intro; apply is_sensitized_complete; auto.
  -intro; apply is_sensitized_correct; auto.
Qed.

(* Useless fonction for SPN but useful for 
 *
 * -  _asynchronous_ Petri nets
 * -  STPN (and SITPN by extension) 
 *
 * Needed to list the sensitized transitions :
 *
 * 1) to increment time counter for these transitions, 
 *    at the beginning of the cycle
 *    
 *)

(*  
 * Function :  Returns the list of sensitized transitions
 *             contained in sometranss.
 *)
Fixpoint list_sensitized_aux 
         (lneighbours : list neighbours_type)
         (pre test inhib : weight_type) 
         (m : marking_type)
         (sensitized_transs : list trans_type)
         (sometranss : list trans_type) : list trans_type :=
  match sometranss with
  | [] => sensitized_transs 
  | (tr i) :: tail =>
    (* Checks if tr i has neighbours *)
    match (get_neighbours lneighbours i) with
    (* If no neighbours, (tr i) is an isolated trans
     * and cannot be sensitized anyway. *)
    | None => list_sensitized_aux lneighbours pre test inhib m sensitized_transs tail
    | Some neighbours_t => if (is_sensitized neighbours_t pre test inhib m (tr i)) then
                             list_sensitized_aux lneighbours pre test inhib m ((tr i) :: sensitized_transs) tail   
                           else
                             list_sensitized_aux lneighbours pre test inhib m sensitized_transs tail
    end
  end.

(*** Formal specification : list_sensitized_aux ***)
Inductive list_sensitized_aux_spec
          (lneighbours : list neighbours_type)
          (pre test inhib : weight_type) 
          (m : marking_type)
          (sensitized_transs_rec : list trans_type) :
  list trans_type -> (* sometranss *)
  list trans_type -> (* sensitized_transs *)
  Prop :=

| list_sensitized_aux_nil :
    list_sensitized_aux_spec lneighbours pre test inhib m sensitized_transs_rec []
                             sensitized_transs_rec      
| list_sensitized_aux_none :
    forall (transs sensitized_transs : list trans_type)
           (i : nat),
    get_neighbours_spec lneighbours i None ->
    list_sensitized_aux_spec lneighbours pre test inhib m sensitized_transs_rec transs
                             sensitized_transs ->
    list_sensitized_aux_spec lneighbours pre test inhib m sensitized_transs_rec ((tr i) :: transs)
                             sensitized_transs      
| list_sensitized_aux_if :
    forall (transs sensitized_transs : list trans_type)
           (i : nat)
           (neighbours_t : neighbours_type),
    get_neighbours_spec lneighbours i (Some neighbours_t) ->
    is_sensitized_spec neighbours_t pre test inhib m (tr i) ->
    list_sensitized_aux_spec lneighbours pre test inhib m ((tr i) :: sensitized_transs_rec) transs
                             sensitized_transs ->
    list_sensitized_aux_spec lneighbours pre test inhib m sensitized_transs_rec ((tr i) :: transs)
                             sensitized_transs
| list_sensitized_aux_else :
    forall (transs sensitized_transs : list trans_type)
           (i : nat)
           (neighbours_t : neighbours_type),
    get_neighbours_spec lneighbours i (Some neighbours_t) ->
    ~is_sensitized_spec neighbours_t pre test inhib m (tr i) ->
    list_sensitized_aux_spec lneighbours pre test inhib m sensitized_transs_rec transs
                             sensitized_transs ->
    list_sensitized_aux_spec lneighbours pre test inhib m sensitized_transs_rec ((tr i) :: transs)
                             sensitized_transs.
    
Functional Scheme list_sensitized_aux_ind :=
  Induction for list_sensitized_aux Sort Prop.

(*** Correctness proof : list_sensitized_aux ***)
Theorem list_sensitized_aux_correct :
  forall (sometranss sensitized_transs_rec sensitized_transs : list trans_type)
         (lneighbours : list neighbours_type)
         (pre test inhib : weight_type)
         (m : marking_type),
  list_sensitized_aux lneighbours pre test inhib m
                      sensitized_transs_rec sometranss = sensitized_transs ->
  list_sensitized_aux_spec lneighbours pre test inhib m
                           sensitized_transs_rec sometranss sensitized_transs.
Proof.
  intros sometranss sensitized_transs_rec sensitized_transs
         lneighbours pre test inhib m.
  functional induction (list_sensitized_aux lneighbours pre test inhib m
                                            sensitized_transs_rec sometranss)
             using list_sensitized_aux_ind.
  (* Case sometranss = [] *)
  - intro Heq. rewrite Heq. apply list_sensitized_aux_nil.
  (* Case is_sensitized = true *)
  - intro Htail. apply list_sensitized_aux_if with (neighbours_t := neighbours_t).
    + apply get_neighbours_correct; auto.
    + apply is_sensitized_correct; auto.
    + apply (IHl Htail).
  (* Case is_sensitized = false *)
  - intro Htail. apply list_sensitized_aux_else with (neighbours_t := neighbours_t).
    + apply get_neighbours_correct; auto.
    + apply not_is_sensitized_iff; auto. 
    + apply (IHl Htail).
  (* Case get_neighbours = None *)
  - intro; apply list_sensitized_aux_none;
      [apply get_neighbours_correct; auto | apply IHl; auto].
Qed.

(*** Completeness proof : list_sensitized_aux ***)
Theorem list_sensitized_aux_complete :
  forall (sometranss sensitized_transs_rec sensitized_transs : list trans_type)
         (lneighbours : list neighbours_type)
         (pre test inhib : weight_type)
         (m : marking_type),
  list_sensitized_aux_spec lneighbours pre test inhib m
                           sensitized_transs_rec sometranss sensitized_transs  ->
  list_sensitized_aux lneighbours pre test inhib  m
                      sensitized_transs_rec sometranss = sensitized_transs.
Proof.
  intros sometranss sensitized_transs_rec sensitized_transs
         lneighbours pre test inhib m Hspec.
  elim Hspec.
  (* Case list_sensitized_aux_nil *)
  - simpl; auto.
  (* Case list_sensitized_aux_none *)
  - intros sensitized_transs_rec0 tail sensitized_transs0 i Hspectail Htail Hsensitized.
    simpl;
      apply get_neighbours_compl in Hspectail;
      rewrite Hspectail;
      rewrite Hsensitized; auto.
  (* Case list_sensitized_aux_if *)
  - intros sensitized_transs_rec0 tail sensitized_transs0 i neighbours_t; intros.
    simpl;
      apply get_neighbours_compl in H;
      rewrite H;
      apply is_sensitized_complete in H0;
      rewrite H0;
      rewrite H2; auto.
  (* Case list_sensitized_aux_else *)
  - intros sensitized_transs_rec0 tail sensitized_transs0 i neighbours_t; intros.
    simpl.
    apply get_neighbours_compl in H; rewrite H.
    apply not_is_sensitized_iff in H0; rewrite H0; auto.    
Qed.

(*
 * Function : Wrapper around list_sensitized_aux.
 *)
Definition list_sensitized 
           (sometranss : list trans_type)
           (lneighbours : list neighbours_type)
           (pre test inhib : weight_type) 
           (m : marking_type) : list trans_type :=
  list_sensitized_aux lneighbours pre test inhib m [] sometranss.

(*** Formal specification : list_sensitized ***)
Inductive list_sensitized_spec
          (sometranss : list trans_type)
          (lneighbours : list neighbours_type)
          (pre test inhib : weight_type) 
          (m : marking_type) : list trans_type -> Prop :=
| list_sensitized_mk :
    forall (sensitized_transs : list trans_type),
    list_sensitized_aux_spec lneighbours pre test inhib m [] sometranss sensitized_transs ->
    list_sensitized_spec sometranss lneighbours pre test inhib m sensitized_transs.

Functional Scheme list_sensitized_ind :=
  Induction for list_sensitized Sort Prop.

(*** Correctness proof : list_sensitized ***)
Theorem list_sensitized_correct :
  forall (sometranss sensitized : list trans_type)
         (lneighbours : list neighbours_type)
         (pre test inhib : weight_type)
         (m : marking_type),
  list_sensitized sometranss lneighbours pre test inhib m = sensitized ->
  list_sensitized_spec sometranss lneighbours pre test inhib m sensitized.
Proof.
  intros sometranss sensitized lneighbours pre test inhib m.
  functional induction (list_sensitized sometranss lneighbours pre test inhib m)
             using list_sensitized_ind.
  intro H.
  apply list_sensitized_mk.
  apply list_sensitized_aux_correct; auto.  
Qed.

(*** Completeness proof : list_sensitized ***)
Theorem list_sensitized_complete : forall
    (sometranss  sensitized : list trans_type)
    (lneighbours : list place_type)
    (pre   test  inhib : weight_type)
    (m : marking_type),
    list_sensitized_spec
      sometranss  lneighbours    pre   test  inhib
      m   sensitized     ->
    list_sensitized
      sometranss  lneighbours    pre   test  inhib
      m      =   sensitized.
Proof.
  intros  sometranss  sensitized lneighbours pre test inhib m H.
  elim H. intros sensitized_transs H0. simpl. unfold list_sensitized.
  rewrite H0. reflexivity. 
Qed.

(*
 * Function : Returns the list of the currently sensitized
 *            transitions contained in spn.
 *)
Definition list_sensitized_spn (spn : SPN) : list trans_type :=
  match spn with
  | (mk_SPN places transs pre post test inhib marking (mk_prior Lol)) =>
    (list_sensitized transs places pre test inhib marking)   
  end.

(*** Formal specification : list_sensitized_spn ***)
Inductive list_sensitized_spn_spec (spn : SPN) : list trans_type -> Prop :=
| list_sensitized_spn_mk :
    forall (Lol: list (list trans_type))
           (m : marking_type)
           (places : list place_type)
           (transs : list trans_type)
           (pre  post test inhib : weight_type)
           (sensitized_transs : list trans_type),
    spn = (mk_SPN places transs pre post test inhib m (mk_prior Lol)) ->
    list_sensitized transs places pre test inhib m = sensitized_transs ->
    list_sensitized_spn_spec spn sensitized_transs.

Functional Scheme list_sensitized_spn_ind :=
  Induction for list_sensitized_spn Sort Prop.

(*** Correctness proof : list_sensitized_spn ***)
Theorem list_sensitized_spn_correct : forall
    (spn : SPN) (sensitized : list trans_type),
    list_sensitized_spn       spn = sensitized        ->
    list_sensitized_spn_spec  spn   sensitized.
Proof.
  intros spn  sensitized.
  functional induction (list_sensitized_spn
                          spn)
             using list_sensitized_spn_ind.
  intro H. apply list_sensitized_spn_mk with
               (Lol := _x0) (m := marking)
               (places := places) (transs := transs)
               (pre:=pre) (post:=_x) (test:=test) (inhib:=inhib).
  + reflexivity.
  + assumption.   
Qed.

(*** Comlpeteness proof : list_sensitized_spn ***)
Theorem list_sensitized_spn_complete :
  forall (spn : SPN) (sensitized : list trans_type),
  list_sensitized_spn_spec spn sensitized -> 
  list_sensitized_spn spn = sensitized.
Proof.
  intros spn  sensitized Hspec. elim Hspec.
  intros Lol m places transs  pre post test inhib
         sensitized_transs Hspn Hsensitized.
  unfold list_sensitized_spn. rewrite Hspn. assumption. 
Qed.

(*
 * Function : Returns the list of currently sensitized
 *            transitions contained in stpn.
 *            Wrapper function around list_sensitized_spn.
 *)
Definition list_sensitized_stpn (stpn : STPN) : list trans_type :=
  match stpn with
  | mk_STPN spn chronos => list_sensitized_spn spn
  end.

(*** Formal specification : list_sensitized_stpn ***)
Inductive list_sensitized_stpn_spec (stpn : STPN) : list trans_type -> Prop :=
| list_sensitized_stpn_mk :
    forall (spn : SPN)
           (sensitized_transs : list trans_type)
           (chronos : trans_type -> option chrono_type),
    stpn = mk_STPN spn chronos ->
    list_sensitized_spn spn = sensitized_transs ->
    list_sensitized_stpn_spec stpn sensitized_transs.

Functional Scheme list_sensitized_stpn_ind :=
  Induction for list_sensitized_stpn Sort Prop.

(*** Correctness proof : list_sensitized_stpn ***)
Theorem list_sensitized_stpn_correct :  forall
    (stpn : STPN) (sensitized : list trans_type),
    list_sensitized_stpn stpn = sensitized ->
    list_sensitized_stpn_spec stpn sensitized.
Proof.
  intros stpn  sensitized.
  functional induction (list_sensitized_stpn stpn) using list_sensitized_stpn_ind.
  intro H. apply list_sensitized_stpn_mk with (spn := spn0) (chronos := _x).
  + reflexivity.
  + assumption.   
Qed.

(*** Completeness proof : list_sensitized_stpn ***)
Theorem list_sensitized_stpn_complete :
  forall (stpn : STPN) (sensitized : list trans_type),
  list_sensitized_stpn_spec stpn sensitized -> 
  list_sensitized_stpn stpn = sensitized.
Proof.
  intros stpn  sensitized H. elim H.
  intros. unfold list_sensitized_stpn. rewrite H0. rewrite H1.
  reflexivity. 
Qed.

(* 
 * Function : Returns the list of disabled (unsensitized)
 *            transitions contained in sometranss according
 *            to the marking (m_steady, m_decreasing) and 
 *            the weight functions (pre, test and inhib).
 *)
Fixpoint list_disabled_aux 
         (places : list place_type)
         (pre test inhib : weight_type) 
         (m_steady m_decreasing : marking_type)
         (disabled_transs : list trans_type)
         (sometranss : list trans_type) : list trans_type :=
  match sometranss with
  | [] => disabled_transs 
  | t :: tail => if (check_all_edges places (pre t) (test t) (inhib t) m_steady m_decreasing)
                 then list_disabled_aux places pre test inhib m_steady m_decreasing
                                        disabled_transs tail 
                 else list_disabled_aux places pre test inhib m_steady m_decreasing
                                        (t :: disabled_transs) tail   
  end.

(*** Formal specification : list_disabled_aux ***)
Inductive list_disabled_aux_spec
          (places : list place_type)
          (pre test inhib : weight_type) 
          (m_steady m_decreasing : marking_type)
          (disabled_transs : list trans_type)
  : list trans_type  ->   (* sometranss *)
    list trans_type  ->   (* DISabled_transs *)
    Prop :=
| list_disabled_aux_nil :
    list_disabled_aux_spec
      places     pre    test    inhib  m_steady   m_decreasing
      disabled_transs      []         disabled_transs
| list_disabled_aux_cons_if :  forall
    (tail  any_transs : list trans_type)
    (t : trans_type),
    list_disabled_aux_spec 
      places     pre   test   inhib     m_steady   m_decreasing
      disabled_transs     tail       any_transs
    ->
     check_all_edges
       places  (pre t) (test t) (inhib t) m_steady  m_decreasing
     = true 
    ->
    list_disabled_aux_spec  
      places     pre   test   inhib      m_steady   m_decreasing
      disabled_transs   (t::tail)   any_transs
| list_disabled_aux_cons_else :  forall
    (tail   any_transs  : list trans_type)
    (t : trans_type),
    list_disabled_aux_spec 
      places     pre   test   inhib  
      m_steady   m_decreasing   (t::disabled_transs)
      tail       any_transs
    ->
     check_all_edges
       places  (pre t) (test t) (inhib t) m_steady  m_decreasing
     = false
    ->
    list_disabled_aux_spec  
      places     pre   test   inhib  
      m_steady   m_decreasing   disabled_transs
      (t::tail)  any_transs.

Functional Scheme list_disabled_aux_ind :=
  Induction for list_disabled_aux Sort Prop.

(*** Correctness proof : list_disabled_aux ***)
Theorem list_disabled_aux_correct :  forall
    (sometranss  disab_rec  disabled_transs: list trans_type)
    (places : list place_type)
    (pre   test  inhib : weight_type)
    (m_steady  m_decreasing : marking_type),
    list_disabled_aux 
      places   pre   test   inhib  m_steady   m_decreasing
      disab_rec   sometranss    = disabled_transs
    ->
    list_disabled_aux_spec 
      places    pre   test  inhib  m_steady   m_decreasing
      disab_rec   sometranss      disabled_transs.
Proof.
  intros sometranss  disab_rec disabled_transs
         places   pre   test   inhib  
         m_steady   m_decreasing.
  functional induction (list_disabled_aux
                          places   pre   test  inhib
                          m_steady   m_decreasing
                          disab_rec  sometranss)
             using list_disabled_aux_ind.
  - intro Heq. rewrite Heq. apply list_disabled_aux_nil.
  - intro Htail. apply list_disabled_aux_cons_if.
    + apply (IHl Htail).
    + assumption.
  - intro Htail. apply list_disabled_aux_cons_else.
    + apply (IHl Htail).
    + assumption.   
Qed.

(*** Completeness proof : list_disabled_aux ***)
Theorem list_disabled_aux_complete :  forall
    (sometranss  disab_rec  disabled_transs: list trans_type)
    (places : list place_type)
    (pre   test  inhib : weight_type)
    (m_steady  m_decreasing : marking_type),
    list_disabled_aux_spec 
      places   pre   test   inhib  m_steady   m_decreasing
      disab_rec    sometranss       disabled_transs
    ->
    list_disabled_aux 
      places   pre   test   inhib  m_steady   m_decreasing
      disab_rec    sometranss     = disabled_transs.  
Proof.
  intros sometranss  disab_rec disabled_transs
         places   pre   test   inhib  
         m_steady   m_decreasing  Hspec. elim Hspec.
  - intro  disab_rec0. simpl. reflexivity.
  - intros disabled_transs0 tail any_transs t
           Hspectail Htail  Hsynchro.
    simpl. rewrite Hsynchro. assumption.
  - intros disabled_transs0 tail any_transs t
           Hspectail Htail  Hnotsynchro.
    simpl. rewrite Hnotsynchro. assumption. 
Qed.

(**************************************************************)
(**************************************************************)

(*  
 * Function : Wrapper function around list_disabled_aux
 *            with the disabled_transs parameter initialized
 *            to zero.
 *)
Definition list_disabled 
           (sometranss : list trans_type)
           (places : list place_type)
           (pre test inhib : weight_type) 
           (m_steady m_decreasing : marking_type) : list trans_type :=
  list_disabled_aux places pre test inhib m_steady m_decreasing [] sometranss.

(*** Formal specification : list_disabled ***)
Inductive list_disabled_spec
           (sometranss : list trans_type)
           (places : list place_type)
           (pre    test    inhib : weight_type) 
           (m_steady   m_decreasing : marking_type)
  : list trans_type  ->  Prop  :=
| list_disabled_mk : forall
    (sensitized_transs : list trans_type),
    list_disabled_aux 
      places   pre  test  inhib  m_steady  m_decreasing  []
      sometranss
    = sensitized_transs
    ->
    list_disabled_spec
      sometranss    places    pre    test   inhib
      m_steady      m_decreasing      sensitized_transs.

Functional Scheme list_disabled_ind :=
  Induction for list_disabled Sort Prop.

(*** Correctness proof : list_disabled ***)
Theorem list_disabled_correct :  forall
    (places : list place_type)
    (pre   test  inhib : weight_type)
    (m_steady   m_decreasing : marking_type)
    (some_transs  sensitized_transs  : list trans_type),
    list_disabled 
      some_transs    places   pre    test    inhib
      m_steady    m_decreasing  =  sensitized_transs
    ->
    list_disabled_spec
      some_transs   places    pre    test    inhib
      m_steady    m_decreasing     sensitized_transs.
Proof.
  intros places  pre    test    inhib
      m_steady    m_decreasing   some_transs  sensitized_transs.
  functional induction (list_disabled
                          some_transs places pre test inhib
                          m_steady m_decreasing)
             using list_disabled_ind.
  intro H. apply list_disabled_mk. assumption.   
Qed.

(*** Completeness proof : list_disabled ***)
Theorem list_disabled_complete : forall
    (places : list place_type)
    (pre   test  inhib : weight_type)
    (m_steady   m_decreasing : marking_type)
    (some_transs  sensitized_transs  : list trans_type),
    list_disabled_spec
      some_transs   places    pre    test    inhib
      m_steady    m_decreasing     sensitized_transs
    ->
    list_disabled 
      some_transs   places    pre    test    inhib
      m_steady    m_decreasing  =  sensitized_transs.
Proof.
  intros places  pre    test    inhib
         m_steady  m_decreasing   some_transs  sensitized_transs H.
  elim H.
  intros sensitized_transs0 Hnotsynchro.
  unfold list_disabled. rewrite Hnotsynchro. reflexivity.
Qed.


(*****************************************************
 ********** FIRING ALGORITHM for STPN ****************
 *****************************************************)

(*
 * Function : Given 1 ordered class of transitions 
 *            in structural conflict (a list class_transs), 
 *            returns a 3-uplet composed of a list of transitions 
 *            "fired_pre_class" (the transitions that have been pre-fired), 
 *            a marking, obtained after the update of the tokens in the pre-condition 
 *            places of the fired_pre_class's transitions, 
 *            and a new chrono function (of type trans_type -> option chrono_type).
 * 
 * Param whole_class : Steady class of transitions. We need it to reset
 *                     the chronos, in a global way, for all the transitions disabled
 *                     by the firing of some transition t, which belongs
 *                     to the class being processed.
 *                      
 *)
Fixpoint stpn_class_fire_pre_aux
         (whole_class : list trans_type)
         (places : list place_type)
         (pre test inhib : weight_type) 
         (m_steady : marking_type)
         (class_transs fired_pre_class : list trans_type)
         (m_decreasing : marking_type) 
         (chronos : trans_type -> option chrono_type) :
  (list trans_type) * marking_type * (trans_type -> option chrono_type) :=

  match class_transs with
  | t :: tail =>
    (* t is sensitized, even w.r.t. to the others *)
    if (check_all_edges places (pre t) (test t) (inhib t) m_steady m_decreasing)
       && (check_chrono (chronos t)) then
      (* (Half-)Fires t by updating the marking in its pre-condition places *)
      let new_decreasing := (update_marking_pre t pre m_decreasing places) in
      
      (* Resets the time counters of all transitions that have been
       * disabled after the firing of t, along with transition t's chrono! 
       *)
      let new_chronos := (reset_all_chronos0 (reset_chrono0 chronos t)    
                                             (list_disabled whole_class
                                                            places
                                                            pre
                                                            test
                                                            inhib
                                                            m_steady
                                                            new_decreasing)) in
      (* Adds t to the fired_pre_class list, and continue
       * with a new marking and a new "chronos".
       *)
      (stpn_class_fire_pre_aux whole_class places pre test inhib m_steady tail
                               (fired_pre_class ++ [t]) new_decreasing new_chronos)
        
    (* not sensitized  w.r.t. the other transs OR not goog time *)
    else (stpn_class_fire_pre_aux whole_class places pre test inhib m_steady tail
                                  fired_pre_class m_decreasing chronos)
           
  | []  => (fired_pre_class, m_decreasing, chronos)
  end.

(* 
 * There are 3 parallel calculus in this function : 
 * 1) pumping tokens to get "m_intermediate"  (half fired)
 * 2) returning subclass of transitions (half fired)
 * 3) resting local counters of any "sensitized transition no more sensitized". 
 * and 2 markings are recorded : 
 *    1) the initial one to check with inhib and test arcs
 *    2) a floating (decreasing) intermediate marking to check classic arcs
 *)

(*** Formal specification : stpn_class_fire_pre_aux ***)
Inductive stpn_class_fire_pre_aux_spec
          (whole_class : list trans_type)
          (places : list place_type)
          (pre test inhib : weight_type)  
          (m_steady : marking_type) :
  (list trans_type)                  -> (* class *)
  (list trans_type)                  -> (* subclass_fired_pre *)
  marking_type                       -> (* m_decreasing *)
  (trans_type -> option chrono_type) -> (* chronos *)      
  (list trans_type)                  -> (* subclass_fired_pre *)
  marking_type                       -> (* m_decreasing *)
  (trans_type -> option chrono_type) -> (* chronos *)
  Prop :=
(* Case class is nil *)
| class_nil :
    forall (m_decreased : marking_type)
           (subclass_fired_pre : list trans_type)
           (chronos : trans_type -> option chrono_type),
      (stpn_class_fire_pre_aux_spec
         whole_class places pre test inhib m_steady [] subclass_fired_pre
         m_decreased chronos subclass_fired_pre m_decreased chronos)
(* Case t is sensitized and has a right chrono *)
| class_cons_if :
    forall (t : trans_type)
           (tail subclass_fired_pre sub : list trans_type)
           (m_decreasing_low m_decreasing_high m : marking_type)
           (chronos new_chronos final_chronos : trans_type -> option chrono_type),
    check_all_edges places (pre t) (test t) (inhib t) m_steady m_decreasing_high = true /\
    check_chrono (chronos t) = true -> 
    m_decreasing_low = (update_marking_pre t pre m_decreasing_high places) ->
    new_chronos = (reset_all_chronos0
                     (reset_chrono0 chronos t)
                     (list_disabled whole_class places pre
                                    test inhib m_steady m_decreasing_low)) ->    
    (stpn_class_fire_pre_aux_spec
       whole_class places pre test inhib m_steady tail (subclass_fired_pre ++ [t])
       m_decreasing_low new_chronos sub m final_chronos) ->
    (stpn_class_fire_pre_aux_spec
       whole_class places pre test inhib m_steady (t :: tail) subclass_fired_pre
       m_decreasing_high chronos sub m final_chronos)
(* Case t is disabled or hasn't the right chrono *)
| class_cons_else :
    forall (t : trans_type)
           (tail subclass_half_fired sub : list trans_type)
           (m_decreasing m : marking_type)
           (chronos final_chronos : trans_type -> option chrono_type),
   check_all_edges places (pre t) (test t) (inhib t) m_steady m_decreasing = false \/
   check_chrono (chronos t) = false ->
   (stpn_class_fire_pre_aux_spec
      whole_class places pre test inhib m_steady tail subclass_half_fired
      m_decreasing chronos sub m final_chronos) ->
   (stpn_class_fire_pre_aux_spec
      whole_class places pre test inhib m_steady (t::tail) subclass_half_fired
      m_decreasing chronos
      sub m final_chronos).

Functional Scheme stpn_class_fire_pre_aux_ind :=
  Induction for stpn_class_fire_pre_aux Sort Prop.

(*** Correctness proof : stpn_class_fire_pre_aux ***)
Theorem stpn_class_fire_pre_aux_correct : forall
    (whole_class : list trans_type)
    (places : list place_type)
    (pre test inhib : weight_type)
    (m_steady m_decreasing m_final : marking_type)
    (class_transs  fired_pre_class  sub_final : list trans_type)
    (chronos final_chronos : trans_type -> option chrono_type),
    stpn_class_fire_pre_aux
      whole_class     places    pre   test   inhib  m_steady
      class_transs
      fired_pre_class   m_decreasing    chronos  
    = (sub_final,          m_final,        final_chronos)
    -> 
    stpn_class_fire_pre_aux_spec
      whole_class     places     pre   test  inhib  m_steady
      class_transs
      fired_pre_class   m_decreasing    chronos
      sub_final            m_final         final_chronos.
Proof.
  intros whole_class  places  pre test inhib  m_steady
         m_decreasing  m_final
         class_transs   fired_pre_class    sub_final
         chronos  final_chronos.
  functional induction 
             (stpn_class_fire_pre_aux
                whole_class places  pre test inhib  m_steady   
                class_transs
                fired_pre_class  m_decreasing    chronos)
             using stpn_class_fire_pre_aux_ind.
  - intro H. inversion H. apply class_nil.
  - intro H.
    apply class_cons_if
      with (m_decreasing_low := (update_marking_pre
                                   t pre m_decreasing  places ))
           (new_chronos :=
              (reset_all_chronos0
                 (reset_chrono0 chronos t)    (* ! reset de t *)
                 (list_disabled
                    whole_class   places     pre    test    inhib
                    m_steady    (update_marking_pre
                                   t pre m_decreasing  places)))).
    + apply andb_prop. assumption. 
    + reflexivity.
    + reflexivity.
    + apply (IHp H).      
  - intro H. apply class_cons_else.
    + apply andb_false_iff. assumption. 
    + apply (IHp H).
Qed.

(*** Completeness proof : stpn_class_fire_pre_aux ***)
Theorem stpn_class_fire_pre_aux_complete :  forall
    (whole_class : list trans_type)
    (places : list place_type)
    (pre  test  inhib : weight_type)
    (m_steady   m_decreasing     m_final : marking_type)
    (class_transs  subclass_fired_pre  sub_final : list trans_type)
    (chronos final_chronos : trans_type -> option chrono_type),
    stpn_class_fire_pre_aux_spec
      whole_class      places     pre test inhib   m_steady
      class_transs
      subclass_fired_pre    m_decreasing        chronos
      sub_final             m_final             final_chronos
    ->
    stpn_class_fire_pre_aux
      whole_class      places     pre test inhib   m_steady
      class_transs
      subclass_fired_pre    m_decreasing    chronos 
    = (sub_final ,          m_final,        final_chronos).
Proof.
  intros whole_class places pre test inhib m_steady
         m_decreasing m_final class_transs fired_pre_class
         sub_final  chronos final_chronos Hspec. elim Hspec.
  - simpl. reflexivity.
  - intros  t tail fired_pre_class0 sub
            m_decreasing_low m_decreasing_high m
            chronos0 new_chronos  final_chronos0
            Hsynchro  Hlow Hnew  Htailspec Htail.
    simpl.
    assert (Hsynchro' : check_all_edges
                          places (pre t) (test t) 
                          (inhib t) m_steady m_decreasing_high &&
                          check_chrono (chronos0 t) = true).
      { apply andb_true_iff. assumption. }  rewrite Hsynchro'.
      rewrite <- Hlow. rewrite <- Hnew. rewrite Htail.
      reflexivity.
  - intros  t tail fired_pre_class0 sub
            m_decreasing0  m
            chronos0   final_chronos0
            Hsynchro   Htailspec Htail. simpl.
    assert (Hsynchro' : check_all_edges
                          places (pre t) (test t) 
                          (inhib t) m_steady m_decreasing0 &&
                          check_chrono (chronos0 t) = false).
      { apply andb_false_iff. assumption. } 
    rewrite Hsynchro'. rewrite Htail.  reflexivity. 
Qed.

(*   
 * Function : Wrapper around the stpn_class_fire_pre function.
 * 
 *)
Definition stpn_class_fire_pre
           (places : list place_type)
           (pre test inhib : weight_type) 
           (m_steady : marking_type)
           (class_transs : list trans_type)
           (m_decreasing : marking_type) 
           (chronos : trans_type -> option chrono_type) :
  (list trans_type) * marking_type * (trans_type -> option chrono_type) :=
  (stpn_class_fire_pre_aux class_transs places pre test inhib m_steady
                           class_transs [] m_decreasing chronos).

(*** Formal specification : stpn_class_fire_pre ***)
Inductive stpn_class_fire_pre_spec
          (places : list place_type)
          (pre test inhib : weight_type)  
          (m_steady : marking_type)
          (class_transs : list trans_type)
          (m_decreasing : marking_type)
          (chronos : trans_type -> option chrono_type) :
    (list trans_type)                     ->
    marking_type                          ->
    (trans_type -> option chrono_type)    ->
    Prop :=
| stpn_sub_fire_pre_mk :
    forall (fired_pre_class : list trans_type)
           (m_fired_pre_class : marking_type)
           (final_chronos: trans_type -> option chrono_type),
      stpn_class_fire_pre_aux
        class_transs     places    pre    test    inhib m_steady
        class_transs     []
        m_decreasing     chronos
      = (fired_pre_class, m_fired_pre_class, final_chronos)
      ->
      stpn_class_fire_pre_spec
        places          pre  test  inhib        m_steady
        class_transs
        m_decreasing        chronos
        fired_pre_class  m_fired_pre_class  final_chronos.

Functional Scheme stpn_class_fire_pre_ind :=
  Induction for stpn_class_fire_pre Sort Prop.

(*** Correctness proof : stpn_class_fire_pre ***)
Theorem stpn_class_fire_pre_correct :
  forall (places : list place_type)
         (pre  test  inhib : weight_type)
         (m_steady   m_decreasing     m_decreased : marking_type)
         (class_transs    fired_pre_class  : list trans_type)
         (chronos final_chronos: trans_type -> option chrono_type),
    stpn_class_fire_pre
      places    pre    test    inhib     m_steady
      class_transs
      m_decreasing         chronos     
    = (fired_pre_class, m_decreased, final_chronos)
    ->
    stpn_class_fire_pre_spec
      places          pre  test  inhib    m_steady
      class_transs
      m_decreasing        chronos 
      fired_pre_class  m_decreased  final_chronos.
Proof.
  intros places pre test inhib m_steady m_decreasing m_decreased
         class_transs  fired_pre_class chronos final_chronos H.
  functional induction (stpn_class_fire_pre
                          places    pre test inhib  m_steady
                          class_transs
                          m_decreasing   chronos)
             using stpn_class_fire_pre_ind.
  apply stpn_sub_fire_pre_mk. assumption.
Qed. 

(*** Completeness proof : stpn_class_fire_pre ***)
Theorem stpn_class_fire_pre_complete : forall
    (places : list place_type)
    (pre  test  inhib : weight_type)
    (m_steady   m_decreasing     m_decreased : marking_type)
    (class_transs     subclass_fired_pre  : list trans_type)
    (chronos final_chronos: trans_type -> option chrono_type),
    stpn_class_fire_pre_spec
      places          pre  test  inhib     m_steady
      class_transs
      m_decreasing        chronos 
      subclass_fired_pre  m_decreased  final_chronos
    -> 
    stpn_class_fire_pre
      places    pre    test    inhib       m_steady
      class_transs
      m_decreasing         chronos
    = (subclass_fired_pre, m_decreased, final_chronos).
Proof.
  intros  places pre test inhib m_steady m_decreasing m_decreased
          class_transs  fired_pre_class chronos final_chronos H.
  elim H.
  intros. unfold stpn_class_fire_pre. assumption.
Qed.

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


(**************************************************************)
(*********************  stpn_fire_pre *************************)
(**************************************************************)

(* 
 * Function : Applies stpn_class_fire_pre over ALL classes of transitions.
 *            Begins with initial marking, end with half fired marking. 
 *            "fired_pre_classes" is meant to be empty at first 
 *)
Fixpoint stpn_fire_pre_aux
         (places : list place_type)
         (pre test inhib : weight_type)
         (m_steady : marking_type)
         (classes fired_pre_classes : list (list trans_type))
         (m_decreasing : marking_type)
         (chronos : trans_type -> option chrono_type) :
  (list (list trans_type)) * marking_type * (trans_type -> option chrono_type)  :=
  match classes with
  | [] => (fired_pre_classes, m_decreasing, chronos)
  | class :: Ltail => let '(sub_l, new_m, new_chronos) :=
                          stpn_class_fire_pre places pre test inhib m_steady
                                              class m_decreasing chronos
                      in  stpn_fire_pre_aux places pre test inhib m_steady
                                            Ltail (sub_l :: fired_pre_classes) new_m new_chronos        
  end.

(*** Formal specification : stpn_fire_pre_aux ***)
Inductive stpn_fire_pre_aux_spec
          (places : list place_type)
          (pre test inhib : weight_type)
          (m_steady  : marking_type)
  : list (list trans_type)               ->  (* classes   *)
    list (list trans_type)               ->  (* fired_pre_classes *)
    marking_type                         ->  (* m_decreasing *)
    (trans_type -> option chrono_type)     ->     (* chronos *)

    list (list trans_type)          ->  (* fired_pre_classes *)
    marking_type                       ->  (* m_decreasing *)
    (trans_type -> option chrono_type)     ->     (* chronos *)
    Prop :=
| classes_nil : forall (fired_pre_classes : list (list trans_type))
                       (m_decreased : marking_type)
                       (chronos : trans_type -> option chrono_type),
    stpn_fire_pre_aux_spec
      places           pre   test  inhib   m_steady
      []
      fired_pre_classes    m_decreased          chronos 
      fired_pre_classes    m_decreased          chronos
| classes_cons : forall
    (classes_tail classes_fired_pre_tail C : list (list trans_type))
    (class     class_fired_pre : list trans_type)
    (m_decreased   m_decreasing  m_any  : marking_type)
    (chronos   chronos_fin  any_chronos : trans_type ->
                                            option chrono_type),
    stpn_class_fire_pre
      places          pre    test    inhib    m_steady
      class
                        m_decreasing chronos
    = (class_fired_pre, m_decreased, chronos_fin)
    ->
    stpn_fire_pre_aux_spec
      places          pre    test    inhib    m_steady
      classes_tail
      (class_fired_pre::
                      classes_fired_pre_tail) m_decreased chronos_fin
      C     m_any    any_chronos
    ->
    stpn_fire_pre_aux_spec
      places          pre   test   inhib   m_steady
      (class::
            classes_tail)
      classes_fired_pre_tail   m_decreasing    chronos
      C                        m_any          any_chronos.

Functional Scheme stpn_fire_pre_aux_ind :=
  Induction for stpn_fire_pre_aux Sort Prop.

(*** Correctness proof : stpn_fire_pre_aux ***)
Theorem stpn_fire_pre_aux_correct : forall
    (places : list place_type)
    (pre   test  inhib : weight_type)
    (m_steady  m_decreasing  m_decreased : marking_type)
    (classes_transs   fired_pre_classes_rec
                      fired_pre_classes : list (list trans_type))
    (chronos   final_chronos  : trans_type -> option chrono_type),
    stpn_fire_pre_aux
      places       pre   test  inhib  m_steady
      classes_transs
      fired_pre_classes_rec  m_decreasing  chronos    
    = (fired_pre_classes,    m_decreased,  final_chronos)
    ->
    stpn_fire_pre_aux_spec
      places       pre   test  inhib  m_steady
      classes_transs
      fired_pre_classes_rec  m_decreasing   chronos
      fired_pre_classes      m_decreased    final_chronos.
Proof.
  intros places  pre test inhib m_steady m_decreasing m_decreased
         classes_transs  fired_pre_classes_rec   fired_pre_classes
         chronos final_chronos.
  functional induction
             (stpn_fire_pre_aux
                places pre test inhib m_steady
                classes_transs
                fired_pre_classes_rec  m_decreasing   chronos)
             using stpn_fire_pre_aux_ind.
  - intro Heq. inversion Heq. apply classes_nil.
  - intro H.
    apply classes_cons
      with (class_fired_pre :=
              fst_tuplet (stpn_class_fire_pre
                            places pre test inhib m_steady
                            class m_decreasing  chronos))
           (m_decreased :=
              snd_tuplet (stpn_class_fire_pre
                            places    pre   test   inhib   m_steady
                            class
                            m_decreasing  chronos))
           (chronos_fin :=
              trd_tuplet (stpn_class_fire_pre
                            places pre test inhib  m_steady
                            class
                            m_decreasing  chronos)).
    + rewrite e0. simpl. reflexivity.
    + rewrite e0. simpl.  apply (IHp H).
Qed.

(*** Completeness proof : stpn_fire_pre_aux ***)
Theorem stpn_fire_pre_aux_complete : forall
    (places : list place_type)
    (pre   test  inhib : weight_type)
    (m_steady  m_decreasing  m_decreased : marking_type)
    (classes_transs   classes_fired_pre_rec
                      classes_fired_pre : list (list trans_type))
    (chronos   final_chronos  : trans_type -> option chrono_type),
    stpn_fire_pre_aux_spec
      places          pre   test   inhib  m_steady
      classes_transs
      classes_fired_pre_rec  m_decreasing   chronos   
      classes_fired_pre      m_decreased    final_chronos
    ->
    stpn_fire_pre_aux
      places          pre   test  inhib   m_steady
      classes_transs
      classes_fired_pre_rec  m_decreasing   chronos
    = (classes_fired_pre,    m_decreased,   final_chronos).    
Proof.
  intros  places pre test inhib  m_steady m_decreasing m_decreased
          classes_transs classes_fired_pre_rec  classes_fired_pre 
          chronos  final_chronos  H. elim H.
  - intros. simpl. reflexivity.
  - intros classes_tail classes_fired_pre_tail
           C  class  class_fired_pre
           m_decreased0   m_decreasing0    m_any
           chronos0     chronos_fin     any_chronos
           Heq   Hspectail   Htail.
    simpl. rewrite Heq. rewrite <- Htail. reflexivity. 
Qed.

(*
 * Function : Wrapper around the stpn_fire_pre_aux function.
 *            Initializes 
 *)
Definition stpn_fire_pre
         (places : list place_type)
         (pre test inhib : weight_type)
         (m_steady : marking_type)
         (classes_transs : list (list trans_type))
         (chronos : trans_type -> option chrono_type) :
  (list (list trans_type)) * marking_type * (trans_type -> option chrono_type) :=
  stpn_fire_pre_aux places pre test inhib m_steady classes_transs [] m_steady chronos.

(*** Formal specification : stpn_fire_pre ***)
Inductive stpn_fire_pre_spec
         (places : list place_type)
         (pre test inhib : weight_type)
         (m_steady : marking_type)
         (classes_transs  : list (list trans_type))
         (chronos : trans_type -> option chrono_type) :
  (list (list trans_type)) ->
  marking_type ->
  (trans_type -> option chrono_type)   ->
  Prop :=
| spn_fire_pre_mk :
    forall (classes_fired_pre : list (list trans_type))
           (m_inter : marking_type)
           (chronos_next  : trans_type ->   option chrono_type),
      stpn_fire_pre_aux
        places      pre    test    inhib  m_steady
        classes_transs
        []                 m_steady   chronos
      = (classes_fired_pre, m_inter,  chronos_next)
      ->
      stpn_fire_pre_spec
        places      pre     test   inhib   m_steady
        classes_transs                 chronos
        classes_fired_pre   m_inter    chronos_next.

Functional Scheme stpn_fire_pre_ind :=
  Induction for stpn_fire_pre   Sort Prop.

(*** Correctness proof : stpn_fire_pre ***)
Theorem stpn_fire_pre_correct :  forall
    (places : list place_type)
    (pre   test  inhib : weight_type)
    (m_steady  m_decreased : marking_type)
    (classes_transs  classes_fired_pre : list (list trans_type))
    (chronos   final_chronos  : trans_type -> option chrono_type),
    stpn_fire_pre
      places       pre   test  inhib  m_steady            
      classes_transs                   chronos
    = (classes_fired_pre, m_decreased, final_chronos)
    ->
    stpn_fire_pre_spec
      places       pre   test  inhib  m_steady            
      classes_transs                    chronos
      classes_fired_pre    m_decreased   final_chronos.
Proof.
  intros places  pre test inhib m_steady m_decreased
         classes_transs classes_fired_pre
         chronos final_chronos.
  functional induction (stpn_fire_pre
                          places pre test inhib  m_steady
                          classes_transs   chronos)
             using stpn_fire_pre_ind.
  apply spn_fire_pre_mk. 
Qed.

(*** Completeness proof : stpn_fire_pre ***)
Theorem stpn_fire_pre_complete : forall
    (places : list place_type)
    (pre   test  inhib : weight_type)
    (m_steady  m_decreased : marking_type)
    (classes_transs  classes_fired_pre : list (list trans_type))
    (chronos   final_chronos  : trans_type -> option chrono_type),
    stpn_fire_pre_spec
      places       pre   test   inhib  m_steady            
      classes_transs                     chronos
      classes_fired_pre    m_decreased   final_chronos
    ->
    stpn_fire_pre
      places        pre   test  inhib  m_steady            
      classes_transs                   chronos
    = (classes_fired_pre, m_decreased, final_chronos).
Proof.
  intros  places pre test  inhib m_steady
          m_decreased classes_transs classes_fired_pre
          chronos  final_chronos H. elim H.
  intros  classes_fired_pre0 m_inter chronos_next  Heq.
  unfold stpn_fire_pre. assumption.
Qed.

(***************************************************)
(*********** For DEBUGGING only .. *****************)
(***************************************************)

(*  
 * Function : Returns the tuplet resulting of the call
 *            to stpn_fire_pre.
 *            Marking and chronos are presented in a
 *            pretty printed manner.
 *            
 *)
Definition stpn_print_fire_pre
           (places : list place_type)
           (transs : list trans_type)
           (pre test inhib : weight_type)
           (marking : marking_type)
           (chronos : trans_type -> option chrono_type)
           (classes_transs : list (list trans_type)) :
  (list (list trans_type)) *
  list (place_type * nat) *
  list (trans_type * option (nat * nat * nat)) (* chronos *) :=
  let '(sub_Lol, m_inter, new_chronos ) :=
      (stpn_fire_pre places pre test inhib marking classes_transs chronos)
  in (sub_Lol, marking2list m_inter places, intervals2list new_chronos transs).

(*  
 * Function : Wrapper around the stpn_print_fire_pre function.
 *)
Definition stpn_debug2 (stpn : STPN) :
  (list (list trans_type)) *
  (list (place_type * nat))  *
  (list (trans_type * option (nat * nat * nat)))  :=
  match stpn with
  | mk_STPN
      (mk_SPN places transs pre test inhib post marking (mk_prior Lol))
      chronos =>
    (stpn_print_fire_pre places transs pre test inhib marking chronos Lol)
  end.


(* 
 * Function : Returns a tuplet (transitions fired (at this cycle), 
 *                              final marking, 
 *                              final chronos). 
 *)
Definition stpn_fire  
           (places : list place_type)
           (pre test inhib post : weight_type)
           (m_steady : marking_type)
           (classes_transs : list (list trans_type))
           (chronos : trans_type -> option chrono_type) :
  (list (list trans_type)) * marking_type * (trans_type -> option chrono_type) :=
  
  let '(sub_Lol, m_inter, new_chronos) :=
      (stpn_fire_pre places pre test inhib m_steady classes_transs chronos)
  (* fire_post already done in SPN.v
   * The way of updating the marking according to post-conditions
   * doesn't change from SPN to STPN.
   *)  
  in  (sub_Lol, (fire_post places post m_inter sub_Lol), new_chronos).

(*** Formal specification : stpn_fire ***)
Inductive stpn_fire_spec   
          (places : list place_type)
          (pre test inhib post : weight_type)
          (m_steady : marking_type)
          (classes_transs : list (list trans_type))
          (chronos : trans_type -> option chrono_type) :
  (list (list trans_type)) ->
  marking_type               ->
  (trans_type -> option chrono_type)    ->
  Prop :=
| stpn_fire_mk :  forall
    (sub_Lol : list (list trans_type))
    (m_inter   m  : marking_type)
    (new_chronos : trans_type -> option chrono_type),
    (sub_Lol, m_inter, new_chronos) = stpn_fire_pre
                                        places pre test inhib m_steady
                                        classes_transs chronos
    ->
    m = fire_post
          places post   m_inter  sub_Lol
    ->
    stpn_fire_spec   
      places         pre test inhib post      m_steady
      classes_transs   chronos
      sub_Lol    m   new_chronos.

Functional Scheme stpn_fire_ind :=
  Induction for  stpn_fire   Sort Prop.

(*** Correctness proof : stpn_fire ***)
Theorem stpn_fire_correct : forall
    (places : list place_type)
    (pre test inhib post : weight_type)
    (m_steady  m_next: marking_type)
    (chronos  next_chronos : trans_type -> option chrono_type)
    (classes_transs   sub_Lol: list (list trans_type)),
    stpn_fire
      places   pre  test  inhib  post  m_steady
      classes_transs      chronos  
    =  (sub_Lol, m_next, next_chronos)
    ->
    stpn_fire_spec
      places   pre  test  inhib  post   m_steady
      classes_transs      chronos
      sub_Lol  m_next next_chronos.
Proof.
  intros places  pre  test  inhib  post  m_steady  m_next
         chronos  next_chronos classes_transs sub_Lol.
  functional induction (stpn_fire
                          places pre test inhib post  m_steady
                          classes_transs  chronos)
             using stpn_fire_ind.
  intro Heq. inversion Heq. 
  apply stpn_fire_mk with (m_inter := m_inter).
  - rewrite e. rewrite H0. rewrite H2.  reflexivity.
  - reflexivity.  
Qed.

(*** Completeness proof : stpn_fire ***)
Theorem stpn_fire_complete : forall
    (places : list place_type)
    (pre test inhib post : weight_type)
    (m_steady  m_next: marking_type)
    (chronos  next_chronos : trans_type -> option chrono_type)
    (classes_transs   sub_Lol: list (list trans_type)),
    stpn_fire_spec
      places   pre  test  inhib  post   m_steady
      classes_transs     chronos  
      sub_Lol  m_next next_chronos
    ->
    stpn_fire
      places   pre  test  inhib  post   m_steady
      classes_transs     chronos
    =  (sub_Lol, m_next, next_chronos).
Proof.
  intros places pre test inhib post  m_steady  m_next chronos
         next_chronos  classes_transs sub_Lol H. elim H.
  intros sub_Lol0  m_inter  m  new_chronos  Hpre   Hpost.
  unfold stpn_fire. rewrite <- Hpre. rewrite Hpost. reflexivity.
Qed.

(* The marking and the chronos are evolving,  
but we want to see also the fired transitions *)
(******************************* CYCLE **********************)

(*  
 * Function : Returns the resulting Petri net after all the sensitized
 *            transitions - with right chrono value - in stpn have been fired, and 
 *            returns the list of lists containing these transitions.
 *            
 *)
Definition stpn_cycle (stpn : STPN) : (list (list trans_type)) * STPN  :=
  match stpn with
  | mk_STPN
      (mk_SPN places transs pre post test inhib marking (mk_prior Lol))
      chronos =>
    (* Lists sensitized transitions in the underlying spn,
     * chronos are not taken into account yet. *)
    let sensitized := list_sensitized_spn
                        (mk_SPN places transs pre post test inhib marking (mk_prior Lol)) in
    (* Increments all chronos for the sensistized trnasitions *)
    let chronos_incr := increment_all_chronos chronos sensitized in

    (* Fires the sensitized transitions, now taking chronos into account. *)
    let '(transs_fired, next_m, next_chronos) :=
        (stpn_fire places pre test inhib post marking Lol chronos_incr) in

    (transs_fired, mk_STPN
                     (mk_SPN places transs pre post test inhib next_m (mk_prior Lol))
                     next_chronos)

  end.

(*** Formal specification : stpn_cycle ***)
Inductive stpn_cycle_spec (stpn : STPN) :
  list (list trans_type) -> STPN -> Prop :=
| stpn_fired_mk :
    forall
      (sub_Lol  Lol: list (list trans_type))
      (next_m   m : marking_type)
      (spn : SPN)
      (next_stpn : STPN)
      (places : list place_type)
      (transs  sensitized : list trans_type)
      (pre  post test inhib : weight_type)
      (chronos  chronos_incr next_chronos : trans_type -> option chrono_type),
    spn = mk_SPN places transs pre post test inhib m (mk_prior Lol) ->
    stpn = mk_STPN spn chronos ->
    sensitized = list_sensitized_spn spn ->
    chronos_incr = increment_all_chronos chronos sensitized -> 
    (sub_Lol, next_m, next_chronos) = (stpn_fire places pre test inhib post m Lol chronos_incr) ->
    next_stpn = mk_STPN
                  (mk_SPN places transs pre post test inhib next_m (mk_prior Lol))
                  next_chronos -> 
    stpn_cycle_spec stpn sub_Lol next_stpn.

Functional Scheme stpn_cycle_ind :=
  Induction for stpn_cycle   Sort Prop.

(*** Correctness proof : stpn_cycle ***)
Theorem stpn_cycle_correct :
  forall (stpn  next_stpn : STPN)
         (sub_Lol : list (list trans_type)),
    stpn_cycle
      stpn    =  (sub_Lol, next_stpn)
    ->
    stpn_cycle_spec
      stpn        sub_Lol  next_stpn.
Proof.
  intros  stpn  next_stpn  sub_Lol.
  functional induction (stpn_cycle stpn)
             using stpn_cycle_ind. 
  intro Heq. apply stpn_fired_mk
               with (Lol:=Lol) (next_m:=next_m) (m:=marking)
                 (places:=places) (transs:=transs)
                 (pre:=pre) (post:=post) (test:=test)
                 (inhib:=inhib) (chronos:=chronos)
                 (spn := {|
                          places := places;
                          transs := transs;
                          pre := pre;
                          post := post;
                          test := test;
                          inhib := inhib;
                          marking := marking;
                          priority :=
                            {| Lol := Lol |} |})
                 (stpn := {|
                           spn := {|
                                   places := places;
                                   transs := transs;
                                   pre := pre;
                                   post := post;
                                   test := test;
                                   inhib := inhib;
                                   marking := marking;
                                   priority :=
                                     {| Lol := Lol |} |} ;
                           all_chronos := chronos |})
                                 
                 (sensitized := list_sensitized_spn
                               {|
                                 places := places;
                                 transs := transs;
                                 pre := pre;
                                 post := post;
                                 test := test;
                                 inhib := inhib;
                                 marking := marking;
                                 priority :=
                                   {| Lol := Lol |} |})    
                 (chronos_incr := increment_all_chronos
                                    chronos
                                    (list_sensitized_spn
                                       {|
                                         places := places;
                                         transs := transs;
                                         pre := pre;
                                         post := post;
                                         test := test;
                                         inhib := inhib;
                                         marking := marking;
                                         priority :=
                                           {| Lol := Lol |} |}))
                 (next_chronos :=
                    trd_tuplet (stpn_fire
                                  places  pre  test  inhib  post marking
                                  Lol (increment_all_chronos
                                         chronos
                                         (list_sensitized_spn
                                            {|
                                              places := places;
                                              transs := transs;
                                              pre := pre;
                                              post := post;
                                              test := test;
                                              inhib := inhib;
                                              marking := marking;
                                              priority :=
                                                {| Lol := Lol |} |}))
                 )).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite e2. inversion Heq. simpl. reflexivity.
  - rewrite e2. simpl. inversion Heq. reflexivity.
Qed.

(*** Completeness proof : stpn_cycle ***)
Theorem stpn_cycle_complete :
 forall (stpn  next_stpn : STPN)
        (sub_Lol : list (list trans_type)),
   stpn_cycle_spec
     stpn         sub_Lol  next_stpn
   ->
   stpn_cycle
      stpn    =  (sub_Lol, next_stpn).
Proof.
  intros  stpn next_stpn sub_Lol  H. elim H.
  intros sub_Lol0  Lol next_m  m  spn0 next_stpn0
         places  transs  sensitized  pre post test  inhib 
         chronos    chronos_incr    next_chronos
         H0 H1 H2 H3 H4 H5.
  unfold stpn_cycle.
  rewrite  H1. rewrite H0. simpl.
  unfold list_sensitized_spn in H2. rewrite H0 in H2. rewrite <- H2.
  rewrite <- H3. rewrite <- H4. rewrite H5. reflexivity. 
Qed.

(***************************************************)
(*************** To animate a STPN *****************)
(***************************************************)

(*  
 * Function : Returns the list of (transitions_fired(i), marking(i), chronos(i))
 *            for each cycle i, from 0 to n, representing the evolution
 *            of the Petri net stpn.
 *)
Fixpoint stpn_animate (stpn : STPN) (n : nat) :
  list
    (list (list trans_type)  *
     list (place_type * nat) *
     (list (trans_type * option (nat * nat * nat)))) :=
  match n with
  | O => [ ( [] , [] , []  ) ]
  | S n' =>  let (Lol_fired, next_stpn) := (stpn_cycle stpn) in
             (Lol_fired,
              (marking2list (marking (spn next_stpn)) (places (spn next_stpn))),
              (intervals2list (all_chronos next_stpn) (transs (spn next_stpn))))
               :: (stpn_animate next_stpn n')
  end.    

(*** Formal specification : stpn_animate ***)
Inductive stpn_animate_spec
          (stpn : STPN)
  : nat ->
    list
      (list (list trans_type)  *
       list (place_type * nat) *
       (list (trans_type * option (nat * nat * nat)))) -> Prop :=
| animate_stpn_O : stpn_animate_spec
                    stpn   O  [ ( [] , [] , [] ) ]
| animate_stpn_S :
    forall (next_stpn : STPN)
           (Lol_fired : list (list trans_type))
           (m_visuel : list (place_type * nat))
           (chronos_visuels : list (trans_type * option (nat * nat * nat)))
           (n : nat)
           (TAIL : list (list (list trans_type) *
                         list (place_type * nat) *
                         (list (trans_type * option (nat * nat * nat))))),
     
      (Lol_fired, next_stpn) = stpn_cycle stpn
      ->
      m_visuel = marking2list
                   (marking (spn next_stpn))
                   (places (spn next_stpn))
      ->
      chronos_visuels = (intervals2list
                           (all_chronos   next_stpn)
                           (transs (spn  next_stpn)))
      ->
      stpn_animate_spec
        next_stpn    n    TAIL
      -> 
      stpn_animate_spec
        stpn   (S n)   ((Lol_fired, m_visuel, chronos_visuels) :: TAIL).

Functional Scheme stpn_animate_ind :=
  Induction for stpn_animate Sort Prop.

(*** Correctness proof : stpn_animate ***)
Theorem stpn_animate_correct :
  forall (stpn : STPN)
         (n : nat)
         (triplets : list (list (list trans_type)  *
                           list (place_type * nat) *
                           list (trans_type * option (nat * nat * nat)))),
  stpn_animate stpn n = triplets -> stpn_animate_spec stpn n triplets.
Proof.
  intros stpn n.
  functional induction (stpn_animate stpn n)
             using stpn_animate_ind.
  - intros truc H. rewrite <- H. apply animate_stpn_O.
  - intros truc H. rewrite <- H.
    apply animate_stpn_S with (next_stpn := snd (stpn_cycle stpn)).
    + rewrite e0. simpl. reflexivity.
    + rewrite e0. simpl. reflexivity.
    + rewrite e0. simpl. reflexivity. 
    + rewrite e0. simpl. apply (IHl (stpn_animate next_stpn n')). reflexivity.
Qed.

(*** Completeness proof : stpn_animate ***)
Theorem stpn_animate_complete :
  forall (stpn : STPN)
         (n : nat)
         (triplets : list (list (list trans_type)  *
                           list (place_type * nat) *
                           list (trans_type * option (nat * nat * nat)))),
  stpn_animate_spec stpn n triplets -> stpn_animate stpn n = triplets.
Proof.
  intros. elim H.
  - simpl. reflexivity. 
  - intros. simpl.
    rewrite <- H0. rewrite <- H1. rewrite <- H2. rewrite <- H4.
    reflexivity.
Qed.

