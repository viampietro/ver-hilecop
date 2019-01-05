Require Import spn_examples.

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
 * STPN is declared as a coercion of SPN.
 *)
Structure STPN : Set :=
  mk_STPN {
      chronos : list (trans_type * option chrono_type);
      spn :> SPN
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
      stpn_fire lneighbours pre test inhib post m chronos transs priority_groups = opt_final_tuplet ->
      StpnFire lneighbours pre test inhib post m chronos transs priority_groups opt_final_tuplet.
  Proof.
    intros lneighbours pre test inhib post m chronos transs priority_groups.
    functional induction (stpn_fire lneighbours pre test inhib post m chronos transs priority_groups)
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
    - rewrite <- H; apply StpnFire_fire_post_err with (pre_fired_transitions := pre_fired_transitions)
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
    - rewrite <- H; apply StpnFire_reset_chronos_err2 with (pre_fired_transitions := pre_fired_transitions)
                                                           (intermediatem := intermediatem)
                                                           (updated_chronos := updated_chronos)
                                                           (disabled_transs := disabled_transs).
      + apply stpn_map_fire_pre_correct in e; auto.
      + apply reset_all_chronos_correct in e1; auto.
      + apply list_disabled_correct in e2; auto.
      + apply reset_all_chronos_correct in e3; auto.
    (* Error case, list_disabled returns None. *)
    - rewrite <- H; apply StpnFire_list_disabled_err with (pre_fired_transitions := pre_fired_transitions)
                                                          (intermediatem := intermediatem)
                                                          (updated_chronos := updated_chronos).
      + apply stpn_map_fire_pre_correct in e; auto.
      + apply reset_all_chronos_correct in e1; auto.
      + apply list_disabled_correct in e2; auto.
    (* Error case, 1st reset_all_chronos returns None. *)
    - rewrite <- H; apply StpnFire_reset_chronos_err1 with (pre_fired_transitions := pre_fired_transitions)
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
    | O => Some stpn_evolution
    | S n' => match (stpn_cycle stpn) with
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

End AnimateStpn.