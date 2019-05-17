(* Import Spn and Stpn types, and predicates. *)

Require Import Hilecop.Spn.Spn.
Require Import Hilecop.Stpn.Stpn.

(* Import functions from Spn token player. *)

Require Import Hilecop.Spn.SpnTokenPlayer.

(*===================================================*)
(*=============== CHRONO SECTION  ===================*)
(*===================================================*)

Section Chrono.

  (** Returns true if chrono doesn't exist,
      or if the associated cnt is greater than or equal
      to min_t and less than or equal to max_t.
      
      Returns false otherwise. *)
  
  Definition check_chrono (opt_chrono : option Chrono) : bool :=
    match opt_chrono with
    | None => true
    | Some (mk_chrono cnt min_t max_t) =>
      match max_t with
      (* If upper bound is infinite, tests only the lower bound *)
      | pos_inf => int min_t <=? cnt
      | pos_val max_val =>
        (int min_t <=? cnt) && (cnt <=? int max_val)
      end
    end.
  
  (** Returns the chrono associated to transition t 
      if t is referenced in the chronos list.
      
      Raises an error (None value) otherwise. *)
  
  Fixpoint get_chrono
           (chronos : list (Trans * option Chrono))
           (t : Trans) {struct chronos} :
    option (option Chrono) :=
    match chronos with
    | (t', opt_chrono) :: tail => if t =? t' then
                                    Some opt_chrono
                                  else get_chrono tail t
    (* Case of error!!! *)
    | [] => None
    end.

  Functional Scheme get_chrono_ind := Induction for get_chrono Sort Prop. 

  (** If [get_chrono] returns Some [opt_chrono], then [opt_chrono] 
      is in [chronos] *)
  
  Lemma get_chrono_in :
    forall (chronos : list (Trans * option Chrono))
      (t : Trans)
      (opt_chrono : option Chrono),
      get_chrono chronos t = Some opt_chrono ->
      In opt_chrono (snd (split chronos)).
  Proof.
    intros chronos t.
    functional induction (get_chrono chronos t)
               using get_chrono_ind; intros.
    - inversion H.
    - rewrite snd_split_cons_app; simpl; left; injection H; auto.
    - rewrite snd_split_cons_app; simpl; right; apply IHo; auto.
  Qed.
  
  (** For all chronos and transition t, [get_chrono chronos t] returns no error
      if t is referenced in chronos. *)
  
  Lemma get_chrono_no_error :
    forall (chronos : list (Trans * option Chrono))
           (t : Trans),
      In t (fst (split chronos)) ->
      exists v : option Chrono, get_chrono chronos t = Some v.
  Proof.
    intros chronos t H;
      functional induction (get_chrono chronos t) using get_chrono_ind;
      decide_accessor_no_err.
  Qed.
  
  (** Returns true if chrono and chrono' are equal.
   
      Two chronos are equal only if their counter, lower bound and
      upper bound values are the same. *)
  
  Definition beq_chrono (chrono chrono' : Chrono) : bool :=
    match (max_t chrono), (max_t chrono') with
    | pos_inf, pos_inf =>
      ((cnt chrono) =? (cnt chrono'))
        && ((int (min_t chrono)) =? (int (min_t chrono')))
    | pos_val max_val, pos_val max_val' =>
      ((cnt chrono) =? (cnt chrono'))
        && ((int (min_t chrono)) =? (int (min_t chrono')))
        && ((int (max_val)) =? (int (max_val')))
    | _, _ => false
    end.

  Functional Scheme beq_chrono_ind := Induction for beq_chrono Sort Prop. 
  
  (** Returns a list of pairs (trans, chrono) where the first 
      occurence of old_chrono has been replaced by new_chrono. *)
  
  Fixpoint replace_chrono
           (old_chrono new_chrono : Chrono)
           (chronos : list (Trans * option Chrono))
           {struct chronos} :
    list (Trans * option Chrono) :=
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
  
  (** Proves that replace_chrono preserves structure of [chronos]. *)
  
  Lemma replace_chrono_same_struct :
    forall (old_chrono new_chrono : Chrono)
      (chronos : list (Trans * option Chrono)),
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
    - rewrite fst_split_cons_app; symmetry; rewrite fst_split_cons_app; simpl; auto.
    (* Case old_chrono is not head of list. *)
    - rewrite fst_split_cons_app; symmetry; rewrite fst_split_cons_app; rewrite IHl; auto.
    (* Case head of chronos is None. *)
    - rewrite fst_split_cons_app; symmetry; rewrite fst_split_cons_app; rewrite IHl; auto.
  Qed.

  (** If all chronos in [chronos] are well-formed, then [replace_chrono] returns 
      a list [chronos'] of well-formed chronos. *)
  
  Lemma replace_chrono_well_formed_chronos :
    forall (old_chrono new_chrono : Chrono)
           (chronos : list (Trans * option Chrono)),
      IsWellFormedChrono new_chrono ->
      (forall chrono : Chrono,
          In (Some chrono) (snd (split chronos)) -> IsWellFormedChrono chrono) ->
      forall chrono' : Chrono,
        In (Some chrono') (snd (split (replace_chrono old_chrono new_chrono chronos))) ->
        IsWellFormedChrono chrono'.
  Proof.
    intros old_chrono new_chrono chronos.
    functional induction (replace_chrono old_chrono new_chrono chronos)
               using replace_chrono_ind; intros.
    (* Base case, chronos = [] *)
    - elim H1.
    (* Case old_chrono = hd chronos *)
    - rewrite snd_split_cons_app in H1; simpl in H1; elim H1; intros.
      + injection H2; intro; rewrite <- H3; assumption.
      + apply or_intror with (A := In (Some chrono') (snd (split [(t, Some chrono)]))) in H2.
        apply in_or_app in H2.
        rewrite snd_split_cons_app in H0; apply (H0 chrono' H2).
    (* Case old_chrono <> hd chronos *)
    - rewrite snd_split_cons_app in H1; simpl in H1; elim H1; intros.
      + apply or_introl with (B := In (Some chrono') (snd (split tail))) in H2.
        rewrite snd_split_cons_app in H0; simpl in H0; apply (H0 chrono' H2).
      + apply IHl.
        -- assumption.
        -- intros; apply or_intror with (A := (Some chrono = Some chrono0)) in H3.
           rewrite snd_split_cons_app in H0; simpl in H0; apply (H0 chrono0 H3).
        -- assumption.
    (* Case None = hd chronos *)
    - rewrite snd_split_cons_app in H1; simpl in H1; elim H1; intros.
      + inversion H2.
      + apply IHl.
        -- assumption.
        -- intros; apply or_intror with (A := (None = Some chrono)) in H3.
           rewrite snd_split_cons_app in H0; simpl in H0; apply (H0 chrono H3).
        -- assumption.
  Qed.
  
  (** Returns a new list of chronos, where the time
      counter of transition t is incremented.
   
      Raises an error (None value) if get_chrono returns
      an error. *)
  
  Definition increment_chrono
             (t : Trans) 
             (chronos : list (Trans * option Chrono)) :
    option (list (Trans * option Chrono)) :=
    match get_chrono chronos t with
    | Some opt_chrono =>
      match opt_chrono with
      (* Replaces old chrono by an incremented chrono 
       * in chronos list.
       *)
      | Some (mk_chrono cnt min_t max_t) =>
        Some (replace_chrono (mk_chrono cnt min_t max_t)
                             (mk_chrono (cnt + 1) min_t max_t)
                             chronos)
      (* Otherwise, nothing to increment, t has no associated chrono. *)
      | None => Some chronos
      end
    (* Case of error!!! *)
    | None => None
    end.

  Functional Scheme increment_chrono_ind := Induction for increment_chrono Sort Prop. 
  
  (** Proves that increment_chrono preserves
      the structure of the chronos passed as argument. *)
  
  Lemma increment_chrono_same_struct :
    forall (t : Trans)
           (chronos chronos': list (Trans * option Chrono)),
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

  (** If all chronos in [chronos] are well-formed, then [increment_chrono] returns
      a list [chronos'] of well-formed chronos. *)
  
  Lemma increment_chrono_well_formed_chronos :
    forall (t : Trans)
           (chronos chronos': list (Trans * option Chrono)),
      (forall chrono : Chrono,
          In (Some chrono) (snd (split chronos)) -> IsWellFormedChrono chrono) -> 
      increment_chrono t chronos = Some chronos' ->
      (forall chrono' : Chrono,
          In (Some chrono') (snd (split chronos')) -> IsWellFormedChrono chrono').
  Proof.
    intros t chronos.
    functional induction (increment_chrono t chronos) using increment_chrono_ind; intros.
    (* GENERAL CASE (all went well) *)
    (* We need to prove that replace_chrono returns a list of well-formed chronos. *)
    - generalize (get_chrono_in
                    chronos t (Some {| cnt := cnt0; min_t := min_t0; max_t := max_t0 |}) e);
        intro. 
      apply H in H2.
      injection H0; intro.
      generalize (replace_chrono_well_formed_chronos
                    {| cnt := cnt0; min_t := min_t0; max_t := max_t0 |}
                    {| cnt := cnt0 + 1; min_t := min_t0; max_t := max_t0 |}
                    chronos H2 H); intro.
      rewrite H3 in H4.
      apply (H4 chrono' H1).
    - injection H0; intro; rewrite <- H2 in H1; apply (H chrono' H1).
    - inversion H0.
  Qed.
  
  (** For all transition [t] and [chronos], [increment_chrono t chronos] returns no error
      if t is referenced in chronos. *)
  
  Lemma increment_chrono_no_error :
    forall (t : Trans)
           (chronos : list (Trans * option Chrono)),
      In t (fst (split chronos)) ->
      exists v : list (Trans * option Chrono),
        increment_chrono t chronos = Some v.
  Proof.
    intros t chronos H.
    functional induction (increment_chrono t chronos)
               using increment_chrono_ind.    
    (* Base case *)
    - exists(replace_chrono
               {| cnt := cnt0;
                  min_t := min_t0;
                  max_t := max_t0 |}
               {| cnt := cnt0 + 1;
                  min_t := min_t0;
                  max_t := max_t0 |} 
               chronos).
      auto.
    (* Case opt_chrono = None *)
    - exists chronos; auto.    
    (* Case get_chrono = None, not possible. *)
    - apply get_chrono_no_error in H.
      elim H; intros; rewrite H0 in e; inversion e.      
  Qed.             
  
  (** Returns an option to a list of pairs (trans, option Chrono),
      where all chronos associated to transition in the list 
      [transs] have been incremented.
    
      Raises an error (None value) if an incrementation
      went wrong for one of the transition in the list. *)
  
  Fixpoint increment_all_chronos
           (chronos : list (Trans * option Chrono))
           (transs : list Trans) :
    option (list (Trans * option Chrono)) :=
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
    
  (** Proves that increment_all_chronos preserves
      the structure of the chronos passed as argument. *)
  
  Lemma increment_all_chronos_same_struct :
    forall (chronos : list (Trans * option Chrono))
           (transs : list Trans)
           (incremented_chronos : list (Trans * option Chrono)),
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

  (** If all chrono in [chronos] are well-formed, then [increment_all_chronos] 
      returns a list [increment_chronos] of well-formed chronos. *)

  Lemma increment_all_chronos_well_formed_chronos :
    forall (chronos : list (Trans * option Chrono))
      (transs : list Trans)
      (incremented_chronos : list (Trans * option Chrono)),
      (forall chrono : Chrono,
          In (Some chrono) (snd (split chronos)) -> IsWellFormedChrono chrono) ->
      increment_all_chronos chronos transs = Some incremented_chronos ->
      (forall chrono' : Chrono,
          In (Some chrono') (snd (split incremented_chronos)) -> IsWellFormedChrono chrono').
  Proof.
    intros chronos transs.
    functional induction (increment_all_chronos chronos transs)
               using increment_all_chronos_ind; intros.
    (* BASE CASE *)
    - injection H0; intros; rewrite <- H2 in H1; apply (H chrono' H1).
    (* GENERAL CASE *)
    (* We need to prove that increment_chrono returns a list of well-formed chronos. *)
    - apply IHo with (incremented_chronos := incremented_chronos).
      + intros.
        generalize (increment_chrono_well_formed_chronos t chronos0 new_chronos H e0); intro.
        apply (H3 chrono H2).
      + assumption.
      + assumption.
    (* CASE increment_chrono returns None, 
     * impossible regarding hypotheses 
     *)
    - inversion H0.
  Qed.
  
  (** Proves that increment_all_chronos returns no error 
      if all transitions of the list transs
      are referenced in chronos. *)
  
  Lemma increment_all_chronos_no_error :
    forall (chronos : list (Trans * option Chrono))
           (transs : list Trans),
      incl transs (fst (split chronos)) ->
      exists v : list (Trans * option Chrono),
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
  
  (** --------------------------------------------------------- *)
  (** --------------------------------------------------------- *)

  (** Returns a new list of chronos, where the time
      counter of transition t has been set to zero.
   
      Raises an error (None value) if get_chrono returns
      an error. *)
  
  Definition reset_chrono
             (t : Trans) 
             (chronos : list (Trans * option Chrono)) :
    option (list (Trans * option Chrono)) :=
    match get_chrono chronos t with
    | Some opt_chrono =>
      match opt_chrono with
      (* Replaces old chrono by a reset chrono in chronos list. *)
      | Some (mk_chrono cnt min_t max_t) =>
        Some (replace_chrono (mk_chrono cnt min_t max_t)
                             (mk_chrono 0 min_t max_t)
                             chronos)
      (* Otherwise, nothing to reset, t has no associated chrono. *)
      | None => Some chronos
      end
    (* Case of error!!! *)
    | None => None
    end.

  Functional Scheme reset_chrono_ind := Induction for reset_chrono Sort Prop. 
  
  (** Proves that reset_chrono preserves
      the structure of the chronos passed as argument. *)
  
  Lemma reset_chrono_same_struct :
    forall (t : Trans)
           (chronos chronos': list (Trans * option Chrono)),
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

  (** If all chronos in [chronos] are well-formed, then [reset_chrono] returns
      a list [chronos'] of well-formed chronos. *)
  
  Lemma reset_chrono_well_formed_chronos :
    forall (t : Trans)
      (chronos chronos': list (Trans * option Chrono)),
      (forall chrono : Chrono,
          In (Some chrono) (snd (split chronos)) -> IsWellFormedChrono chrono) -> 
      reset_chrono t chronos = Some chronos' ->
      (forall chrono' : Chrono,
          In (Some chrono') (snd (split chronos')) -> IsWellFormedChrono chrono').
  Proof.
    intros t chronos.
    functional induction (reset_chrono t chronos) using reset_chrono_ind; intros.
    (* GENERAL CASE (all went well) *)
    (* We need to prove that replace_chrono returns a list of well-formed chronos. *)
    - generalize (get_chrono_in
                    chronos t (Some {| cnt := cnt0; min_t := min_t0; max_t := max_t0 |}) e); intro. 
      apply H in H2.
      injection H0; intro.
      generalize (replace_chrono_well_formed_chronos
                    {| cnt := cnt0; min_t := min_t0; max_t := max_t0 |}
                    {| cnt := 0; min_t := min_t0; max_t := max_t0 |}
                    chronos H2 H); intro.
      rewrite H3 in H4.
      apply (H4 chrono' H1).
    - injection H0; intro; rewrite <- H2 in H1; apply (H chrono' H1).
    - inversion H0.
  Qed.
      
  (** For all transition t and chronos, reset_chrono t chronos returns no error
      if t is referenced in chronos. *)
  
  Lemma reset_chrono_no_error :
    forall (t : Trans)
           (chronos : list (Trans * option Chrono)),
      In t (fst (split chronos)) ->
      exists v : list (Trans * option Chrono),
        reset_chrono t chronos = Some v.
  Proof.
    intros t chronos H.
    functional induction (reset_chrono t chronos)
               using reset_chrono_ind.    
    (* Base case *)
    - exists(replace_chrono
               {| cnt := cnt0;
                  min_t := min_t0;
                  max_t := max_t0 |}
               {| cnt := 0;
                  min_t := min_t0;
                  max_t := max_t0 |}
               chronos).
      auto.
    (* Case opt_chrono = None *)
    - exists chronos; auto.    
    (* Case get_chrono = None, not possible. *)
    - apply get_chrono_no_error in H.
      elim H; intros; rewrite H0 in e; inversion e.      
  Qed.
    
  (** Returns an option to a list of pair (trans, option Chrono),
      where all chronos associated to transition in the list 
      transs have been set to zero.
               
      Raises an error (None value) if a reseting
      went wrong for one of the transition of the list. *)
  
  Fixpoint reset_all_chronos
           (chronos : list (Trans * option Chrono))
           (transs : list Trans) :
    option (list (Trans * option Chrono)) :=
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
  
  (** Proves that reset_all_chronos preserves
      the structure of the chronos passed as argument. *)
  
  Lemma reset_all_chronos_same_struct :
    forall (chronos : list (Trans * option Chrono))
      (transs : list Trans)
      (reset_chronos : list (Trans * option Chrono)),
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

  (** If all chrono in [chronos] are well-formed, then [reset_all_chronos] 
      returns a list [reset_chronos] of well-formed chronos. *)

  Lemma reset_all_chronos_well_formed_chronos :
    forall (chronos : list (Trans * option Chrono))
      (transs : list Trans)
      (reset_chronos : list (Trans * option Chrono)),
      (forall chrono : Chrono,
          In (Some chrono) (snd (split chronos)) -> IsWellFormedChrono chrono) ->
      reset_all_chronos chronos transs = Some reset_chronos ->
      (forall chrono' : Chrono,
          In (Some chrono') (snd (split reset_chronos)) -> IsWellFormedChrono chrono').
  Proof.
    intros chronos transs.
    functional induction (reset_all_chronos chronos transs)
               using reset_all_chronos_ind; intros.
    (* BASE CASE *)
    - injection H0; intros; rewrite <- H2 in H1; apply (H chrono' H1).
    (* GENERAL CASE *)
    (* We need to prove that reset_chrono returns a list of well-formed chronos. *)
    - apply IHo with (reset_chronos := reset_chronos).
      + intros. generalize (reset_chrono_well_formed_chronos t chronos0 new_chronos H e0); intro.
        apply (H3 chrono H2).
      + assumption.
      + assumption.
    (* CASE reset_chrono returns None, 
     * impossible regarding hypotheses 
     *)
    - inversion H0.
  Qed.
  
  (** Proves that reset_all_chronos returns no error 
      if all transitions of the list transs
      are referenced in chronos. *)
  
  Lemma reset_all_chronos_no_error :
    forall (chronos : list (Trans * option Chrono))
           (transs : list Trans),
      incl transs (fst (split chronos)) ->
      exists v : list (Trans * option Chrono),
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

(** * List sensitized section *)

(*==============================================================*)
(*================= LIST SENSITIZED SECTION  ===================*)
(*==============================================================*)

Section ListSensitized.
  
  (* 
   * Useless fonction for Spn but useful for 
   *
   * -  _asynchronous_ Petri nets
   * -  Stpn (and SITPN by extension) 
   *
   * Needed to list sensitized transitions, to increment 
   * time counters for these transitions at the beginning of the cycle.
   * 
   * Needed to list disabled transitions, to reset
   * time counters for these transitions at the beginning of the cycle.    
   *)

  (** Returns the list of sensitized transitions
      contained in transs.
                
      Raises an error (None value) if get_neighbours or
      is_sensitized return None. *)
  
  Fixpoint list_sensitized_aux 
           (lneighbours : list (Trans * Neighbours))
           (pre test inhib : Weight) 
           (m : list (Place * nat))
           (sensitized_transs : list Trans)
           (transs : list Trans) :
    option (list Trans) :=
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

  (** Formal specification : list_sensitized_aux *)

  Inductive ListSensitizedAux
            (lneighbours : list (Trans * Neighbours))
            (pre test inhib : Weight) 
            (m : list (Place * nat))
            (sensitized_transs : list Trans) :
    list Trans -> (* sometranss *)
    option (list Trans) -> (* opt_sensitized_transs *)
    Prop :=
  | ListSensitizedAux_nil :
      ListSensitizedAux lneighbours pre test inhib m sensitized_transs []
                        (Some sensitized_transs)      
  | ListSensitizedAux_get_neighbours_err :
      forall (transs : list Trans)
             (t : Trans),
        GetNeighbours lneighbours t None ->
        ListSensitizedAux lneighbours pre test inhib m sensitized_transs (t :: transs) None      
  | ListSensitizedAux_is_sensitized_err :
      forall (transs : list Trans)
             (t : Trans)
             (neighbours_t : Neighbours),
        GetNeighbours lneighbours t (Some neighbours_t) ->
        IsSensitized neighbours_t pre test inhib m t None ->
        ListSensitizedAux lneighbours pre test inhib m sensitized_transs (t :: transs) None
  | ListSensitizedAux_is_sensitized_true :
      forall (transs : list Trans)
             (t : Trans)
             (neighbours_t : Neighbours)
             (opt_sensitized_transs : option (list Trans)),
        GetNeighbours lneighbours t (Some neighbours_t) ->
        IsSensitized neighbours_t pre test inhib m t (Some true) ->
        ListSensitizedAux lneighbours pre test inhib m (t :: sensitized_transs) transs
                          opt_sensitized_transs ->
        ListSensitizedAux lneighbours pre test inhib m sensitized_transs (t :: transs)
                          opt_sensitized_transs
  | ListSensitizedAux_is_sensitized_false :
      forall (transs : list Trans)
        (t : Trans)
        (neighbours_t : Neighbours)
        (opt_sensitized_transs : option (list Trans)),
        GetNeighbours lneighbours t (Some neighbours_t) ->
        IsSensitized neighbours_t pre test inhib m t (Some false) ->
        ListSensitizedAux lneighbours pre test inhib m sensitized_transs transs
                          opt_sensitized_transs ->
        ListSensitizedAux lneighbours pre test inhib m sensitized_transs (t :: transs)
                          opt_sensitized_transs.
  
  Functional Scheme list_sensitized_aux_ind := Induction for list_sensitized_aux Sort Prop.

  (** Correctness proof : list_sensitized_aux *)

  Theorem list_sensitized_aux_correct :
    forall (lneighbours : list (Trans * Neighbours))
      (pre test inhib : Weight)
      (m : list (Place * nat))
      (sensitized_transs transs : list Trans)
      (opt_sensitized_transs : option (list Trans)),
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

  (** Completeness proof : list_sensitized_aux *)
  
  Theorem list_sensitized_aux_complete :
    forall (lneighbours : list (Trans * Neighbours))
           (pre test inhib : Weight)
           (m : list (Place * nat))
           (sensitized_transs transs : list Trans)
           (opt_sensitized_transs : option (list Trans)),
      ListSensitizedAux lneighbours pre test inhib m sensitized_transs
                        transs opt_sensitized_transs ->
      list_sensitized_aux lneighbours pre test inhib m sensitized_transs
                          transs = opt_sensitized_transs.
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

  (** If list_sensitized_aux returns Some final_sensitized then
      all transitions in final_sensitized are in sensitized_transs ++ transs. *)
  
  Lemma list_sensitized_aux_incl_transs :
    forall (lneighbours : list (Trans * Neighbours))
           (pre test inhib : Weight)
           (m : list (Place * nat))
           (sensitized_transs transs final_sensitized : list Trans),
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
  
  (** [list_sensitized_aux] returns no error if all transition t in [transs] 
      are referenced in [lneighbours] and if all neighbour places referenced 
      in [lneighbours] are referenced in the marking [m]. *)
  
  Lemma list_sensitized_aux_no_error :
    forall (lneighbours : list (Trans * Neighbours))
           (pre test inhib : Weight)
           (m : list (Place * nat))
           (sensitized_transs transs : list Trans),
      incl transs (fst (split lneighbours)) ->
      (forall (t : Trans) (neighbours : Neighbours),
          In (t, neighbours) lneighbours ->
          (incl neighbours.(pre_pl) (fst (split m)) /\
           incl neighbours.(inhib_pl) (fst (split m)) /\
           incl neighbours.(test_pl) (fst (split m)))) ->
      exists v : list Trans,
        list_sensitized_aux lneighbours pre test inhib m sensitized_transs transs = Some v.
  Proof.
    unfold incl.
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

  (** Wrapper around list_sensitized_aux. *)
  
  Definition list_sensitized 
             (lneighbours : list (Trans * Neighbours))
             (pre test inhib : Weight) 
             (m : list (Place * nat))
             (transs : list Trans) : option (list Trans) :=
    list_sensitized_aux lneighbours pre test inhib m [] transs.

  (** Formal specification : list_sensitized *)
  
  Inductive ListSensitized
            (lneighbours : list (Trans * Neighbours))
            (pre test inhib : Weight) 
            (m : list (Place * nat)) :
    list Trans ->
    option (list Trans) -> Prop :=
  | ListSensitized_cons :
      forall (transs : list Trans)
             (opt_sensitized_transs : option (list Trans)),
        ListSensitizedAux lneighbours pre test inhib m [] transs opt_sensitized_transs ->
        ListSensitized lneighbours pre test inhib m transs opt_sensitized_transs.

  Functional Scheme list_sensitized_ind := Induction for list_sensitized Sort Prop.

  (** Correctness proof : list_sensitized *)
  
  Theorem list_sensitized_correct :
    forall (lneighbours : list (Trans * Neighbours))
           (pre test inhib : Weight)
           (m : list (Place * nat))
           (transs : list Trans)
           (opt_sensitized_transs : option (list Trans)),
      list_sensitized lneighbours pre test inhib m transs = opt_sensitized_transs ->
      ListSensitized lneighbours pre test inhib m transs opt_sensitized_transs.
  Proof.
    intros lneighbours pre test inhib m transs.
    functional induction (list_sensitized lneighbours pre test inhib m transs)
               using list_sensitized_ind; intros.
    apply ListSensitized_cons.
    apply list_sensitized_aux_correct; auto.  
  Qed.

  (** Completeness proof : list_sensitized *)
  
  Theorem list_sensitized_complete :
    forall (lneighbours : list (Trans * Neighbours))
           (pre test inhib : Weight)
           (m : list (Place * nat))
           (transs : list Trans)
           (opt_sensitized_transs : option (list Trans)),
      ListSensitized lneighbours pre test inhib m transs opt_sensitized_transs ->
      list_sensitized lneighbours pre test inhib m transs = opt_sensitized_transs.
  Proof.
    intros; elim H; intros.
    unfold list_sensitized; apply list_sensitized_aux_complete in H0; rewrite H0; auto. 
  Qed.

  (** All transitions in sensitized_transs (returned by list_sensitized_aux)
      are in transs. *)
  
  Lemma list_sensitized_incl_transs :
    forall (lneighbours : list (Trans * Neighbours))
           (pre test inhib : Weight)
           (m : list (Place * nat))
           (transs sensitized_transs : list Trans),
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
  
  (** [list_sensitized] returns no error if all transition t in [transs] are 
      referenced in [lneighbours] and if all neighbour places referenced in 
      [lneighbours] are referenced in the marking [m]. *)
  
  Lemma list_sensitized_no_error :
    forall (lneighbours : list (Trans * Neighbours))
           (pre test inhib : Weight)
           (m : list (Place * nat))
           (transs : list Trans),
      incl transs (fst (split lneighbours)) ->
      (forall (t : Trans) (neighbours : Neighbours),
          In (t, neighbours) lneighbours ->
          (incl neighbours.(pre_pl) (fst (split m)) /\
           incl neighbours.(inhib_pl) (fst (split m)) /\
           incl neighbours.(test_pl) (fst (split m)))) ->
      exists v : list Trans,
        list_sensitized lneighbours pre test inhib m transs = Some v.
  Proof.
    intros lneighbours pre test inhib m transs; intros.
    unfold list_sensitized.
    apply list_sensitized_aux_no_error; [auto | auto].
  Qed.
  
End ListSensitized.

(** * List disabled section  *)

(*============================================================*)
(*================= LIST DISABLED SECTION  ===================*)
(*============================================================*)

Section ListDisabled.
  
  (** Returns the list of disabled transitions contained in transs.
   
      Raises an error (None value) if get_neighbours or
      is_sensitized return None. *)
  
  Fixpoint list_disabled_aux 
           (lneighbours : list (Trans * Neighbours))
           (pre test inhib : Weight) 
           (m : list (Place * nat))
           (disabled_transs : list Trans)
           (transs : list Trans) :
    option (list Trans) :=
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

  (** Formal specification : list_disabled_aux *)
  
  Inductive ListDisabledAux
            (lneighbours : list (Trans * Neighbours))
            (pre test inhib : Weight) 
            (m : list (Place * nat))
            (disabled_transs : list Trans) :
    list Trans -> (* sometranss *)
    option (list Trans) -> (* opt_disabled_transs *)
    Prop :=
  | ListDisabledAux_nil :
      ListDisabledAux lneighbours pre test inhib m disabled_transs []
                        (Some disabled_transs)      
  | ListDisabledAux_get_neighbours_err :
      forall (transs : list Trans)
             (t : Trans),
        GetNeighbours lneighbours t None ->
        ListDisabledAux lneighbours pre test inhib m disabled_transs (t :: transs) None      
  | ListDisabledAux_is_sensitized_err :
      forall (transs : list Trans)
             (t : Trans)
             (neighbours_t : Neighbours),
        GetNeighbours lneighbours t (Some neighbours_t) ->
        IsSensitized neighbours_t pre test inhib m t None ->
        ListDisabledAux lneighbours pre test inhib m disabled_transs (t :: transs) None
  | ListDisabledAux_is_disabled_false :
      forall (transs : list Trans)
             (t : Trans)
             (neighbours_t : Neighbours)
             (opt_disabled_transs : option (list Trans)),
        GetNeighbours lneighbours t (Some neighbours_t) ->
        IsSensitized neighbours_t pre test inhib m t (Some true) ->
        ListDisabledAux lneighbours pre test inhib m disabled_transs transs
                        opt_disabled_transs ->
        ListDisabledAux lneighbours pre test inhib m disabled_transs (t :: transs)
                        opt_disabled_transs
  | ListDisabledAux_is_disabled_true :
      forall (transs : list Trans)
             (t : Trans)
             (neighbours_t : Neighbours)
             (opt_disabled_transs : option (list Trans)),
        GetNeighbours lneighbours t (Some neighbours_t) ->
        IsSensitized neighbours_t pre test inhib m t (Some false) ->
        ListDisabledAux lneighbours pre test inhib m (t :: disabled_transs) transs
                        opt_disabled_transs ->
        ListDisabledAux lneighbours pre test inhib m disabled_transs (t :: transs)
                        opt_disabled_transs.
  
  Functional Scheme list_disabled_aux_ind := Induction for list_disabled_aux Sort Prop.

  (** Correctness proof : list_disabled_aux *)
  
  Theorem list_disabled_aux_correct :
    forall (lneighbours : list (Trans * Neighbours))
           (pre test inhib : Weight)
           (m : list (Place * nat))
           (disabled_transs transs : list Trans)
           (opt_disabled_transs : option (list Trans)),
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

  (** Completeness proof : list_disabled_aux *)

  Theorem list_disabled_aux_complete :
    forall (lneighbours : list (Trans * Neighbours))
           (pre test inhib : Weight)
           (m : list (Place * nat))
           (disabled_transs transs : list Trans)
           (opt_disabled_transs : option (list Trans)),
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

  (** If all transitions in transs are ref in lneighbours then 
      all transitions in disabled_transs (returned by list_disabled_aux)
      are in lneighbours. *)
  
  Lemma list_disabled_aux_incl_lneighbours :
    forall (lneighbours : list (Trans * Neighbours))
           (pre test inhib : Weight)
           (m : list (Place * nat))
           (disabled_transs transs final_disabled : list Trans),
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

  (** If list_disabled_aux returns Some final_disabled then
      all transitions in final_disabled are in disabled_transs ++ transs. *)
  
  Lemma list_disabled_aux_incl_transs :
    forall (lneighbours : list (Trans * Neighbours))
           (pre test inhib : Weight)
           (m : list (Place * nat))
           (disabled_transs transs final_disabled : list Trans),
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
  
  (** [list_disabled_aux] returns no error if all transition t in [transs] 
      are referenced in [lneighbours] and if all neighbour places 
      referenced in [lneighbours] are referenced in the marking [m]. *)
  
  Lemma list_disabled_aux_no_error :
    forall (lneighbours : list (Trans * Neighbours))
           (pre test inhib : Weight)
           (m : list (Place * nat))
           (disabled_transs transs : list Trans),
      incl transs (fst (split lneighbours)) ->
      (forall (t : Trans) (neighbours : Neighbours),
          In (t, neighbours) lneighbours ->
          (incl neighbours.(pre_pl) (fst (split m)) /\
           incl neighbours.(inhib_pl) (fst (split m)) /\
           incl neighbours.(test_pl) (fst (split m)))) ->
      exists v : list Trans,
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
  
  (** Wrapper around list_disabled_aux. *)
  
  Definition list_disabled 
             (lneighbours : list (Trans * Neighbours))
             (pre test inhib : Weight) 
             (m : list (Place * nat))
             (transs : list Trans) : option (list Trans) :=
    list_disabled_aux lneighbours pre test inhib m [] transs.

  (** Formal specification : list_disabled *)

  Inductive ListDisabled
            (lneighbours : list (Trans * Neighbours))
            (pre test inhib : Weight) 
            (m : list (Place * nat)) :
    list Trans ->
    option (list Trans) -> Prop :=
  | ListDisabled_cons :
      forall (transs : list Trans)
             (opt_disabled_transs : option (list Trans)),
        ListDisabledAux lneighbours pre test inhib m [] transs opt_disabled_transs ->
        ListDisabled lneighbours pre test inhib m transs opt_disabled_transs.

  Functional Scheme list_disabled_ind := Induction for list_disabled Sort Prop.

  (** Correctness proof : list_disabled *)

  Theorem list_disabled_correct :
    forall (lneighbours : list (Trans * Neighbours))
           (pre test inhib : Weight)
           (m : list (Place * nat))
           (transs : list Trans)
           (opt_disabled_transs : option (list Trans)),
      list_disabled lneighbours pre test inhib m transs = opt_disabled_transs ->
      ListDisabled lneighbours pre test inhib m transs opt_disabled_transs.
  Proof.
    intros lneighbours pre test inhib m transs.
    functional induction (list_disabled lneighbours pre test inhib m transs)
               using list_disabled_ind; intros.
    apply ListDisabled_cons.
    apply list_disabled_aux_correct; auto.  
  Qed.

  (** Completeness proof : list_disabled *)

  Theorem list_disabled_complete :
    forall (lneighbours : list (Trans * Neighbours))
           (pre test inhib : Weight)
           (m : list (Place * nat))
           (transs : list Trans)
           (opt_disabled_transs : option (list Trans)),
      ListDisabled lneighbours pre test inhib m transs opt_disabled_transs ->
      list_disabled lneighbours pre test inhib m transs = opt_disabled_transs.
  Proof.
    intros; elim H; intros.
    unfold list_disabled; apply list_disabled_aux_complete in H0; rewrite H0; auto. 
  Qed.

  (** If all transitions in [transs] are ref in [lneighbours] then 
      all transitions in [disabled_transs] (returned by [list_disabled])
      are ref in [lneighbours]. *)
  
  Lemma list_disabled_incl_lneighbours :
    forall (lneighbours : list (Trans * Neighbours))
           (pre test inhib : Weight)
           (m : list (Place * nat))
           (transs disabled_transs : list Trans),
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

  (** All transitions in [disabled_transs] (returned by [list_disabled_aux])
      are in [transs]. *)

  Lemma list_disabled_incl_transs :
    forall (lneighbours : list (Trans * Neighbours))
           (pre test inhib : Weight)
           (m : list (Place * nat))
           (transs disabled_transs : list Trans),
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
      
  (** [list_disabled] returns no error if all transition t in [transs] are 
     referenced in [lneighbours] and if all neighbour places referenced in 
     [lneighbours] are referenced in the marking [m]. *)
  
  Lemma list_disabled_no_error :
    forall (lneighbours : list (Trans * Neighbours))
      (pre test inhib : Weight)
      (m : list (Place * nat))
      (transs : list Trans),
      incl transs (fst (split lneighbours)) ->
      (forall (t : Trans) (neighbours : Neighbours),
          In (t, neighbours) lneighbours ->
          (incl neighbours.(pre_pl) (fst (split m)) /\
           incl neighbours.(inhib_pl) (fst (split m)) /\
           incl neighbours.(test_pl) (fst (split m)))) ->
      exists v : list Trans,
        list_disabled lneighbours pre test inhib m transs = Some v.
  Proof.
    intros lneighbours pre test inhib m transs; intros.
    unfold list_disabled.
    apply list_disabled_aux_no_error; [auto | auto].
  Qed.
  
End ListDisabled.

(** * Firing algorithm for Stpn *)

(*** ========================= ***)
(*** FIRING ALGORITHM for Stpn ***)
(*** ========================= ***)

Section FireStpn.

  (** Returns [true] if transition t is firable according
      to "[Stpn] standards", meaning that t is sensitized and
      its time counter value is in the firable interval.
   
      Raises an error (None value) if spn_is_firable or get_chronos 
      returns None. *)
  
  Definition stpn_is_firable
             (t : Trans)
             (neighbours_t : Neighbours)
             (pre test inhib: Weight)
             (steadym decreasingm : list (Place * nat))
             (chronos : list (Trans * option Chrono)) :
    option bool :=
    match spn_is_firable t neighbours_t pre test inhib steadym decreasingm with
    (* If t is firable according to "Spn standards", then checks its chrono. *)
    | Some true =>
      match get_chrono chronos t with
      (* Case t is referenced in chronos. *)
      | Some opt_chrono => Some (check_chrono opt_chrono)
      (* Error case!!! *)
      | None => None
      end
    (* t is not firable according to Spn. *)
    | Some false => Some false
    (* Error case!!! *)
    | None => None
    end.

  Functional Scheme stpn_is_firable_ind := Induction for stpn_is_firable Sort Prop.
  
  (** Formal specification : stpn_is_firable *)
  
  Inductive StpnIsFirable
            (t : Trans)
            (neighbours_t : Neighbours)
            (pre test inhib: Weight)
            (steadym decreasingm : list (Place * nat))
            (chronos : list (Trans * option Chrono)) :
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
      forall (opt_chrono : option Chrono),
        SpnIsFirable t neighbours_t pre test inhib steadym decreasingm (Some true) ->
        GetChrono chronos t (Some opt_chrono) ->
        CheckChrono opt_chrono ->
        StpnIsFirable t neighbours_t pre test inhib steadym decreasingm chronos (Some true)
  | StpnIsFirable_cons_false :
      forall (opt_chrono : option Chrono),
        SpnIsFirable t neighbours_t pre test inhib steadym decreasingm (Some true) ->
        GetChrono chronos t (Some opt_chrono) ->
        ~CheckChrono opt_chrono ->
        StpnIsFirable t neighbours_t pre test inhib steadym decreasingm chronos (Some false).

  (** Correctness proof : stpn_is_firable *)
  
  Theorem stpn_is_firable_correct :
    forall (t : Trans)
      (neighbours_t : Neighbours)
      (pre test inhib: Weight)
      (steadym decreasingm : list (Place * nat))
      (chronos : list (Trans * option Chrono))
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

  (** Completeness proof : stpn_is_firable *)
  
  Theorem stpn_is_firable_compl :
    forall (t : Trans)
      (neighbours_t : Neighbours)
      (pre test inhib: Weight)
      (steadym decreasingm : list (Place * nat))
      (chronos : list (Trans * option Chrono))
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

  (** Proves that stpn_is_firable returns no error if
      the places in (pre_pl neighbours_t), (inhib_pl neighbours_t) 
      and (test_pl neighbours_t) are referenced in markings steadym
      and decreasingm, and if t is referenced in chronos. *)
  
  Lemma stpn_is_firable_no_error :
    forall (t : Trans)
           (neighbours_t : Neighbours)
           (pre test inhib : Weight)
           (steadym decreasingm : list (Place * nat))
           (chronos : list (Trans * option Chrono)),
      In t (fst (split chronos)) ->
      incl (pre_pl neighbours_t) (fst (split decreasingm)) ->
      incl (test_pl neighbours_t) (fst (split steadym)) ->
      incl (inhib_pl neighbours_t) (fst (split steadym)) ->
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

  (** ------------------------------------------------------------------- *)
  (** ------------------------------------------------------------------- *)
  
  (** Given 1 priority group of transitions (a list [pgroup]), 
      returns 1 list of transitions [fired_pre_group] 
      and marking [decreasingm] accordingly ...
   
      Returns a couple (list of transitions, marking).
      
      For each sensitized transition of the list,
      the marking of the pre-condition places are updated (the 
      transition is fired). "decreasingm" is then the resulting marking. *)
  
  Fixpoint stpn_fire_pre_aux
           (lneighbours : list (Trans * Neighbours))
           (pre test inhib : Weight)  
           (steadym : list (Place * nat))
           (decreasingm : list (Place * nat))
           (chronos : list (Trans * option Chrono))
           (fired_pre_group pgroup : list Trans) {struct pgroup} :
    option ((list Trans) * list (Place * nat)) :=
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
  
  (** Formal specification : spn_fire_pre_aux *)
  
  Inductive StpnFirePreAux
            (lneighbours : list (Trans * Neighbours))
            (pre test inhib : Weight) 
            (steadym : list (Place * nat)) 
            (decreasingm : list (Place * nat))
            (chronos : list (Trans * option Chrono))
            (fired_pre_group : list Trans) :
    list Trans -> option (list Trans * list (Place * nat)) -> Prop :=
  | StpnFirePreAux_nil :
      StpnFirePreAux lneighbours pre test inhib steadym decreasingm chronos fired_pre_group []
                     (Some (fired_pre_group, decreasingm))
  (* Case get_neighbours returns an error. *)
  | StpnFirePreAux_neighbours_err :
      forall (t : Trans) (pgroup : list Trans),
        GetNeighbours lneighbours t None ->
        StpnFirePreAux lneighbours pre test inhib steadym decreasingm chronos fired_pre_group (t :: pgroup) None
  (* Case stpn_is_firable returns an error. *)
  | StpnFirePreAux_firable_err :
      forall (t : Trans) (pgroup : list Trans) (neighbours_t : Neighbours),
        GetNeighbours lneighbours t (Some neighbours_t) ->
        StpnIsFirable t neighbours_t pre test inhib steadym decreasingm chronos None ->
        StpnFirePreAux lneighbours pre test inhib steadym decreasingm chronos fired_pre_group (t :: pgroup) None
  (* Case stpn_is_firable returns false. *)
  | StpnFirePreAux_firable_false :
      forall (t : Trans)
             (pgroup : list Trans)
             (neighbours_t : Neighbours)
             (option_final_couple : option (list Trans * list (Place * nat))),
        GetNeighbours lneighbours t (Some neighbours_t) ->
        StpnIsFirable t neighbours_t pre test inhib steadym decreasingm chronos (Some false) ->
        StpnFirePreAux lneighbours pre test inhib steadym decreasingm chronos fired_pre_group pgroup
                       option_final_couple ->
        StpnFirePreAux lneighbours pre test inhib steadym decreasingm chronos fired_pre_group (t :: pgroup)
                       option_final_couple
  (* Case update_marking_pre returns an error. *)
  | StpnFirePreAux_update_err :
      forall (t : Trans)
             (neighbours_t : Neighbours)
             (pgroup : list Trans),
        GetNeighbours lneighbours t (Some neighbours_t) ->
        StpnIsFirable t neighbours_t pre test inhib steadym decreasingm chronos (Some true) ->
        UpdateMarkingPre t pre decreasingm (pre_pl neighbours_t) None ->
        StpnFirePreAux lneighbours pre test inhib steadym decreasingm chronos fired_pre_group (t :: pgroup) None
  (* General case, all went well. *)
  | StpnFirePreAux_cons :
      forall (t : Trans)
             (neighbours_t : Neighbours)
             (pgroup : list Trans)
             (modifiedm : list (Place * nat))
             (option_final_couple : option (list Trans * list (Place * nat))),
        GetNeighbours lneighbours t (Some neighbours_t) ->
        StpnIsFirable t neighbours_t pre test inhib steadym decreasingm chronos (Some true) ->
        UpdateMarkingPre t pre decreasingm (pre_pl neighbours_t) (Some modifiedm) ->
        StpnFirePreAux lneighbours pre test inhib steadym modifiedm chronos (fired_pre_group ++ [t]) pgroup
                       option_final_couple ->
        StpnFirePreAux lneighbours pre test inhib steadym decreasingm chronos fired_pre_group (t :: pgroup)
                       option_final_couple.

  (** Correctness proof : stpn_fire_pre_aux *)
  
  Theorem stpn_fire_pre_aux_correct :
    forall (lneighbours : list (Trans * Neighbours))
      (pre test inhib : Weight) 
      (steadym : list (Place * nat)) 
      (decreasingm : list (Place * nat))
      (chronos : list (Trans * option Chrono))
      (fired_pre_group : list Trans)
      (pgroup : list Trans)
      (option_final_couple : option (list Trans * list (Place * nat))),
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

  (** Completeness proof : stpn_fire_pre_aux *)
  
  Theorem stpn_fire_pre_aux_compl :
    forall (lneighbours : list (Trans * Neighbours))
           (pre test inhib : Weight) 
           (steadym : list (Place * nat)) 
           (decreasingm : list (Place * nat))
           (chronos : list (Trans * option Chrono))
           (fired_pre_group : list Trans)
           (pgroup : list Trans)
           (option_final_couple : option (list Trans * list (Place * nat))),
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

  (** Proves that stpn_fire_pre preserves
      the structure of the marking decreasingm
      passed as argument.
   
      stpn_fire_pre returns a marking decreasedm
      which has the same structure as decreasingm. *)
  
  Lemma stpn_fire_pre_aux_same_struct :
    forall (lneighbours : list (Trans * Neighbours))
      (pre test inhib : Weight) 
      (steadym : list (Place * nat)) 
      (decreasingm : list (Place * nat))
      (chronos : list (Trans * option Chrono))
      (fired_pre_group : list Trans)
      (pgroup : list Trans)
      (pre_fired_transitions : list Trans)
      (decreasedm : list (Place * nat)),
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

  (** If all transitions in [pgroup] are in [lneighbours] then 
      all transitions in [final_fired_pre_group] (returned by [stpn_fire_pre_aux])
      are in [lneighbours]. *)
  
  Lemma stpn_fire_pre_aux_final_fired_in_lneighbours :
    forall (lneighbours : list (Trans * Neighbours))
           (pre test inhib : Weight) 
           (steadym : list (Place * nat)) 
           (decreasingm : list (Place * nat))
           (chronos : list (Trans * option Chrono))
           (fired_pre_group : list Trans)
           (pgroup : list Trans)
           (final_fired_pre_group : list Trans)
           (finalm : list (Place * nat)),
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
  
  (** If all transitions in [pgroup] are ref in [chronos] then 
      all transitions in [final_fired_pre_group] (returned by [stpn_fire_pre_aux])
      are ref in [chronos]. *)
  
  Lemma stpn_fire_pre_aux_final_fired_in_chronos :
    forall (lneighbours : list (Trans * Neighbours))
           (pre test inhib : Weight) 
           (steadym : list (Place * nat)) 
           (decreasingm : list (Place * nat))
           (chronos : list (Trans * option Chrono))
           (fired_pre_group : list Trans)
           (pgroup : list Trans)
           (final_fired_pre_group : list Trans)
           (finalm : list (Place * nat)),
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
  
  (** [stpn_fire_pre_aux] returns no error if 
      all transition t in [pgroup] are referenced in [lneighbours]
      and if all neighbour places referenced in [lneighbours] are
      referenced in the markings [steadym] and [decreasingm]. *)
  
  Lemma stpn_fire_pre_aux_no_error :
    forall (lneighbours : list (Trans * Neighbours))
           (pre test inhib : Weight) 
           (steadym : list (Place * nat)) 
           (decreasingm : list (Place * nat))
           (chronos : list (Trans * option Chrono))
           (fired_pre_group : list Trans)
           (pgroup : list Trans),
      incl pgroup (fst (split chronos)) ->
      incl pgroup (fst (split lneighbours)) ->
      (forall (t : Trans) (neighbours : Neighbours),
          In (t, neighbours) lneighbours ->
          (incl neighbours.(pre_pl) (fst (split decreasingm)) /\
           incl neighbours.(inhib_pl) (fst (split steadym)) /\
           incl neighbours.(test_pl) (fst (split steadym)))) ->
      exists v : (list Trans * list (Place * nat)),
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
                                      steadym decreasingm chronos H3 H4 H6) in H2.
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
  
  (** ------------------------------------------------- *)
  (** ------------------------------------------------- *)
  
  (** Wrapper function around stpn_fire_pre_aux. *)
  
  Definition stpn_fire_pre
             (lneighbours : list (Trans * Neighbours))
             (pre test inhib : Weight) 
             (steadym : list (Place * nat)) 
             (decreasingm : list (Place * nat))
             (chronos : list (Trans * option Chrono))
             (pgroup : list Trans) :
    option (list Trans * list (Place * nat)) :=
    stpn_fire_pre_aux lneighbours pre test inhib steadym decreasingm chronos [] pgroup.

  Functional Scheme stpn_fire_pre_ind := Induction for stpn_fire_pre Sort Prop.

  (** Formal specification : stpn_fire_pre *)
  Inductive StpnFirePre
            (lneighbours : list (Trans * Neighbours))
            (pre test inhib : Weight) 
            (steadym : list (Place * nat)) 
            (decreasingm : list (Place * nat))
            (chronos : list (Trans * option Chrono))
            (pgroup : list Trans) : option (list Trans * list (Place * nat)) -> Prop :=
  | StpnFirePre_cons :
      forall (option_final_couple : option (list Trans * list (Place * nat))),
        StpnFirePreAux lneighbours pre test inhib steadym decreasingm chronos [] pgroup
                       option_final_couple ->
        StpnFirePre lneighbours pre test inhib steadym decreasingm chronos pgroup
                    option_final_couple.

  (** Correctness proof : stpn_fire_pre *)
  
  Theorem stpn_fire_pre_correct :
    forall (lneighbours : list (Trans * Neighbours))
           (pre test inhib : Weight) 
           (steadym decreasingm : list (Place * nat))
           (chronos : list (Trans * option Chrono))
           (pgroup : list Trans)
           (option_final_couple : option (list Trans * list (Place * nat))),
      stpn_fire_pre lneighbours pre test inhib steadym decreasingm chronos pgroup = option_final_couple ->
      StpnFirePre lneighbours pre test inhib steadym decreasingm chronos pgroup option_final_couple.
  Proof.
    intros; unfold stpn_fire_pre in H.
    apply StpnFirePre_cons; apply stpn_fire_pre_aux_correct in H; auto.
  Qed.

  (** Completeness proof : stpn_fire_pre *)
  Theorem stpn_fire_pre_compl :
    forall (lneighbours : list (Trans * Neighbours))
           (pre test inhib : Weight) 
           (steadym decreasingm : list (Place * nat))
           (chronos : list (Trans * option Chrono))
           (pgroup : list Trans)
           (option_final_couple : option (list Trans * list (Place * nat))),
      StpnFirePre lneighbours pre test inhib steadym decreasingm chronos pgroup option_final_couple ->
      stpn_fire_pre lneighbours pre test inhib steadym decreasingm chronos pgroup = option_final_couple.
  Proof.
    intros; elim H; intros.
    unfold stpn_fire_pre; apply stpn_fire_pre_aux_compl in H0; auto. 
  Qed.

  (** Proves that [stpn_fire_pre] preserves
      the structure of the marking [decreasingm]
      passed as argument.
   
      [stpn_fire_pre] returns a marking [decreasedm]
      which has the same structure as [decreasingm]. *)
  
  Lemma stpn_fire_pre_same_struct :
    forall (lneighbours : list (Trans * Neighbours))
      (pre test inhib : Weight) 
      (steadym : list (Place * nat)) 
      (decreasingm : list (Place * nat))
      (chronos : list (Trans * option Chrono))
      (pgroup : list Trans)
      (pre_fired_transitions : list Trans)
      (decreasedm : list (Place * nat)),
      stpn_fire_pre lneighbours pre test inhib steadym decreasingm chronos pgroup =
      Some (pre_fired_transitions, decreasedm) ->
      MarkingHaveSameStruct decreasingm decreasedm.
  Proof.
    intros lneighbours pre test inhib steadym decreasingm chronos pgroup; intros.
    unfold stpn_fire_pre in H.
    apply stpn_fire_pre_aux_same_struct in H; auto.
  Qed.

  (** If all transitions in [pgroup] are in [lneighbours] then 
      all transitions in [final_fired_pre_group] (returned by [stpn_fire_pre])
      are in [lneighbours]. *)
  
  Lemma stpn_fire_pre_final_fired_in_lneighbours :
    forall (lneighbours : list (Trans * Neighbours))
           (pre test inhib : Weight) 
           (steadym : list (Place * nat)) 
           (decreasingm : list (Place * nat))
           (chronos : list (Trans * option Chrono))
           (pgroup : list Trans)
           (final_fired_pre_group : list Trans)
           (finalm : list (Place * nat)),
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

  (** If all transitions in [pgroup] are ref in [chronos] then 
      all transitions in [final_fired_pre_group] (returned by [stpn_fire_pre])
      are ref in [chronos]. *)
  
  Lemma stpn_fire_pre_final_fired_in_chronos :
    forall (lneighbours : list (Trans * Neighbours))
      (pre test inhib : Weight) 
      (steadym : list (Place * nat)) 
      (decreasingm : list (Place * nat))
      (chronos : list (Trans * option Chrono))
      (pgroup : list Trans)
      (final_fired_pre_group : list Trans)
      (finalm : list (Place * nat)),
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
  
  (** [stpn_fire_pre] returns no error if 
      all transition t in [pgroup] are referenced in [lneighbours]
      and if all neighbour places referenced in [lneighbours] are
      referenced in the markings [steadym] and [decreasingm]. *)
  
  Lemma stpn_fire_pre_no_error :
    forall (lneighbours : list (Trans * Neighbours))
           (pre test inhib : Weight) 
           (steadym : list (Place * nat)) 
           (decreasingm : list (Place * nat))
           (chronos : list (Trans * option Chrono))
           (pgroup : list Trans),
      incl pgroup (fst (split chronos)) ->
      incl pgroup (fst (split lneighbours)) ->
      (forall (t : Trans) (neighbours : Neighbours),
          In (t, neighbours) lneighbours ->
          (incl neighbours.(pre_pl) (fst (split decreasingm)) /\
           incl neighbours.(inhib_pl) (fst (split steadym)) /\
           incl neighbours.(test_pl) (fst (split steadym)))) ->
      exists v : (list Trans * list (Place * nat)),
        stpn_fire_pre lneighbours pre test inhib steadym decreasingm chronos pgroup = Some v.
  Proof.
    intros lneighbours pre test inhib steadym decreasingm chronos pgroup; intros.
    unfold spn_fire_pre.
    apply stpn_fire_pre_aux_no_error; [auto | auto | auto].
  Qed.
  
  (** ------------------------------------------------------------------ *)
  (** ------------------------------------------------------------------ *)
  
  (** Returns the list of pre-fired transitions and a marking.
   
      Applies [stpn_fire_pre] over all priority group of transitions. 
      Begins with initial marking; ends with half fired marking.  
      [pre_fired_transitions] is meant to be empty at first. *)
  
  Fixpoint stpn_map_fire_pre_aux
           (lneighbours : list (Trans * Neighbours))
           (pre test inhib : Weight)
           (steadym decreasingm : list (Place * nat))
           (chronos : list (Trans * option Chrono))
           (pre_fired_transitions : list Trans)
           (priority_groups : list (list Trans)) :
    option (list Trans * list (Place * nat)) :=
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
  
  (** Formal specification : stpn_map_fire_pre_aux *)
  
  Inductive StpnMapFirePreAux
            (lneighbours : list (Trans * Neighbours))
            (pre test inhib : Weight)
            (steadym decreasingm : list (Place * nat))
            (chronos : list (Trans * option Chrono))
            (pre_fired_transitions : list Trans) :
    list (list Trans) -> option (list Trans * list (Place * nat)) -> Prop :=
  | StpnMapFirePreAux_nil :
      StpnMapFirePreAux lneighbours pre test inhib steadym decreasingm chronos pre_fired_transitions []
                        (Some (pre_fired_transitions, decreasingm))
  | StpnMapFirePreAux_cons :
      forall (pgroup pre_fired_trs : list Trans)
             (decreasedm : list (Place * nat))
             (priority_groups : list (list Trans))
             (option_final_couple : option (list Trans * list (Place * nat))),
        StpnFirePre lneighbours pre test inhib steadym decreasingm chronos pgroup
                    (Some (pre_fired_trs, decreasedm)) ->
        StpnMapFirePreAux lneighbours pre test inhib steadym decreasedm chronos (pre_fired_transitions ++ pre_fired_trs)
                          priority_groups
                          option_final_couple ->
        StpnMapFirePreAux lneighbours pre test inhib steadym decreasingm chronos pre_fired_transitions
                          (pgroup :: priority_groups)
                          option_final_couple
  | StpnMapFirePreAux_err :
      forall (pgroup : list Trans)
             (priority_groups : list (list Trans)),
        StpnFirePre lneighbours pre test inhib steadym decreasingm chronos pgroup None ->
        StpnMapFirePreAux lneighbours pre test inhib steadym decreasingm chronos pre_fired_transitions
                          (pgroup :: priority_groups) None.

  (** Correctness proof : stpn_map_fire_pre_aux *)
  
  Theorem stpn_map_fire_pre_aux_correct :
    forall (lneighbours : list (Trans * Neighbours))
           (pre test inhib : Weight)
           (steadym decreasingm : list (Place * nat))
           (chronos : list (Trans * option Chrono))
           (priority_groups : list (list Trans))
           (pre_fired_transitions : list Trans)
           (option_final_couple : option (list Trans * list (Place * nat))),
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

  (** Completeness proof : stpn_map_fire_pre_aux *)
  
  Theorem stpn_map_fire_pre_aux_compl :
    forall (lneighbours : list (Trans * Neighbours))
           (pre test inhib : Weight)
           (steadym decreasingm : list (Place * nat))
           (chronos : list (Trans * option Chrono))           
           (priority_groups : list (list Trans))
           (pre_fired_transitions : list Trans)
           (option_final_couple : option (list Trans * list (Place * nat))),
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

  (** Proves that [stpn_map_fire_pre_aux] preserves
      the structure of the marking [decreasingm]
      passed as argument. *)

  Lemma stpn_map_fire_pre_aux_same_struct :
    forall (lneighbours : list (Trans * Neighbours))
           (pre test inhib : Weight)
           (steadym decreasingm : list (Place * nat))
           (chronos : list (Trans * option Chrono))
           (pre_fired_transitions : list Trans)
           (priority_groups : list (list Trans))
           (final_pre_fired : list Trans)
           (intermediatem : list (Place * nat)),
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

  (** If all transitions in [priority_groups] are in [lneighbours]
      then all transitions in [final_pre_fired] (returned by [stpn_map_fire_pre_aux]) 
      are in [lneighbours]. *)
  
  Lemma stpn_map_fire_pre_aux_final_fired_in_lneighbours :
    forall (lneighbours : list (Trans * Neighbours))
           (pre test inhib : Weight)
           (steadym decreasingm : list (Place * nat))
           (chronos : list (Trans * option Chrono))
           (pre_fired_transitions : list Trans)
           (priority_groups : list (list Trans))
           (final_pre_fired : list Trans)
           (intermediatem : list (Place * nat)),
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
                      chronos
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

  (** If all transitions in [priority_groups] are ref in [chronos]
      then all transitions in [final_pre_fired] (returned by [stpn_map_fire_pre_aux]) 
      are ref in [chronos]. *)
  
  Lemma stpn_map_fire_pre_aux_final_fired_in_chronos :
    forall (lneighbours : list (Trans * Neighbours))
      (pre test inhib : Weight)
      (steadym decreasingm : list (Place * nat))
      (chronos : list (Trans * option Chrono))
      (pre_fired_transitions : list Trans)
      (priority_groups : list (list Trans))
      (final_pre_fired : list Trans)
      (intermediatem : list (Place * nat)),
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
                      chronos
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

  (** [stpn_map_fire_pre_aux] returns no error if 
      forall pgroup of transitions in [priority_groups],
      transitions are referenced in [chronos] and
      transitions are referenced in [lneighbours] and
      neighbours places (of these transitions) are referenced 
      in markings [steadym] and [decreasingm]. *)
  
  Lemma stpn_map_fire_pre_aux_no_error :
    forall (lneighbours : list (Trans * Neighbours))
      (pre test inhib : Weight)
      (steadym decreasingm : list (Place * nat))
      (chronos : list (Trans * option Chrono))
      (priority_groups : list (list Trans))
      (pre_fired_transitions : list Trans),
      PriorityGroupsAreRefInChronos priority_groups chronos ->
      PriorityGroupsAreRefInLneighbours priority_groups lneighbours ->
      (forall (t : Trans) (neighbours : Neighbours),
          In (t, neighbours) lneighbours ->
          (incl neighbours.(pre_pl) (fst (split decreasingm)) /\
           incl neighbours.(inhib_pl) (fst (split steadym)) /\
           incl neighbours.(test_pl) (fst (split steadym)))) ->
      exists v : (list Trans * list (Place * nat)),
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
                                         chronos pgroup H2 H3 H1).
      intro; elim H4; intros; rewrite H5 in e0; inversion e0.
  Qed.
  
  (** ------------------------------------------------------------------ *)
  (** ------------------------------------------------------------------ *)
  
  (** Wrapper around stpn_map_fire_pre_aux function. 

      Updates the marking by consuming
      the tokens in pre-condition places. *)
  
  Definition stpn_map_fire_pre
             (lneighbours : list (Trans * Neighbours))
             (pre test inhib : Weight)
             (m : list (Place * nat))
             (chronos : list (Trans * option Chrono))
             (priority_groups : list (list Trans)) :
    option (list Trans * list (Place * nat)) :=
    stpn_map_fire_pre_aux lneighbours pre test inhib m m chronos [] priority_groups.

  Functional Scheme stpn_map_fire_pre_ind := Induction for stpn_map_fire_pre Sort Prop.
  
  (** Formal specification : stpn_map_fire_pre *)
  
  Inductive StpnMapFirePre
            (lneighbours : list (Trans * Neighbours))
            (pre test inhib : Weight)
            (m : list (Place * nat))
            (chronos : list (Trans * option Chrono))
            (priority_groups : list (list Trans)) :
    option (list Trans * list (Place * nat)) -> Prop :=
  | StpnMapFirePre_cons :
      forall (option_final_couple : option (list Trans * list (Place * nat))),
        StpnMapFirePreAux lneighbours pre test inhib m m chronos [] priority_groups
                          option_final_couple ->
        StpnMapFirePre lneighbours pre test inhib m chronos priority_groups option_final_couple.

  (** Correctness proof : stpn_map_fire_pre *)
  
  Theorem stpn_map_fire_pre_correct :
    forall (lneighbours : list (Trans * Neighbours))
           (pre test inhib : Weight)
           (m : list (Place * nat))
           (chronos : list (Trans * option Chrono))
           (priority_groups : list (list Trans))
           (option_final_couple : option (list Trans * list (Place * nat))),
      stpn_map_fire_pre lneighbours pre test inhib m chronos priority_groups = option_final_couple ->
      StpnMapFirePre lneighbours pre test inhib m chronos priority_groups option_final_couple.  
  Proof.
    intros lneighbours pre test inhib m chronos priority_groups option_final_couple H.
    apply StpnMapFirePre_cons.
    apply stpn_map_fire_pre_aux_correct.
    auto.
  Qed.

  (** Completeness proof : stpn_map_fire_pre *)
  
  Theorem stpn_map_fire_pre_compl :
    forall (lneighbours : list (Trans * Neighbours))
      (pre test inhib : Weight)
      (m : list (Place * nat))
      (chronos : list (Trans * option Chrono))
      (priority_groups : list (list Trans))
      (option_final_couple : option (list Trans * list (Place * nat))),
      StpnMapFirePre lneighbours pre test inhib m chronos priority_groups
                     option_final_couple ->
      stpn_map_fire_pre lneighbours pre test inhib m chronos priority_groups = option_final_couple.
  Proof.
    intros; elim H; intros.
    unfold stpn_map_fire_pre.
    apply stpn_map_fire_pre_aux_compl; auto.
  Qed.

  (** If all transitions in priority_groups are in lneighbours
      then all transitions in final_pre_fired (returned by stpn_map_fire_pre) 
      are in lneighbours. *)
  
  Lemma stpn_map_fire_pre_final_fired_in_lneighbours :
    forall (lneighbours : list (Trans * Neighbours))
           (pre test inhib : Weight)
           (m : list (Place * nat))
           (chronos : list (Trans * option Chrono))
           (priority_groups : list (list Trans))
           (final_pre_fired : list Trans)
           (intermediatem : list (Place * nat)),
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
    cut (forall t : Trans, In t [] -> In t (fst (split lneighbours))); intros.
    - generalize (stpn_map_fire_pre_aux_final_fired_in_lneighbours
                    lneighbours pre test inhib m m chronos [] priority_groups
                    final_pre_fired intermediatem
                    H H2 H0).
      intros.
      apply H3 in H1; auto.
    - elim H2.
  Qed.

  (** If all transitions in [priority_groups] are ref in [chronos]
      then all transitions in [final_pre_fired] (returned by [stpn_map_fire_pre]) 
      are ref in [chronos]. *)
  
  Lemma stpn_map_fire_pre_final_fired_in_chronos :
    forall (lneighbours : list (Trans * Neighbours))
      (pre test inhib : Weight)
      (m : list (Place * nat))
      (chronos : list (Trans * option Chrono))
      (priority_groups : list (list Trans))
      (final_pre_fired : list Trans)
      (intermediatem : list (Place * nat)),
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
    cut (forall t : Trans, In t [] -> In t (fst (split chronos))); intros.
    - generalize (stpn_map_fire_pre_aux_final_fired_in_chronos
                    lneighbours pre test inhib m m chronos [] priority_groups
                    final_pre_fired intermediatem
                    H H2 H0).
      intros.
      apply H3 in H1; auto.
    - elim H2.
  Qed.
  
  (** [stpn_map_fire_pre] returns no error if for all [pgroup] of transitions in [priority_groups] :
      
      - transitions are referenced in [chronos]
      - transitions are referenced in [lneighbours]
      - neighbours places (of these transitions) are referenced 
        in markings [steadym] and [decreasingm]. *)
  
  Lemma stpn_map_fire_pre_no_error :
    forall (lneighbours : list (Trans * Neighbours))
           (pre test inhib : Weight)
           (m : list (Place * nat))
           (chronos : list (Trans * option Chrono))
           (priority_groups : list (list Trans)),
      PriorityGroupsAreRefInChronos priority_groups chronos ->
      PriorityGroupsAreRefInLneighbours priority_groups lneighbours ->
      (forall (t : Trans) (neighbours : Neighbours),
          In (t, neighbours) lneighbours ->
          (incl neighbours.(pre_pl) (fst (split m)) /\
           incl neighbours.(inhib_pl) (fst (split m)) /\
           incl neighbours.(test_pl) (fst (split m)))) ->
      exists v : (list Trans * list (Place * nat)),
        stpn_map_fire_pre lneighbours pre test inhib m chronos priority_groups = Some v.
  Proof.
    intros lneighbours pre test inhib m chronos priority_groups.
    unfold stpn_map_fire_pre; intros.
    apply stpn_map_fire_pre_aux_no_error; [ auto | auto | auto ].
  Qed.

  (** Proves that [stpn_map_fire_pre] preserves the structure of the marking [m]
      passed in parameter. *)
  
  Lemma stpn_map_fire_pre_same_struct :
    forall (lneighbours : list (Trans * Neighbours))
      (pre test inhib : Weight)
      (m : list (Place * nat))
      (chronos : list (Trans * option Chrono))
      (priority_groups : list (list Trans))
      (final_pre_fired : list Trans)
      (intermediatem : list (Place * nat)),
      stpn_map_fire_pre lneighbours pre test inhib m chronos priority_groups =
      Some (final_pre_fired, intermediatem) ->
      MarkingHaveSameStruct m intermediatem.
  Proof.
    intros lneighbours pre test inhib m chronos priority_groups.
    functional induction (stpn_map_fire_pre lneighbours pre test inhib m chronos priority_groups)
               using stpn_map_fire_pre_ind; intros.
    apply stpn_map_fire_pre_aux_same_struct in H; auto.
  Qed.

  (** ------------------------------------------------------------------ *)
  (** ------------------------------------------------------------------ *)
  
  (** Returns a tuplet (fired transitions (at this cycle), final marking, final chronos).
             
      Raises an error ([None] value) if [stpn_map_fire_pre], [reset_all_chronos],
      [list_disabled], or [fire_post] return None.            
   
      This function has the same structure has [spn_fire], except
      that [stpn_fire] adds some instructions to reset chronos
      between the pre-firing and the post-firing phases. *)
  
  Definition stpn_fire  
             (lneighbours : list (Trans * Neighbours))
             (pre test inhib post : Weight)
             (m : list (Place * nat))
             (chronos : list (Trans * option Chrono))
             (transs : list Trans)
             (priority_groups : list (list Trans)) :
    option ((list Trans) * list (Place * nat) * (list (Trans * option Chrono))) :=
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
  
  (** Formal specification : stpn_fire *)
  
  Inductive StpnFire
            (lneighbours : list (Trans * Neighbours))
            (pre test inhib post : Weight)
            (m : list (Place * nat))
            (chronos : list (Trans * option Chrono))
            (transs : list Trans)
            (priority_groups : list (list Trans)) :
    option ((list Trans) * list (Place * nat) * (list (Trans * option Chrono))) ->
    Prop :=
  | StpnFire_fire_pre_err :
      StpnMapFirePre lneighbours pre test inhib m chronos priority_groups None ->
      StpnFire lneighbours pre test inhib post m chronos transs priority_groups None
  | StpnFire_reset_chronos_err1 :
      forall (pre_fired_transitions : list Trans)
             (intermediatem : list (Place * nat)),
        StpnMapFirePre lneighbours pre test inhib m chronos priority_groups
                       (Some (pre_fired_transitions, intermediatem)) ->
        ResetAllChronos chronos pre_fired_transitions None ->
        StpnFire lneighbours pre test inhib post m chronos transs priority_groups None
  | StpnFire_list_disabled_err :
      forall (pre_fired_transitions : list Trans)
             (intermediatem : list (Place * nat))
             (updated_chronos : list (Trans * option Chrono)),
        StpnMapFirePre lneighbours pre test inhib m chronos priority_groups
                       (Some (pre_fired_transitions, intermediatem)) ->
        ResetAllChronos chronos pre_fired_transitions (Some updated_chronos) ->
        ListDisabled lneighbours pre test inhib m transs None -> 
        StpnFire lneighbours pre test inhib post m chronos transs priority_groups None
  | StpnFire_reset_chronos_err2 :
      forall (pre_fired_transitions : list Trans)
             (intermediatem : list (Place * nat))
             (updated_chronos : list (Trans * option Chrono))
             (disabled_transs : list Trans),
        StpnMapFirePre lneighbours pre test inhib m chronos priority_groups
                       (Some (pre_fired_transitions, intermediatem)) ->
        ResetAllChronos chronos pre_fired_transitions (Some updated_chronos) ->
        ListDisabled lneighbours pre test inhib m transs (Some disabled_transs) -> 
        ResetAllChronos updated_chronos disabled_transs None ->
        StpnFire lneighbours pre test inhib post m chronos transs priority_groups None
  | StpnFire_fire_post_err :
      forall (pre_fired_transitions : list Trans)
             (intermediatem : list (Place * nat))
             (updated_chronos : list (Trans * option Chrono))
             (disabled_transs : list Trans)
             (final_chronos : list (Trans * option Chrono)),
        StpnMapFirePre lneighbours pre test inhib m chronos priority_groups
                       (Some (pre_fired_transitions, intermediatem)) ->
        ResetAllChronos chronos pre_fired_transitions (Some updated_chronos) ->
        ListDisabled lneighbours pre test inhib m transs (Some disabled_transs) -> 
        ResetAllChronos updated_chronos disabled_transs (Some final_chronos) ->
        FirePost lneighbours post intermediatem pre_fired_transitions None ->
        StpnFire lneighbours pre test inhib post m chronos transs priority_groups None
  | StpnFire_cons :
      forall (pre_fired_transitions : list Trans)
             (intermediatem : list (Place * nat))
             (updated_chronos : list (Trans * option Chrono))
             (disabled_transs : list Trans)
             (final_chronos : list (Trans * option Chrono))
             (finalm : list (Place * nat)),
        StpnMapFirePre lneighbours pre test inhib m chronos priority_groups
                       (Some (pre_fired_transitions, intermediatem)) ->
        ResetAllChronos chronos pre_fired_transitions (Some updated_chronos) ->
        ListDisabled lneighbours pre test inhib m transs (Some disabled_transs) -> 
        ResetAllChronos updated_chronos disabled_transs (Some final_chronos) ->
        FirePost lneighbours post intermediatem pre_fired_transitions (Some finalm) ->
        StpnFire lneighbours pre test inhib post m chronos transs priority_groups
                 (Some (pre_fired_transitions, finalm, final_chronos)).

  (** Correctness proof : stpn_fire *)
  
  Theorem stpn_fire_correct :
    forall (lneighbours : list (Trans * Neighbours))
           (pre test inhib post : Weight)
           (m : list (Place * nat))
           (chronos : list (Trans * option Chrono))
           (transs : list Trans)
           (priority_groups : list (list Trans))
           (opt_final_tuplet : option ((list Trans) *
                                       list (Place * nat) *
                                       (list (Trans * option Chrono)))),
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

  (** Completeness proof : stpn_fire *)
  
  Theorem stpn_fire_compl :
    forall (lneighbours : list (Trans * Neighbours))
           (pre test inhib post : Weight)
           (m : list (Place * nat))
           (chronos : list (Trans * option Chrono))
           (transs : list Trans)
           (priority_groups : list (list Trans))
           (opt_final_tuplet : option ((list Trans) *
                                       list (Place * nat) *
                                       (list (Trans * option Chrono)))),
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

  (** Proves that [stpn_fire] preserves the structure of the marking [m]
      passed as argument. *)
  
  Lemma stpn_fire_same_struct_marking :
    forall (lneighbours : list (Trans * Neighbours))
           (pre test inhib post : Weight)
           (m : list (Place * nat))
           (chronos : list (Trans * option Chrono))
           (transs : list Trans)
           (priority_groups : list (list Trans))
           (fired_transitions : list (Trans))
           (newm : list (Place * nat))
           (new_chronos : list (Trans * option Chrono)),
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

  (** Proves that stpn_fire preserves the structure of the [chronos] list. *)
  
  Lemma stpn_fire_same_struct_chronos :
    forall (lneighbours : list (Trans * Neighbours))
           (pre test inhib post : Weight)
           (m : list (Place * nat))
           (chronos : list (Trans * option Chrono))
           (transs : list Trans)
           (priority_groups : list (list Trans))
           (fired_transitions : list (Trans))
           (newm : list (Place * nat))
           (new_chronos : list (Trans * option Chrono)),
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

  (** If all chrono in [chronos] are well-formed, then [stpn_fire] 
      returns a list [new_chronos] of well-formed chronos. *)
  
  Lemma stpn_fire_well_formed_chronos :
    forall (lneighbours : list (Trans * Neighbours))
      (pre test inhib post : Weight)
      (m : list (Place * nat))
      (chronos : list (Trans * option Chrono))
      (transs : list Trans)
      (priority_groups : list (list Trans))
      (fired_transitions : list (Trans))
      (newm : list (Place * nat))
      (new_chronos : list (Trans * option Chrono)),
      (forall chrono : Chrono,
          In (Some chrono) (snd (split chronos)) -> IsWellFormedChrono chrono) ->
      stpn_fire lneighbours pre test inhib post m chronos transs priority_groups =
      Some (fired_transitions, newm, new_chronos) ->
      (forall chrono' : Chrono,
          In (Some chrono') (snd (split new_chronos)) -> IsWellFormedChrono chrono').
  Proof.
    intros lneighbours pre test inhib post m chronos transs priority_groups.
    functional induction (stpn_fire lneighbours pre test inhib post m chronos transs
                                    priority_groups)
               using stpn_fire_ind; intros.
    (* GENERAL CASE (all went well) *)
    (* We need to prove that reset_all_chronos return well-formed chronos. *)
    - generalize (reset_all_chronos_well_formed_chronos chronos pre_fired_transitions updated_chronos H e1); intro.
      generalize (reset_all_chronos_well_formed_chronos updated_chronos disabled_transs final_chronos H2 e3); intro.
      injection H0; intros.
      rewrite <- H4 in H1; apply (H3 chrono' H1).
    (* CASE fire_post returns None, impossible. *)
    - inversion H0.
    (* CASE reset_all_chronos returns None, impossible. *)
    - inversion H0.
    (* CASE list_disabled returns None, impossible. *)
    - inversion H0.
    (* CASE reset_all_chronos returns None, impossible. *)
    - inversion H0.
    (* CASE stpn_map_fire_pre returns None, impossible. *)
    - inversion H0.      
  Qed.
  
  (** Proves that [stpn_fire] returns no error if :
      
      - All transitions in [transs] are ref in [chronos] and [lneighbours].
      - All pgroups in [priority_groups] are ref in [chronos] and [lneighbours].
      - All places in [lneighbours] are ref in [m]. *)
  
  Lemma stpn_fire_no_error :
    forall (lneighbours : list (Trans * Neighbours))
      (pre test inhib post : Weight)
      (m : list (Place * nat))
      (chronos : list (Trans * option Chrono))
      (transs : list Trans)
      (priority_groups : list (list Trans)),
      incl transs (fst (split chronos)) ->
      incl transs (fst (split lneighbours)) ->
      PriorityGroupsAreRefInChronos priority_groups chronos ->
      PriorityGroupsAreRefInLneighbours priority_groups lneighbours ->
      (forall (t : Trans) (neighbours : Neighbours),
          In (t, neighbours) lneighbours ->
          (incl neighbours.(pre_pl) (fst (split m)) /\
           incl neighbours.(inhib_pl) (fst (split m)) /\
           incl neighbours.(test_pl) (fst (split m)))) ->
      (forall (t : Trans) (neighbours : Neighbours),
          In (t, neighbours) lneighbours ->
          incl neighbours.(post_pl) (fst (split m))) ->
      exists v : (list Trans * list (Place * nat) * list (Trans * option Chrono)),
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

(** * Stpn cycle evolution *)

(*! ==================== !*)
(*! Stpn CYCLE EVOLUTION !*)
(*! ==================== !*)

Section AnimateStpn.
  
  (** Returns the resulting Petri net after the firing of all sensitized
      transitions - with right chrono value - in [stpn].
      
      Also returns the list of fired transitions. *)
  
  Definition stpn_cycle (stpn : Stpn) : option ((list Trans) * Stpn)  :=
    match stpn with
    | mk_Stpn
        chronos
        (mk_Spn places transs pre post test inhib marking priority_groups lneighbours) =>
      (* Lists all sensitized transitions. *)
      match list_sensitized lneighbours pre test inhib marking transs with
      | Some sensitized_transs =>           
        (* Increments all chronos for the sensitized transitions. *)
        match increment_all_chronos chronos sensitized_transs with
        | Some updated_chronos =>
          match stpn_fire lneighbours pre test inhib post marking updated_chronos transs priority_groups with
          | Some (fired_transitions, nextm, next_chronos) =>
            Some (fired_transitions,
                  (mk_Stpn
                     next_chronos
                     (mk_Spn places transs pre post test inhib nextm priority_groups lneighbours)))
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
  
  (** Formal specification : stpn_cycle *)
  
  Inductive StpnCycle (stpn : Stpn) : option ((list Trans) * Stpn) -> Prop :=
  | StpnCycle_list_sensitized_err :
      forall (chronos : list (Trans * option Chrono))
             (places : list Place)
             (transs : list Trans)
             (pre post test inhib : Weight)
             (marking : list (Place * nat))
             (priority_groups : list (list Trans))
             (lneighbours : list (Trans * Neighbours)),
        stpn = (mk_Stpn
                  chronos
                  (mk_Spn places transs pre post test inhib marking priority_groups lneighbours)) ->
        ListSensitized lneighbours pre test inhib marking transs None ->
        StpnCycle stpn None
  | StpnCycle_increment_chronos_err :
      forall (chronos : list (Trans * option Chrono))
             (places : list Place)
             (transs : list Trans)
             (pre post test inhib : Weight)
             (marking : list (Place * nat))
             (priority_groups : list (list Trans))
             (lneighbours : list (Trans * Neighbours))
             (sensitized_transs : list Trans),
        stpn = (mk_Stpn
                  chronos
                  (mk_Spn places transs pre post test inhib marking priority_groups lneighbours)) ->
        ListSensitized lneighbours pre test inhib marking transs (Some sensitized_transs) ->
        IncrementAllChronos chronos sensitized_transs None ->
        StpnCycle stpn None
  | StpnCycle_fire_err :
      forall (chronos : list (Trans * option Chrono))
             (places : list Place)
             (transs : list Trans)
             (pre post test inhib : Weight)
             (marking : list (Place * nat))
             (priority_groups : list (list Trans))
             (lneighbours : list (Trans * Neighbours))
             (sensitized_transs : list Trans)
             (updated_chronos : list (Trans * option Chrono)),
        stpn = (mk_Stpn
                  chronos
                  (mk_Spn places transs pre post test inhib marking priority_groups lneighbours)) ->
        ListSensitized lneighbours pre test inhib marking transs (Some sensitized_transs) ->
        IncrementAllChronos chronos sensitized_transs (Some updated_chronos) ->
        StpnFire lneighbours pre test inhib post marking updated_chronos transs priority_groups None -> 
        StpnCycle stpn None
  | StpnCycle_cons :
      forall (chronos : list (Trans * option Chrono))
        (places : list Place)
        (transs : list Trans)
        (pre post test inhib : Weight)
        (marking : list (Place * nat))
        (priority_groups : list (list Trans))
        (lneighbours : list (Trans * Neighbours))
        (sensitized_transs : list Trans)
        (updated_chronos : list (Trans * option Chrono))
        (fired_transitions : list Trans)
        (nextm : list (Place * nat))
        (next_chronos : list (Trans * option Chrono)),
        stpn = (mk_Stpn
                  chronos
                  (mk_Spn places transs pre post test inhib marking priority_groups lneighbours)) ->
        ListSensitized lneighbours pre test inhib marking transs (Some sensitized_transs) ->
        IncrementAllChronos chronos sensitized_transs (Some updated_chronos) ->
        StpnFire lneighbours pre test inhib post marking updated_chronos transs priority_groups
                 (Some (fired_transitions, nextm, next_chronos)) -> 
        StpnCycle stpn (Some (fired_transitions,
                              (mk_Stpn
                                 next_chronos
                                 (mk_Spn places transs pre post test inhib nextm priority_groups lneighbours)))).

  (** Correctness proof : stpn_cycle *)
  
  Theorem stpn_cycle_correct :
    forall (stpn : Stpn)
      (opt_final_couple : option ((list Trans) * Stpn)),
      stpn_cycle stpn = opt_final_couple ->
      StpnCycle stpn opt_final_couple.
  Proof.
    intro stpn.
    functional induction (stpn_cycle stpn) using stpn_cycle_ind; intros.
    (* General case, all went well. *)
    - rewrite <- H; apply StpnCycle_cons with (chronos := chronos)
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
                                                  (chronos := chronos)
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
                                                               (chronos := chronos)
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
                                                               (chronos := chronos)
                                                               (marking := marking).
      + auto.
      + apply list_sensitized_correct; auto.
  Qed.

  (** Completeness proof : stpn_cycle *)
  
  Theorem stpn_cycle_compl :
    forall (stpn : Stpn)
           (opt_final_couple : option ((list Trans) * Stpn)),
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

  (** For all [Stpn] with properties [NoUnknownInPriorityGroups]
      and [NoUnknownTransInChronos] then transitions
      in [Stpn.(priority_groups)] are referenced in [Stpn.(chronos)].
          
      Useful to apply [stpn_fire_no_error] while proving [stpn_cycle_no_error]. *)
  
  Lemma priority_groups_in_chronos :
    forall (stpn : Stpn),
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
  
  (** For all [Stpn] verifying the predicate [IsWellDefinedStpn],
      [stpn_cycle] returns no error (always returns Some value). *)
  
  Theorem stpn_cycle_no_error :
    forall (stpn : Stpn),
      IsWellDefinedStpn stpn ->
      exists v : ((list Trans) * Stpn),
        stpn_cycle stpn = Some v.
  Proof.
    unfold IsWellDefinedStpn; intro.
    functional induction (stpn_cycle stpn) using stpn_cycle_ind;
      set (stpn := {| chronos := chronos;
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
       * from the properties embedded in IsWellDefinedStpn.
       *)
      assert (H' : incl (Spn.transs stpn) (fst (split (Stpn.chronos stpn))))
        by (rewrite H2; unfold incl; intros ; auto).
      assert (H'' : incl (Spn.transs stpn) (fst (split (Spn.lneighbours stpn))))
        by (rewrite H9; unfold incl; intros ; auto).
      generalize (priority_groups_in_chronos stpn H4 H2); intro.
      generalize (priority_groups_in_lneighbours stpn H4 H9); intro.
      generalize (pre_places_in_marking stpn H12 H8); intro.
      generalize (post_places_in_marking stpn H12 H8); intro.
      (* Then, ensures that chronos and updated_chronos have same structure. *)
      generalize (increment_all_chronos_same_struct
                    chronos sensitized_transs updated_chronos e2); intros.
      (* Rewrites chronos with updated_chronos in some hypotheses.  *)
      unfold ChronosHaveSameStruct in H14.
      simpl in H'.
      rewrite H15 in H'.
      simpl in H.
      unfold PriorityGroupsAreRefInChronos in H.
      rewrite H15 in H.
      (* Finally, applies lemma stpn_fire_no_error. *)
      generalize (stpn_fire_no_error
                    lneighbours pre test inhib post marking updated_chronos transs priority_groups
                    H' H'' H H11 H13 H14).
      intro; elim H16; intros.
      rewrite H17 in e3.
      inversion e3.
    (* CASE increment_all_chronos returns None, impossible
     * regarding the hypotheses. 
     *)
    - unfold NoUnknownTransInChronos in H0.
      generalize (list_sensitized_incl_transs
                    lneighbours pre test inhib marking transs sensitized_transs e1); intro.
      assert (H' : incl (Spn.transs stpn) (fst (split (Stpn.chronos stpn))))
        by (rewrite H2; unfold incl; intros ; auto).
      generalize (incl_tran H H'); intro.
      generalize (increment_all_chronos_no_error
                    chronos sensitized_transs H11); intro.
      elim H13; intros.
      rewrite H14 in e2; inversion e2.
    (* CASE list_sensitized returns None, impossible
     * regarding the hypotheses. 
     *)
    - unfold NoUnknownTransInLNeighbours in H9.
      assert (H'' : incl (Spn.transs stpn) (fst (split (Spn.lneighbours stpn))))
        by (rewrite H9; unfold incl; intros ; auto).
      generalize (pre_places_in_marking stpn H12 H8); intro.
      unfold incl in H.
      generalize (list_sensitized_no_error
                    lneighbours pre test inhib marking transs
                    H'' H); intro.
      elim H11; intros; rewrite H13 in e1; inversion e1.
  Qed.

  (** For all [stpn] verifying the property [IsWellDefinedStpn],
      [stpn_cycle] returns a new Stpn [next_stpn] verifying the relation
      [IsWellDefinedStpn]. *)
  
  Theorem stpn_cycle_well_structured :
    forall (stpn : Stpn)
      (fired_transitions : list Trans)
      (next_stpn : Stpn),
      IsWellDefinedStpn stpn ->
      stpn_cycle stpn = Some (fired_transitions, next_stpn) ->
      IsWellDefinedStpn next_stpn.
  Proof.
    intro.
    functional induction (stpn_cycle stpn) using stpn_cycle_ind; intros.
    (* GENERAL CASE. *)
    - unfold IsWellDefinedStpn; unfold IsWellStructuredSpn.
      unfold IsWellDefinedStpn in H; unfold IsWellStructuredSpn in H.
      injection H0; clear H0; intros.
      unfold NoUnmarkedPlace in H.
      unfold NoUnknownTransInChronos in H.
      (*  
       * We need to ensure that stpn_fire preserves the structure
       * of marking and chronos, and preserves the fact that chronos
       * are well-formed.
       *)
      
      (* stpn_fire returns well-formed chronos. *)
      (* Hypothesis H2 in needed to apply stpn_fire_well_formed_chronos. *)
      elim H; intros; clear H3; unfold AreWellFormedChronos in H2; simpl in H2.
      generalize (increment_all_chronos_well_formed_chronos
                    chronos sensitized_transs updated_chronos H2 e2); intro.
      generalize (stpn_fire_well_formed_chronos
                    lneighbours pre test inhib post
                    marking updated_chronos transs priority_groups
                    fired_transitions nextm next_chronos H3 e3); intro.
      (* stpn_fire preserves marking structure. *)
      generalize (stpn_fire_same_struct_marking
                    lneighbours pre test inhib post
                    marking updated_chronos transs priority_groups
                    fired_transitions nextm next_chronos e3); intro.
      (* increment_all_chronos and stpn_fire preserves chronos structure *)
      generalize (increment_all_chronos_same_struct
                    chronos sensitized_transs updated_chronos e2); intro.
      generalize (stpn_fire_same_struct_chronos
                    lneighbours pre test inhib post
                    marking updated_chronos transs priority_groups
                    fired_transitions nextm next_chronos e3); intro.
  
      (*  
       * Then, we need to rewrite chronos with updated_chronos, and
       * marking with nextm.
       *)
      unfold MarkingHaveSameStruct in H5;
        unfold ChronosHaveSameStruct in H6;
        unfold ChronosHaveSameStruct in H7.
      simpl in H.
      rewrite H5 in H.
      rewrite H6 in H.
      rewrite H7 in H.
      unfold NoUnknownTransInChronos;
        unfold NoUnmarkedPlace;
        unfold AreWellFormedChronos.
      (* Conjunction of H2 and H8 to obtain a hypothesis close to the goal. *)
      elim H; clear H; intros.
      generalize (conj H2 H8); intro.
      (* Rewrite and symplify goal to match last hypothesis. *)
      rewrite <- H0; simpl; auto.
    (* CASE stpn_fire returns None. *)
    - inversion H0.
    (* CASE increment_all_chronos returns None. *)
    - inversion H0.
    (* CASE list_sensitized returns None. *)
    - inversion H0.
  Qed.

  (** -------------------------------------------------------------------------- *)
  (** -------------------------------------------------------------------------- *)
  
  (*! ========================================= !*)
  (*! ====== ANIMATING DURING N CYCLES ======== !*)
  (*! ========================================= !*)
  
  (** Returns the list of (transitions_fired(i), Stpn(i)) for each cycle i, 
      from 0 to n, representing the evolution of the Petri net [stpn]. *)
  
  Fixpoint stpn_animate_aux 
           (stpn : Stpn)
           (n : nat)
           (stpn_evolution : list (list Trans * Stpn)) :
    option (list (list Trans * Stpn)) :=
    match n with
    (* Base case, returns the list storing the evolution. *)
    | O => Some stpn_evolution
    | S n' =>
      match (stpn_cycle stpn) with
      (* Adds a new evolution step at the end of the list. *)
      | Some (fired_trans_at_n, stpn_at_n) =>
        stpn_animate_aux stpn_at_n n' (stpn_evolution ++ [(fired_trans_at_n, stpn_at_n)])
      (* Error, stpn_cycle failed!!! *)
      | None => None
      end
    end.

  Functional Scheme stpn_animate_aux_ind := Induction for stpn_animate_aux Sort Prop.
  
  (** Formal specification : stpn_animate_aux *)

  Inductive StpnAnimateAux (stpn : Stpn) :
    nat ->
    list (list Trans * Stpn) ->
    option (list (list Trans * Stpn) )->
    Prop :=
  | StpnAnimateAux_0 :
      forall (stpn_evolution : list (list Trans * Stpn)),
        StpnAnimateAux stpn 0 stpn_evolution (Some stpn_evolution) 
  | StpnAnimateAux_cons :
      forall (n : nat)
             (fired_trans_at_n : list Trans)
             (stpn_at_n : Stpn)
             (stpn_evolution : list (list Trans * Stpn))
             (opt_evolution : option (list (list Trans * Stpn))),
        StpnCycle stpn (Some (fired_trans_at_n, stpn_at_n)) ->
        StpnAnimateAux stpn_at_n
                       n
                       (stpn_evolution ++ [(fired_trans_at_n, stpn_at_n)])
                       opt_evolution ->
        StpnAnimateAux stpn
                       (S n)
                       stpn_evolution
                       opt_evolution
  | StpnAnimateAux_err :
      forall (n : nat)
             (stpn_evolution : list (list Trans * Stpn)),
        StpnCycle stpn None ->
        StpnAnimateAux stpn (S n) stpn_evolution None.
  
  (** Correctness proof : stpn_animate_aux *)

  Theorem stpn_animate_aux_correct :
    forall (stpn :Stpn)
           (n : nat)
           (stpn_evolution : list (list Trans * Stpn))
           (opt_evolution : option (list (list Trans * Stpn))),
      stpn_animate_aux stpn n stpn_evolution = opt_evolution ->
      StpnAnimateAux stpn n stpn_evolution opt_evolution.
  Proof.                                                                                
    intros stpn n stpn_evolution.
    functional induction (stpn_animate_aux stpn n stpn_evolution) using stpn_animate_aux_ind; intros.
    (* Case n = 0 *)
    - rewrite <- H; apply StpnAnimateAux_0.
    (* General case *)
    - intros; rewrite <- H.
      apply StpnAnimateAux_cons with (fired_trans_at_n := fired_trans_at_n)
                                  (stpn_at_n := stpn_at_n).
      + apply stpn_cycle_correct in e0; auto.
      + apply IHo; auto.
    (* Error case, stpn_cycle returns None. *)
    - rewrite <- H; apply StpnAnimateAux_err.
      apply stpn_cycle_correct in e0; auto.
  Qed.

  (** Completeness proof : stpn_animate_aux *)

  Theorem stpn_animate_aux_compl :
    forall (stpn : Stpn)
           (n : nat)
           (stpn_evolution : list (list Trans * Stpn))
           (opt_evolution : option (list (list Trans * Stpn))),
      StpnAnimateAux stpn n stpn_evolution opt_evolution ->
      stpn_animate_aux stpn n stpn_evolution = opt_evolution.
  Proof.
    intros; elim H; intros.
    (* Case StpnAnimateAux_0 *)
    - simpl; auto.
    (* Case StpnAnimateAux_cons *)
    - simpl. apply stpn_cycle_compl in H0; rewrite H0.
      rewrite H2; auto.
    (* Case StpnAnimateAux_err *)
    - apply stpn_cycle_compl in H0.
      simpl.
      rewrite H0; auto.
  Qed.

  (** For all [Stpn] verifying the property [IsWellDefinedStpn], and for all number [n] 
      of evolution cycles, [stpn_animate_aux] returns no error. *)
  Theorem stpn_animate_aux_no_error :
    forall (stpn : Stpn)
           (n : nat)
           (stpn_evolution : list (list Trans * Stpn)),
      IsWellDefinedStpn stpn ->
      exists (v : list (list Trans * Stpn)),
        stpn_animate_aux stpn n stpn_evolution = Some v.
  Proof.
    do 3 intro.
    functional induction (stpn_animate_aux stpn n stpn_evolution)
               using stpn_animate_aux_ind;
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

  (** For all well-structured [Stpn] passed to [stpn_animate_aux], and for all list of well-structured [Stpn]
      stpn_evolution, the resulting list is only composed of well-structured [Stpn]. *)
  
  Theorem stpn_animate_aux_well_structured :
    forall (stpn : Stpn)
           (n : nat)
           (stpn_evolution final_stpn_evolution : list (list Trans * Stpn)),
      IsWellDefinedStpn stpn ->
      (forall stpn' : Stpn, In stpn' (snd (split stpn_evolution)) -> IsWellDefinedStpn stpn') ->
      stpn_animate_aux stpn n stpn_evolution = Some final_stpn_evolution ->
      forall (stpn'' : Stpn), In stpn'' (snd (split final_stpn_evolution)) -> IsWellDefinedStpn stpn''.
  Proof.
    do 3 intro.
    functional induction (stpn_animate_aux stpn n stpn_evolution) using stpn_animate_aux_ind; intros.
    - injection H1; intros.
      rewrite <- H3 in H2.
      apply (H0 stpn'' H2).
    - apply IHo with (final_stpn_evolution := final_stpn_evolution).
      + generalize (stpn_cycle_well_structured stpn fired_trans_at_n stpn_at_n H e0); intro; auto.
      + intros.
        rewrite snd_split_app in H3.
        apply in_app_or in H3.
        elim H3; intros.
        -- apply (H0 stpn' H4).
        -- simpl in H4; elim H4; intros;
           [generalize (stpn_cycle_well_structured stpn fired_trans_at_n stpn_at_n H e0); intro;
            rewrite H5 in H6; assumption
           | elim H5].           
      + auto.
      + auto.
    - inversion H1.
  Qed.

  (** For all well-structured [Stpn] passed to [stpn_animate_aux], and for all [n], number 
      of evolution cycles, the length of the resulting [final_stpn_evolution] list
      is equal to the number of evolution cycles plus the length of the [stpn_evolution] 
      list passed in argument. *)
  
  Theorem stpn_animate_aux_preserves_cycles :
    forall (stpn : Stpn)
           (n : nat)
           (stpn_evolution final_stpn_evolution : list (list Trans * Stpn)),
      IsWellDefinedStpn stpn ->
      stpn_animate_aux stpn n stpn_evolution = Some final_stpn_evolution ->
      n + length stpn_evolution = length final_stpn_evolution.
  Proof.
    do 3 intro.
    functional induction (stpn_animate_aux stpn n stpn_evolution) using stpn_animate_aux_ind; intros.
    - injection H0; intros; rewrite H1; simpl; auto.
    - generalize (stpn_cycle_well_structured stpn fired_trans_at_n stpn_at_n H e0); intro.
      generalize (IHo final_stpn_evolution H1 H0); intro.
      rewrite <- H2.
      rewrite app_length.
      simpl.
      rewrite Nat.add_1_r.
      auto.
    - inversion H0.
  Qed.

  (** ------------------------------------------------------------------------------- *)
  (** ------------------------------------------------------------------------------- *)

  (** Wrapper function around stpn_animate_aux. Here, stpn_evolution is initialized to nil. *)
  
  Definition stpn_animate (stpn : Stpn) (n : nat) :
    option (list (list Trans * Stpn)) := stpn_animate_aux stpn n [].

  (** Formal specification : stpn_animate *)
  
  Inductive StpnAnimate (stpn : Stpn) (n : nat) : option (list (list Trans * Stpn)) -> Prop :=
  | StpnAnimate_cons :
      forall (opt_stpn_evolution : option (list (list Trans * Stpn))),
        StpnAnimateAux stpn n [] opt_stpn_evolution ->
        StpnAnimate stpn n opt_stpn_evolution.

  (** Correctness proof : stpn_animate *)
  
  Theorem stpn_animate_correct :
    forall (stpn : Stpn) (n : nat) (opt_stpn_evolution : option (list (list Trans * Stpn))),
      stpn_animate stpn n = opt_stpn_evolution ->
      StpnAnimate stpn n opt_stpn_evolution.
  Proof.
    unfold stpn_animate.
    intros.
    apply StpnAnimate_cons; apply stpn_animate_aux_correct in H; auto.
  Qed.

  (** Completeness proof : stpn_animate *)
  
  Theorem stpn_animate_compl :
    forall (stpn : Stpn) (n : nat) (opt_stpn_evolution : option (list (list Trans * Stpn))),
      StpnAnimate stpn n opt_stpn_evolution ->
      stpn_animate stpn n = opt_stpn_evolution.
  Proof.
    unfold stpn_animate.
    intros.
    elim H; apply stpn_animate_aux_compl; auto.
  Qed.

  (** For all [Stpn] verifying the property [IsWellDefinedStpn],
      and for all number [n] of evolution cycles, [stpn_animate] returns no error. *)
  
  Theorem stpn_animate_no_error :
    forall (stpn : Stpn)
           (n : nat),
      IsWellDefinedStpn stpn ->
      exists (v : list ((list Trans) * Stpn)),
        stpn_animate stpn n = Some v.
  Proof.
    unfold stpn_animate.
    intros.
    generalize (stpn_animate_aux_no_error stpn n [] H); intro.
    elim H0; intros.
    rewrite H1.
    exists x; auto.
  Qed.

  (** For all well-structured [Stpn] passed to [stpn_animate], the resulting evolution 
      list is only composed of well-structured [Stpn]. *)
  
  Theorem stpn_animate_well_structured :
    forall (stpn : Stpn)
           (n : nat)
           (stpn_evolution : list (list Trans * Stpn)),
      IsWellDefinedStpn stpn ->
      stpn_animate stpn n = Some stpn_evolution ->
      forall (stpn' : Stpn), In stpn' (snd (split stpn_evolution)) -> IsWellDefinedStpn stpn'.
  Proof.
    unfold stpn_animate.
    intros.
    (* We need this hypothesis to apply stpn_animate_aux_well_structured. *)
    assert (H' : forall (stpn' : Stpn), In stpn' [] -> IsWellDefinedStpn stpn')
      by (intros; elim H2).
    generalize (stpn_animate_aux_well_structured stpn n [] stpn_evolution H H' H0); intros.
    apply H2; assumption.
  Qed.

  (** For all well-structured [Stpn] passed to [stpn_animate], and for all [n], number 
      of evolution cycles, the length of the resulting [final_stpn_evolution] list
      is equal to the number of evolution cycles plus the length of the [stpn_evolution] 
      list passed in argument. *)
  
  Theorem stpn_animate_preserves_cycles :
    forall (stpn : Stpn)
           (n : nat)
           (stpn_evolution : list (list Trans * Stpn)),
      IsWellDefinedStpn stpn ->
      stpn_animate stpn n = Some stpn_evolution ->
      n = length stpn_evolution.
  Proof.
    unfold stpn_animate; intros.
    generalize (stpn_animate_aux_preserves_cycles stpn n [] stpn_evolution H H0); intros.
    rewrite Nat.add_0_r in H1.
    assumption.
  Qed.
  
End AnimateStpn.
