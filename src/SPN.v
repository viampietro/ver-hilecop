Require Export Arith Omega List Bool Bool.Sumbool Bool.Bool FunInd Coq.Lists.ListDec.
Export ListNotations.

(******************************************************************)
(* Syntax of generalized (weight on transitions > or equal to 1), *)
(* extended (test and inhibiting edges) Petri nets.               *)
(******************************************************************)

(* A place is identified by an index which is unique. *)
Inductive place_type : Set :=
| mk_place : nat -> place_type.

(* Simpler notation for mk_place, strong binding level. *)
Notation "'pl' nat" := (mk_place nat) (at level 100, no associativity).

(* A transition is identified by an index which is unique. *)
Inductive trans_type : Set :=
| mk_trans : nat -> trans_type.

(* Simpler notation for mk_transition, strong binding level. *)
Notation "'tr' nat" := (mk_trans nat) (at level 100, no associativity).

(* There are 4 kinds of edges : pre, post, inhib, test 
 * along with "some" positive weight (default is 1 usually).       
 *)

(* Set of natural numbers that are strictly over zero.   *)
(* The second member, posi, must be a lemma of the form "n > 0" *)
Structure nat_star : Set := mk_nat_star { int : nat ; posi : int > 0 }.

(* A given edge, either reaching in or coming out of a place,
 * has some weight over 0 or no weight at all, meaning it
 * doesn't exist (which is why weight_type returns a option nat_star 
 * that can take the None value). 
 *)
Definition weight_type := trans_type -> place_type -> option nat_star.

(* The marking in a Petri net is represented as
 * a list of couples (index, nboftokens), where index is
 * the index of a place in the Petri net, and nboftokens
 * is the number of tokens currently assoicated to the place.
 *)
Definition marking_type := list (nat * nat).

(* Defines a structure,
 * where index corresponds to a transition index
 * and the other attributes correspond to its
 * pre, test, inhib and post neighbour places.
 *)
Structure neighbours_type : Set := mk_neighbours {
                                       index : nat;
                                       pre_pl : list place_type;
                                       test_pl : list place_type;
                                       inhib_pl : list place_type;
                                       post_pl : list place_type
                                     }.

(*******************************************************)
(*** Defines the structure of Synchronous Petri Nets ***)
(*******************************************************)
Structure SPN : Set :=
  mk_SPN {
      
      (*==== ATTRIBUTES ====*)
      
      places : list place_type;
      transs : list trans_type;
      pre : weight_type;
      post : weight_type;
      test : weight_type;
      inhib : weight_type;
      marking : marking_type;

      (* Each list of transitions contained in priority_groups is 
       * a priority-ordered list of transitions.
       * Defines priority relations between transitions,
       * necessary to obtain a deterministic Petri net.*)
      priority_groups : list (list trans_type);

      (* Contains the list of pre, test, inhib and post places 
       * associated with each transition of the SPN. *)
      lneighbours : list neighbours_type;

      (*==== LEMMAS ====*)
      
      (*** Properties on places and transitions ***)
      nodup_places : NoDup places;
      nodup_transs : NoDup transs;

      (*** Properties on priority_groups ***)

      (* For all transition t, t is in transs iff 
       * there exists a group in priority_groups containing t. *)
      no_unknown_in_priority_groups :
        forall (t : trans_type),
          In t transs <->
          exists group : list trans_type,
            In group priority_groups /\ In t group;

      (* For all transition t in one of the group of
       * priority_groups, t is contained in only one
       * group of priority_groups. *)
      no_intersect_in_priority_groups :
        forall (group group' : list trans_type),
          In group priority_groups /\
          In group' priority_groups /\
          group <> group' ->
          forall (t : trans_type), In t group -> ~In t group';
      
      (*** Properties on lneighbours ***)
      nodup_lneighbours : NoDup lneighbours;
      
      (* For all place p, p is in places iff 
       * p is in the neighbourhood of at least one transition. *)
      no_isolated_or_unknown_place : 
        forall (p : place_type),
          In p places <->
          exists (neighbours : neighbours_type),
            In neighbours lneighbours /\  
            (In p (pre_pl neighbours)) \/
            (In p (test_pl neighbours)) \/
            (In p (inhib_pl neighbours)) \/
            (In p (post_pl neighbours));

      (* For all transition (tr i), (tr i) is in transs iff 
       * t is connected to at least one place. *)
      no_isolated_or_unknown_trans :
        forall (i : nat),
          In (tr i) transs <->
          exists (pre_pl test_pl inhib_pl post_pl : list place_type),
            In (mk_neighbours i pre_pl test_pl inhib_pl post_pl) lneighbours /\
            (pre_pl <> [] \/ test_pl <> [] \/ inhib_pl <> [] \/ post_pl <> []);

      (* For all neighbours, if neighbours is in lneighbours then
       * there is no neighbours' in lneighbours with the same index
       * as neighbours. *)
      uniq_index_lneighbours :
        forall (neighbours : neighbours_type),
          In neighbours lneighbours ->
          ~exists (neighbours' : neighbours_type),
              In neighbours' lneighbours /\
              neighbours.(index) = neighbours'.(index) /\
              neighbours <> neighbours';
      
      (*** Properties on marking ***)
      nodup_marking : NoDup marking;
      
      (* For all place (pl i), (pl i) is in places iff
       * (pl i) is referenced in marking. *)
      no_unmarked_or_unknown_place :
        forall (i : nat), In (pl i) places <-> exists (n : nat), In (i, n) marking;

      (* For all couple of nat (i, n), if (i, n) is in marking 
       * then there is no couple (i, n') in marking with n' different from n. *)
      uniq_index_marking :
        forall (i n : nat),
          In (i, n) marking -> ~exists (n' : nat), In (i, n') marking /\ n <> n';
      
    }.

(**************************************************************)
(************ Are 2 nat/places/transitions equal ? ************)
(**************************************************************)

(*** Formal specification : beq_places ***)
Inductive beq_places_spec : place_type -> place_type -> Prop :=
| beq_places_mk :
    forall (p p' : place_type) (n : nat), 
      p = mk_place n /\ p' = mk_place n -> beq_places_spec p p'.

(* Function : Returns true if p and p' have the same index. 
 *            false otherwise.
 *)
Definition beq_places (p p' : place_type) : bool :=
  match (p, p') with
  | (mk_place n, mk_place n') => beq_nat n n'
  end.

Functional Scheme beq_places_ind := Induction for beq_places Sort Prop.

(*** Correctness proof : beq_places ***)
Theorem beq_places_correct :
  forall (p p' : place_type),
    beq_places p p' = true -> beq_places_spec p p'.
Proof.
  intros p p'.
  functional induction (beq_places  p p') using beq_places_ind.
  intro H. rewrite beq_nat_true_iff in H. rewrite H.
  apply beq_places_mk with (n:=n').
  split; reflexivity. 
Qed.

(*** Completeness proof : beq_places ***)
Theorem beq_places_complete :
  forall (p p' : place_type),
    beq_places_spec p p' -> beq_places p p' = true. 
Proof.
  intros p p' H. elim H.
  intros  p0 p1  n  H01.
  assert (H0 : p0 = mk_place n).  { firstorder. }  
                                  assert (H1 : p1 = mk_place n).  { firstorder. }                   
                                                                  unfold beq_places. rewrite H1. rewrite H0.
  rewrite beq_nat_true_iff. reflexivity.
Qed.

(*** Formal specification : beq_transs ***)
Inductive beq_transs_spec : trans_type -> trans_type -> Prop :=
| beq_transs_mk :
    forall (t t' : trans_type) (n : nat), 
      t = mk_trans n /\ t' = mk_trans n -> beq_transs_spec t t'.

(* Function : Returns true if t and t' have the same index.
 *            false otherwise.
 *)
Definition beq_transs (t t' : trans_type) : bool :=
  match (t, t') with
  | (mk_trans n, mk_trans n') => beq_nat n n'
  end.

Functional Scheme beq_transs_ind := Induction for beq_transs Sort Prop.

(*** Correctness prooof : beq_transs ***)
Theorem beq_transs_correct :
  forall (t t' : trans_type),
    beq_transs t t' = true -> beq_transs_spec t t'.
Proof.
  intros t t'.
  functional induction (beq_transs  t t') using beq_transs_ind.
  intro H. rewrite beq_nat_true_iff in H. rewrite H.
  apply beq_transs_mk with (n:=n').
  split; reflexivity. 
Qed.

(*** Completeness proof : beq_transs ***)
Theorem beq_transs_complete :
  forall (t t' : trans_type),
    beq_transs_spec t t' -> beq_transs t t' = true. 
Proof.
  intros t t' H. elim H.
  intros  t0 t1  n  H01.
  assert (H0 : t0 = mk_trans n).
  - firstorder.   
  - assert (H1 : t1 = mk_trans n).
    + firstorder.                   
    + unfold beq_transs. rewrite H1. rewrite H0.
      rewrite beq_nat_true_iff. reflexivity.
Qed.

(*** Equality decidability for place_type. ***)
Definition places_eq_dec :
  forall x y : place_type, {x = y} + {x <> y}.
Proof.
  decide equality.
  decide equality.
Defined.

(*** Equality decidability for trans_type. ***)
Definition transs_eq_dec :
  forall x y : trans_type, {x = y} + {x <> y}.
Proof.
  decide equality.
  decide equality.
Defined.

(*** Equality decidability for neighbours_type ***)
Definition neighbours_eq_dec :
  forall x y : neighbours_type, {x = y} + {x <> y}.
Proof.
  repeat decide equality.    
Defined.

(*====================================================*)
(*=============== MARKING SECTION  ===================*)
(*====================================================*)
Section Marking.

  (*  
   * Function : Returns the number of tokens
   *            associated with the place of index "index"
   *            in marking "marking".
   *            Returns None if "index" doesn't belong
   *            to the marking.
   *)
  Fixpoint get_m (marking : marking_type) (index : nat) : option nat :=
    match marking with
    | (i, nboftokens) :: tail => if i =? index then
                                   Some nboftokens
                                 else get_m tail index
    (* Exception : index is not in marking. *)
    | [] => None
    end.

  Functional Scheme get_m_ind := Induction for get_m Sort Prop.

  (*** Formal specification : get_m ***)
  Inductive get_m_spec : marking_type -> nat -> option nat -> Prop :=
  | get_m_err :
      forall (i : nat), get_m_spec [] i None
  | get_m_if :
      forall (m m' : marking_type) (index i nboftokens : nat),
        m = (i, nboftokens) :: m' ->
        index = i ->
        get_m_spec m index (Some nboftokens)
  | get_m_else :
      forall (m m' : marking_type) (index i  n : nat) (opt_nboftokens : option nat),
        m = (i, n) :: m' ->
        index <> i ->
        get_m_spec m' index opt_nboftokens -> get_m_spec m index opt_nboftokens.

  (*** Correctness proof : get_m ***)
  Theorem get_m_correct :
    forall (m : marking_type) (index : nat) (opt_nboftokens : option nat),
      get_m m index = opt_nboftokens -> get_m_spec m index opt_nboftokens.
  Proof.
    do 2 intro; functional induction (get_m m index0) using get_m_ind; intros.
    (* Case m = []. *)
    - rewrite <- H; apply get_m_err.
    (* Case if is true. *)
    - rewrite <- H.
      apply get_m_if with (m' := tail) (i := i);
        [auto | rewrite Nat.eqb_sym in e1; apply beq_nat_true in e1; auto].
    (* Case else *)
    - apply get_m_else with (i := i) (n := nboftokens) (m' := tail).
      + auto.
      + rewrite Nat.eqb_sym in e1. apply beq_nat_false in e1. assumption.
      + rewrite <- H. apply IHo with (opt_nboftokens := (get_m tail index0)). auto.
  Qed.

  (*** Completeness proof : get_m ***)
  Theorem get_m_compl :
    forall (m : marking_type) (index : nat) (opt_nboftokens : option nat),
      get_m_spec m index opt_nboftokens -> get_m m index = opt_nboftokens.
  Proof.
    intros. induction H.
    (* Case get_m_0 *)
    - simpl; auto.
    (* Case get_m_if *)
    - rewrite H. simpl.
      rewrite Nat.eqb_sym.
      rewrite H0.
      rewrite Nat.eqb_refl.
      auto.
    (* Case get_m_else *)
    - rewrite H. simpl.
      apply Nat.eqb_neq in H0.
      rewrite Nat.eqb_sym. rewrite H0.
      assumption.
  Qed.
  
  (*
   * Equality decidability between two pairs of nat. 
   * Necessary to use the replace_occ function.
   *)
  Definition prodnat_eq_dec :
    forall (x y : (nat * nat)), {x = y} + {x <> y}.
  Proof.
    decide equality.
    decide equality.
    decide equality.
  Defined.

  (*
   * Function : Replaces every occurence of occ by repl
   *            in list l.
   *            Inspired from the remove function. 
   *)
  Fixpoint replace_occ
           {A : Type}
           (eq_dec : forall (x y : A), {x = y} + {x <> y})
           (occ : A)
           (repl : A)
           (l : list A)
           {struct l} : list A :=
    match l with
    (* eq_dec is evaluated into a boolean expr
     * thanks to the def Bool.Sumbool.bool_of_sumbool *)
    | x :: tl => if eq_dec x occ then
                   repl :: (replace_occ eq_dec occ repl tl)
                 else x :: (replace_occ eq_dec occ repl tl)
    | [] => l
    end.

  Functional Scheme replace_occ_ind := Induction for replace_occ Sort Prop.

  (*** Formal specification : replace_occ ***)
  Inductive replace_occ_spec
            {A : Type}
            (eq_dec : forall x y : A, {x = y} + {x <> y})
            (occ : A)
            (repl : A) :
    list A -> list A -> Prop :=
  | replace_occ_nil :
      replace_occ_spec eq_dec occ repl [] []
  | replace_occ_if :
      forall (l l' : list A),
      replace_occ_spec eq_dec occ repl l l' ->
      replace_occ_spec eq_dec occ repl (occ :: l) (repl :: l')
  | replace_occ_else :
      forall (l l' : list A) (x : A),
      x <> occ ->
      replace_occ_spec eq_dec occ repl l l' ->
      replace_occ_spec eq_dec occ repl (x :: l) (x :: l').

  (*** Correctness proof : replace_occ ***)
  Theorem replace_occ_correct {A : Type} :
    forall (eq_dec : forall x y : A, {x = y} + {x <> y}) (occ repl : A) (l l' : list A),
    replace_occ eq_dec occ repl l = l' -> replace_occ_spec eq_dec occ repl l l'.
  Proof.
    do 4 intro; functional induction (replace_occ eq_dec occ repl l)
                           using replace_occ_ind; intros.
    (* Case l = nil *)
    - rewrite <- H; apply replace_occ_nil.
    (* Case occ is head *)
    - rewrite <- H; apply replace_occ_if; apply IHl0; auto.
    (* Case occ is not head *)
    - rewrite <- H; apply replace_occ_else; [auto |apply IHl0; auto].
  Qed.

  (*** Completeness proof : replace_occ ***)
  Theorem replace_occ_compl {A : Type} :
    forall (eq_dec : forall x y : A, {x = y} + {x <> y}) (occ repl : A) (l l' : list A),
    replace_occ_spec eq_dec occ repl l l' -> replace_occ eq_dec occ repl l = l'.
  Proof.
    intros; induction H.
    (* Case replace_occ_nil *)
    - simpl; auto.
    (* Case replace_occ_if *)
    - simpl. elim eq_dec; [intro; rewrite IHreplace_occ_spec; auto | intro; contradiction].
    (* Case replace_occ_else *)
    - simpl. elim eq_dec; [intro; contradiction | intro; rewrite IHreplace_occ_spec; auto].
  Qed.
  
  (* Function : Given a marking m, add/remove nboftokens tokens (if not None)
   *            inside place p and returns the new marking.
   *
   * Param nboftokens : number of tokens to add or sub for place p.
   *
   * Param op : addition or substraction operator.
   *)
  Definition modify_m
             (m : marking_type)
             (p : place_type)
             (op : nat -> nat -> nat)
             (nboftokens : option nat_star) : option marking_type :=
    match p with
    | (pl i) => match nboftokens with
                | None => Some m
                | Some (mk_nat_star n' _) =>
                  let opt_n := get_m m i in
                  match opt_n with
                  (* The couple (i, n) to remove must be unique. *)
                  | Some n =>
                    Some (replace_occ prodnat_eq_dec (i, n) (i, (op n n')) m)
                  (* If couple with first member i doesn't exist
                   * in m, then returns None (it's an exception). *)
                  | None => None 
                  end
                end
    end.

  Functional Scheme modify_m_ind := Induction for modify_m Sort Prop.

  (*** Formal specification : modify_m ***)
  Inductive modify_m_spec
            (m : marking_type)
            (p : place_type)
            (op : nat -> nat -> nat) :
    option nat_star -> option marking_type -> Prop :=
  | modify_m_tokens_none :
      modify_m_spec m p op None (Some m)
  (* Case place of index i is not in the marking,
   * which is a exception case. *)
  | modify_m_err :
      forall (i : nat)
             (n : nat_star),
        p = (pl i) ->
        get_m_spec m i None ->
        modify_m_spec m p op (Some n) None
  (* Case place of index i exists in the marking *)
  | modify_m_some_repl :
      forall (nboftokens : option nat_star)
             (i n n' : nat)
             (is_positive : n' > 0)
             (m' : marking_type),
        (pl i) = p ->
        nboftokens = Some (mk_nat_star n' is_positive) ->
        get_m_spec m i (Some n) ->
        replace_occ_spec prodnat_eq_dec (i, n) (i, (op n n')) m m' ->
        modify_m_spec m p op nboftokens (Some m').

  (*** Correctness proof : modify_m ***)
  Theorem modify_m_correct :
    forall (m : marking_type)
           (optionm : option marking_type)
           (p : place_type)
           (op : nat -> nat -> nat)
           (nboftokens : option nat_star),
    modify_m m p op nboftokens = optionm -> modify_m_spec m p op nboftokens optionm.
  Proof.
    do 5 intro; functional induction (modify_m m p op nboftokens)
                           using modify_m_ind; intros.
    (* Case (pl i) exists in marking m *)
    - rewrite <- H. apply modify_m_some_repl with (i := i)
                                    (n := n0)
                                    (n' := n')
                                    (is_positive := _x).
      + auto.
      + auto.
      + apply get_m_correct in e2; auto.
      + apply replace_occ_correct; auto.
    (* Case (pl i) doesn't exist in marking m (error) *)
    - rewrite <- H. apply modify_m_err with (i := i).
      + auto.
      + apply get_m_correct; auto.
    (* Case nboftokens is None *)
    - rewrite <- H; apply modify_m_tokens_none.
  Qed.

  (*** Completeness proof : modify_m ***)
  Theorem modify_m_compl :
    forall (m : marking_type)
           (optionm : option marking_type)
           (p : place_type)
           (op : nat -> nat -> nat)
           (nboftokens : option nat_star),
    modify_m_spec m p op nboftokens optionm -> modify_m m p op nboftokens = optionm.
  Proof.
    intros; induction H.
    (* Case  modify_m_tokens_none *)
    - unfold modify_m; elim p; auto.
    (* Case modify_m_err *)
    - unfold modify_m; rewrite H; elim n; intros.
      apply get_m_compl in H0; rewrite H0; auto.
    (* Case modify_m_some_repl *)
    - unfold modify_m; rewrite <- H; rewrite H0; apply get_m_compl in H1; rewrite H1.
      apply replace_occ_compl in H2; rewrite H2; auto.      
  Qed.
  
  (*=================================================*)
  (*=============== UPDATE MARKING ==================*)
  (*=================================================*)

  (*
   * Function : Removes some tokens from pre places, according 
   *            to the firing of t. 
   *            Returns the resulting marking.
   *)
  Fixpoint update_marking_pre
           (t : trans_type)
           (pre : weight_type)
           (m : marking_type)
           (places : list place_type) : option marking_type :=
    match places with
    | p :: tail => match modify_m m p Nat.sub (pre t p) with
                   | Some m' => update_marking_pre t pre m' tail
                   (* It's a exception, p is not referenced in m. *)
                   | None => None
                   end
    | [] => Some m
    end.

  Functional Scheme update_marking_pre_ind := Induction for update_marking_pre Sort Prop.
  
  (*** Formal specification : update_marking_pre ***)
  Inductive update_marking_pre_spec
            (t : trans_type)
            (pre : weight_type)
            (m : marking_type) :
    list place_type -> option marking_type -> Prop :=
  | update_marking_pre_nil :
      update_marking_pre_spec t pre m [] (Some m)
  | update_marking_pre_some :
      forall (places : list place_type)
             (m' : marking_type)
             (optionm : option marking_type)
             (p : place_type),
        modify_m_spec m p Nat.sub (pre t p) (Some m') ->
        update_marking_pre_spec t pre m' places optionm ->
        update_marking_pre_spec t pre m (p :: places) optionm
  | update_marking_pre_err :
      forall (p : place_type) (places : list place_type),
        modify_m_spec m p Nat.sub (pre t p) None ->
        update_marking_pre_spec t pre m (p :: places) None.

  (*** Correctness proof : update_marking_pre ***)
  Theorem update_marking_pre_correct :
    forall (t : trans_type)
           (pre : weight_type)
           (places : list place_type)
           (m : marking_type)
           (optionm : option marking_type),
      update_marking_pre t pre m places = optionm ->
      update_marking_pre_spec t pre m places optionm.
  Proof.
    intros t pre places m optionm;
    functional induction (update_marking_pre t pre m places)
               using update_marking_pre_ind;
    intros.
    (* Case places is nil *)
    - rewrite <- H; apply update_marking_pre_nil.
    (* Case p is referenced in m *)
    - apply update_marking_pre_some with (m' := m').
      + apply modify_m_correct; auto.
      + apply IHo; auto.
    (* Case p is not in m *)
    - rewrite <- H; apply update_marking_pre_err;
        [apply modify_m_correct; auto].      
  Qed.

  (*** Completeness proof : update_marking_pre ***)
  Theorem update_marking_pre_compl :
    forall (t : trans_type)
           (pre : weight_type)
           (places : list place_type)
           (m : marking_type)
           (optionm : option marking_type),
      update_marking_pre_spec t pre m places optionm ->
      update_marking_pre t pre m places = optionm.
  Proof.
    intros t pre places m optionm Hspec; induction Hspec.
    (* Case update_marking_pre_nil *)
    - simpl; auto.
    (* Case update_marking_pre_some *)
    - simpl; apply modify_m_compl in H; rewrite H; rewrite IHHspec; auto.
    (* Case update_marking_pre_err *)
    - simpl; apply modify_m_compl in H; rewrite H; auto.
  Qed.
  
  (* 
   * Function : Adds some tokens from post places, according 
   *            to the firing of t.
   *            Returns a new marking application. 
   *)
  Fixpoint update_marking_post (* structural induction over list of places *)
           (t : trans_type)
           (post : weight_type)
           (m : marking_type)
           (places : list place_type) : option marking_type :=
    match places with
    | p :: tail => match modify_m m p Nat.add (post t p) with
                   | Some m' => update_marking_post t post m' tail
                   (* It's a exception, p is not referenced in m. *)
                   | None => None
                   end
    | [] => Some m
    end.

  Functional Scheme update_marking_post_ind := Induction for update_marking_post Sort Prop.

  (*** Formal specification : update_marking_post ***)
  Inductive update_marking_post_spec
            (t : trans_type)
            (post : weight_type)
            (m : marking_type) :
    list place_type -> option marking_type -> Prop :=
  | update_marking_post_nil :
      update_marking_post_spec t post m [] (Some m)
  | update_marking_post_some :
      forall (p : place_type)
             (m' : marking_type)
             (optionm : option marking_type)
             (places : list place_type),
        modify_m_spec m p Nat.add (post t p) (Some m') ->
        update_marking_post_spec t post m' places optionm ->
        update_marking_post_spec t post m (p :: places) optionm
  | update_marking_post_err :
      forall (p : place_type)
             (places : list place_type),
        modify_m_spec m p Nat.add (post t p) None ->
        update_marking_post_spec t post m (p :: places) None.

  (*** Correctness proof : update_marking_post ***)
  Theorem update_marking_post_correct :
    forall (t : trans_type)
           (post : weight_type)
           (places : list place_type)
           (m : marking_type)
           (optionm : option marking_type),
    update_marking_post t post m places = optionm ->
    update_marking_post_spec t post m places optionm.
  Proof.
    intros t post places m optionm;
    functional induction (update_marking_post t post m places)
               using update_marking_post_ind;
    intros.
    (* Case places is nil *)
    - rewrite <- H; apply update_marking_post_nil.
    (* Case p is referenced in m. *)
    - apply update_marking_post_some with (m' := m').
      + apply modify_m_correct; auto.
      + apply (IHo H); auto.
    (* Case p not referenced in m, error! *)
    - rewrite <- H;
        apply update_marking_post_err;
        apply modify_m_correct; auto.
  Qed.

  (*** Completeness proof : update_marking_post ***)
  Theorem update_marking_post_compl :
    forall (t : trans_type)
           (post : weight_type)
           (places : list place_type)
           (m : marking_type)
           (optionm : option marking_type),
      update_marking_post_spec t post m places optionm ->
      update_marking_post t post m places = optionm.
  Proof.
    intros t post places m optionm H; elim H; intros.
    (* Case update_marking_post_nil *)
    - simpl; auto.
    (* Case update_marking_post_some *)
    - simpl; apply modify_m_compl in H0; rewrite H0; auto.
    (* Case update_marking_post_err *)
    - simpl; apply modify_m_compl in H0; rewrite H0; auto.
  Qed.

End Marking.

(*===============================================================*)
(*== CHECKS NB OF TOKENS IN NEIGHBOUR PLACES OF A TRANSITION T ==*)
(*== WITH WEIGHT OF ITS ADJACENT EDGES.                        ==*)
(*===============================================================*)

Section Edges.
  
  (*
   * Function : Returns true if all places in the places list
   *            have a marking superior or equal to pre(t)(p)
   *            or test(t)(p).
   *
   * Param pre_or_test_arcs_t : pre(t) and test(t) returning
   *                            the weight of the edge coming
   *                            from some place p towards transition t.
   *                            
   *)
  Fixpoint check_pre_or_test
           (pre_or_test_arcs_t : place_type -> option nat_star)
           (m : marking_type)
           (places : list place_type)
           (check_result : bool) : option bool :=
    match places with
    | (pl i) :: tail => match pre_or_test_arcs_t (pl i) with
                        (* If there is no pre or test edge between (pl i) and t. *)
                        | None => check_pre_or_test pre_or_test_arcs_t m tail check_result
                        (* Else some pre or test edge exists. *)
                        | Some (mk_nat_star edge_weight _) =>
                          (* Retrieves the number of tokens associated 
                           * with place i. *)
                          let nboftokens := (get_m m i) in
                          match nboftokens with
                          | Some n =>
                            check_pre_or_test pre_or_test_arcs_t m tail ((edge_weight <=? n)
                                                                           && check_result)
                          (* If number of tokens is None, then it's an error. *)
                          | None => None
                          end
                        end
    (* check_result must be initialized to true. *)
    | [] => Some check_result
    end.
  
  Functional Scheme check_pre_or_test_ind := Induction for check_pre_or_test Sort Prop. 
  
  (*** Formal specification : check_pre_or_test ***)
  Inductive check_pre_or_test_spec
            (pre_or_test_arcs_t : place_type -> option nat_star)
            (m : marking_type) :
    list place_type -> bool -> option bool -> Prop :=
  | check_pre_or_test_nil :
      forall (b : bool),
        check_pre_or_test_spec pre_or_test_arcs_t m [] b (Some b)
  | check_pre_or_test_edge_none :
      forall (places : list place_type)
             (i : nat)
             (check_result : bool)
             (optionb : option bool),
        pre_or_test_arcs_t (pl i) = None ->
        check_pre_or_test_spec pre_or_test_arcs_t m places check_result optionb ->
        check_pre_or_test_spec pre_or_test_arcs_t m ((pl i) :: places) check_result optionb
  | check_pre_or_test_err :
      forall (places : list place_type) 
             (i edge_weight : nat)
             (check_result : bool)
             (is_positive : edge_weight > 0),
        pre_or_test_arcs_t (pl i) = Some (mk_nat_star edge_weight is_positive) ->
        get_m_spec m i None ->
        check_pre_or_test_spec pre_or_test_arcs_t m ((pl i) :: places) check_result None
  | check_pre_or_test_tokens_some :
      forall (places : list place_type) 
             (i n edge_weight : nat)
             (is_positive : edge_weight > 0)
             (check_result : bool)
             (optionb : option bool),
      pre_or_test_arcs_t (pl i) = Some (mk_nat_star edge_weight is_positive) ->
      get_m_spec m i (Some n) ->
      check_pre_or_test_spec pre_or_test_arcs_t m places ((edge_weight <=? n) && check_result)
                             optionb ->
      check_pre_or_test_spec pre_or_test_arcs_t m ((pl i) :: places) check_result optionb.

  (*** Correctness proof : check_pre_or_test ***)
  Theorem check_pre_or_test_correct :
    forall (pre_or_test_arcs_t : place_type -> option nat_star)
           (m : marking_type)
           (places : list place_type)
           (check_result : bool)
           (optionb : option bool),
    check_pre_or_test pre_or_test_arcs_t m places check_result = optionb ->
    check_pre_or_test_spec pre_or_test_arcs_t m places check_result optionb.
  Proof.
    intros pre_or_test_arcs_t m places check_result optionb;
    functional induction (check_pre_or_test pre_or_test_arcs_t m places check_result)
               using check_pre_or_test_ind;
    intros.
    (* Case places = [] *)
    - rewrite <- H; apply check_pre_or_test_nil.
    (* Case edge and tokens exist *)
    - apply check_pre_or_test_tokens_some with (i := i)
                                               (n := n0)
                                               (edge_weight := edge_weight)
                                               (is_positive := _x).
      + rewrite e1; auto.
      + apply get_m_correct; auto.
      + apply IHo; auto. 
    (* Case of error, get_m returns None *)
    - rewrite <- H; apply check_pre_or_test_err with (i := i)
                                               (edge_weight := edge_weight)
                                               (is_positive := _x).
      + rewrite e1; auto.
      + apply get_m_correct; auto.
    (* Case edge doesn't exist *)
    - apply check_pre_or_test_edge_none.
      + auto.
      + apply IHo; auto.
  Qed.

  (*** Completeness proof : check_pre_or_test ***)
  Theorem check_pre_or_test_compl :
   forall (pre_or_test_arcs_t : place_type -> option nat_star)
          (m : marking_type)
          (places : list place_type)
          (check_result : bool)
          (optionb : option bool),
     check_pre_or_test_spec pre_or_test_arcs_t m places check_result optionb ->
     check_pre_or_test pre_or_test_arcs_t m places check_result = optionb.
  Proof.
    intros pre_or_test_arcs_t m places check_result optionb H; induction H.
    (* Case check_pre_or_test_nil *)
    - simpl; auto.
    (* Case check_pre_or_test_edge_none *)
    - simpl; rewrite H; auto.
    (* Case check_pre_or_test_err *)
    - simpl; rewrite H; apply get_m_compl in H0; rewrite H0; auto.
    (* Case check_pre_or_test_tokens_some *)
    - simpl; rewrite H; apply get_m_compl in H0; rewrite H0; auto.
  Qed.
  
  (**************************************************)
  (**************************************************)

  (*
   * Function : Returns true if all places in the places list
   *            have a marking less equal than inhib(t)(p).
   *            inhib(t)(p) denoting the function associating
   *            a weight to a inhibiting edge coming from place
   *            p to transition t. 
   *)
  Fixpoint check_inhib
           (inhib_arcs_t : place_type -> option nat_star)
           (m : marking_type)
           (places : list place_type)
           (check_result : bool) : option bool :=
    match places with
    | (pl i) :: tail => match inhib_arcs_t (pl i) with
                        (* If there is inhib edge between (pl i) and t. *)
                        | None => check_inhib inhib_arcs_t m tail check_result
                        (* Else some inhib edge exists. *)
                        | Some (mk_nat_star edge_weight _) =>
                          let nboftokens := (get_m m i) in
                          match nboftokens with
                          | Some n => check_inhib inhib_arcs_t m tail (check_result
                                                                         && (n <? edge_weight))
                          (* Case of error, place i is not in m. *)
                          | None => None
                          end
                          
                        end
    | [] => Some check_result
    end.

  Functional Scheme check_inhib_ind := Induction for check_inhib Sort Prop.

  (*** Formal specification ***)
  Inductive check_inhib_spec
            (inhib_arcs_t : place_type -> option nat_star)
            (m : marking_type) :
    list place_type -> bool -> option bool -> Prop :=
  | check_inhib_nil :
      forall (b : bool),
        check_inhib_spec inhib_arcs_t m [] b (Some b)
  | check_inhib_edge_none :
      forall (places : list place_type)
             (i : nat)
             (check_result : bool)
             (optionb : option bool),
      inhib_arcs_t (pl i) = None ->
      check_inhib_spec inhib_arcs_t m places check_result optionb->
      check_inhib_spec inhib_arcs_t m ((pl i) :: places) check_result optionb
  | check_inhib_err :
      forall (places : list place_type) 
             (i edge_weight : nat)
             (is_positive : edge_weight > 0)
             (check_result : bool),
        inhib_arcs_t (pl i) = Some (mk_nat_star edge_weight is_positive) ->
        get_m_spec m i None ->
        check_inhib_spec inhib_arcs_t m ((pl i) :: places) check_result None
  | check_inhib_tokens_some :
      forall (places : list place_type) 
             (i n edge_weight : nat)
             (is_positive : edge_weight > 0)
             (check_result : bool)
             (optionb : option bool),
      inhib_arcs_t (pl i) = Some (mk_nat_star edge_weight is_positive) ->
      get_m_spec m i (Some n) ->
      check_inhib_spec inhib_arcs_t m places (check_result && (n <? edge_weight)) optionb ->
      check_inhib_spec inhib_arcs_t m ((pl i) :: places) check_result optionb.

  (*** Correctness proof : check_inhib ***)
   Theorem check_inhib_correct :
    forall (inhib_arcs_t : place_type -> option nat_star)
           (m : marking_type)
           (places : list place_type)
           (check_result : bool)
           (optionb : option bool),
    check_inhib inhib_arcs_t m places check_result = optionb ->
    check_inhib_spec inhib_arcs_t m places check_result optionb.
  Proof.
    intros inhib_arcs_t m places check_result optionb;
    functional induction (check_inhib inhib_arcs_t m places check_result)
               using check_inhib_ind;
    intros.
    (* Case places = [] *)
    - rewrite <- H; apply check_inhib_nil.
    (* Case edge and tokens exist *)
    - apply check_inhib_tokens_some with (i := i)
                                               (n := n0)
                                               (edge_weight := edge_weight)
                                               (is_positive := _x).
      + rewrite e1; auto.
      + apply get_m_correct; auto.
      + apply IHo; auto.
    (* Case edge exists but no tokens, case of error! *)
    - rewrite <- H; apply check_inhib_err with (i := i)
                                                       (edge_weight := edge_weight)
                                                       (is_positive := _x).
      + rewrite e1; auto.
      + apply get_m_correct; auto.
    (* Case edge doesn't exist *)
    - apply check_inhib_edge_none.
      + auto.
      + apply IHo; auto.
  Qed.

  (*** Completeness proof : check_inhib ***)
  Theorem check_inhib_compl :
   forall (inhib_arcs_t : place_type -> option nat_star)
          (m : marking_type)
          (places : list place_type)
          (check_result : bool)
          (optionb : option bool),
     check_inhib_spec inhib_arcs_t m places check_result optionb ->
     check_inhib inhib_arcs_t m places check_result = optionb.
  Proof.
    intros inhib_arcs_t m places check_result optionb H; induction H.
    (* Case check_inhib_nil *)
    - simpl; auto.
    (* Case check_inhib_edge_none *)
    - simpl; rewrite H; auto.
    (* Case check_inhib_err *)
    - simpl; rewrite H; apply get_m_compl in H0; rewrite H0; auto.
    (* Case check_inhib_tokens_some *)
    - simpl; rewrite H; apply get_m_compl in H0; rewrite H0; auto.
  Qed.
  
  (*****************************************************)
  (*****************************************************)

  (* 
   * Function : Returns true if a certain transition t
   *            is sensitized according to a marking steadym
   *            (or decreasingm) on the neighbour places of t and
   *            to some weight functions pre_arcs_t, test_arcs_t
   *            and inhib_arcs_t.
   *)
  Definition check_all_edges
             (neighbours_t : neighbours_type)
             (pre_arcs_t : place_type -> option nat_star)
             (test_arcs_t : place_type -> option nat_star)
             (inhib_arcs_t : place_type -> option nat_star)
             (steadym decreasingm : marking_type) : option bool :=
    match (check_pre_or_test pre_arcs_t decreasingm (pre_pl neighbours_t) true) with
    | Some check_pre_result =>  
      match (check_pre_or_test test_arcs_t steadym (test_pl neighbours_t) true) with
      | Some check_test_result =>
        match check_inhib inhib_arcs_t steadym (inhib_pl neighbours_t) true with
        | Some check_inhib_result => Some (check_pre_result
                                             && check_test_result
                                             && check_inhib_result)
        (* Case of error!! *)
        | None => None
        end
      (* Case of error!! *)
      | None => None
      end
    (* Case of error!! *)
    | None => None
    end.

  Functional Scheme check_all_edges_ind := Induction for check_all_edges Sort Prop.

  (*** Formal specification : check_all_edges ***)
  Inductive check_all_edges_spec
            (neighbours_t : neighbours_type)
            (pre_arcs_t : place_type -> option nat_star)
            (test_arcs_t : place_type -> option nat_star)
            (inhib_arcs_t : place_type -> option nat_star)
            (steadym decreasingm : marking_type) : option bool -> Prop :=
  | check_all_edges_some :
      forall (check_pre_result check_test_result check_inhib_result : bool),
        check_pre_or_test_spec pre_arcs_t decreasingm (pre_pl neighbours_t) true (Some check_pre_result) /\
        check_pre_or_test_spec test_arcs_t steadym (test_pl neighbours_t) true (Some check_test_result) /\
        check_inhib_spec inhib_arcs_t steadym (inhib_pl neighbours_t) true (Some check_inhib_result) ->
        check_all_edges_spec neighbours_t pre_arcs_t test_arcs_t inhib_arcs_t steadym decreasingm
                             (Some (check_pre_result && check_test_result && check_inhib_result))
  | check_all_edges_err :
      check_pre_or_test_spec pre_arcs_t decreasingm (pre_pl neighbours_t) true None \/
      check_pre_or_test_spec test_arcs_t steadym (test_pl neighbours_t) true None \/
      check_inhib_spec inhib_arcs_t steadym (inhib_pl neighbours_t) true None ->
      check_all_edges_spec neighbours_t pre_arcs_t test_arcs_t inhib_arcs_t steadym decreasingm None.

  (*** Correctness proof : check_all_edges *)
  Theorem check_all_edges_correct :
    forall (neighbours_t : neighbours_type)
           (pre_arcs_t : place_type -> option nat_star)
           (test_arcs_t : place_type -> option nat_star)
           (inhib_arcs_t : place_type -> option nat_star)
           (steadym decreasingm : marking_type)
           (optionb : option bool),
    check_all_edges neighbours_t pre_arcs_t test_arcs_t inhib_arcs_t steadym decreasingm = optionb ->
    check_all_edges_spec neighbours_t pre_arcs_t test_arcs_t inhib_arcs_t steadym decreasingm optionb.
  Proof.
    intros;
      functional induction (check_all_edges neighbours_t pre_arcs_t test_arcs_t inhib_arcs_t steadym decreasingm)
                 using check_all_edges_ind;
      intros.
    (* Case check_pre, check_test and check_inhib returned some value. *)
    - rewrite <- H; apply check_all_edges_some.
      split; [apply check_pre_or_test_correct; auto |
              split; [apply check_pre_or_test_correct; auto |
                      apply check_inhib_correct; auto]].            
    (* Case of error 1. check_inhib returns None. *)
    - rewrite <- H; apply check_all_edges_err.
      apply check_inhib_correct in e1; auto.
    (* Case of error 2. check_test returns None.  *)
    - rewrite <- H; apply check_all_edges_err.
      apply check_pre_or_test_correct in e0; auto.
    (* Case of error 3. check_pre returns None. *)
    - rewrite <- H; apply check_all_edges_err.
      apply check_pre_or_test_correct in e; auto.
  Qed.

  (*** Completeness proof : check_all_edges ***)
  Theorem check_all_edges_compl :
    forall (neighbours_t : neighbours_type)
           (pre_arcs_t : place_type -> option nat_star)
           (test_arcs_t : place_type -> option nat_star)
           (inhib_arcs_t : place_type -> option nat_star)
           (steadym decreasingm : marking_type)
           (optionb : option bool),
      check_all_edges_spec neighbours_t pre_arcs_t test_arcs_t inhib_arcs_t steadym decreasingm optionb ->
      check_all_edges neighbours_t pre_arcs_t test_arcs_t inhib_arcs_t steadym decreasingm = optionb.
  Proof.
    intros. induction H.
    (* Case check_all_edges_some *)
    - unfold check_all_edges.
      elim H; clear H; intros.
      elim H0; clear H0; intros.
      repeat (((apply check_pre_or_test_compl in H; rewrite H) ||
               (apply check_pre_or_test_compl in H0; rewrite H0) ||
               (apply check_inhib_compl in H1; rewrite H1));
              auto).
    (* Case check_all_edges_err *)
    - unfold check_all_edges.
      elim H; clear H; intros.
      + apply check_pre_or_test_compl in H; rewrite H; auto.
      + elim H; clear H; intros.
        -- case (check_pre_or_test pre_arcs_t decreasingm (pre_pl neighbours_t) true).
           ++ intro; apply check_pre_or_test_compl in H; rewrite H; auto.
           ++ auto.
        -- case (check_pre_or_test pre_arcs_t decreasingm (pre_pl neighbours_t) true).
           +++ case (check_pre_or_test test_arcs_t steadym (test_pl neighbours_t) true);
                 [ apply check_inhib_compl in H; rewrite H; auto | intro; auto ].
           +++ auto.
  Qed.
  
End Edges.

(*==============================================================*)
(*================= FIRING ALGORITHM for SPN ===================*)
(*==============================================================*)

Section FireSpn.

  (*  
   * Function : Returns the element of type neighbours_type
   *            included in the list neighbours having an
   *            index attribute equal to idx.
   *            Returns None if no element have an index
   *            attribute equal to idx.
   *)
  Fixpoint get_neighbours
           (lneighbours : list neighbours_type)
           (idx : nat) {struct lneighbours} : option neighbours_type :=
    match lneighbours with
    | neighbours :: tail => if (index neighbours) =? idx then
                              Some neighbours
                            else get_neighbours tail idx
    | [] => None 
    end.

  (*** Formal specification : get_neighbours ***)
  Inductive get_neighbours_spec :
    list neighbours_type -> nat -> option neighbours_type -> Prop :=
  | get_neighbours_err :
      forall (idx : nat), get_neighbours_spec [] idx None
  | get_neighbours_if :
      forall (lneighbours lneighbours' : list neighbours_type)
             (idx : nat)
             (neighbours : neighbours_type),
      lneighbours = neighbours :: lneighbours' ->
      (index neighbours) = idx ->
      get_neighbours_spec lneighbours idx (Some neighbours)
  | get_neighbours_else :
      forall (lneighbours lneighbours' : list neighbours_type)
             (idx : nat)
             (neighbours : neighbours_type)
             (opt_neighbours : option neighbours_type),
      lneighbours = neighbours :: lneighbours' ->
      (index neighbours) <> idx ->
      get_neighbours_spec lneighbours' idx opt_neighbours ->
      get_neighbours_spec lneighbours idx opt_neighbours.

  Functional Scheme get_neighbours_ind := Induction for get_neighbours Sort Prop.
  
  (*** Correctness proof : get_neighbours ***)
  Theorem get_neighbours_correct :
    forall (lneighbours : list neighbours_type)
           (idx : nat)
           (opt_neighbours : option neighbours_type),
    get_neighbours lneighbours idx = opt_neighbours ->
    get_neighbours_spec lneighbours idx opt_neighbours.
  Proof.
    intros lneighbours idx opt_neighbours;
      functional induction (get_neighbours lneighbours idx) using get_neighbours_ind; intros.
    (* Case neighbours = None *)
    - rewrite <- H; apply get_neighbours_err with (idx := idx).
    (* Case neighbour is head *)
    - rewrite <- H; apply get_neighbours_if with (lneighbours' := tail) (idx := idx);
        [auto | apply beq_nat_true in e0; auto].
    (* Case neighbour is not head *)
    - rewrite <- H. apply get_neighbours_else with (neighbours := neighbours)
                                                   (lneighbours' := tail)
                                                   (idx := idx).
      + auto.
      + apply beq_nat_false in e0. auto.
      + rewrite H. apply IHo. auto.
  Qed.

  (*** Completeness proof : get_neighbours ***)
  Theorem get_neighbours_compl :
    forall (lneighbours : list neighbours_type)
           (idx : nat)
           (opt_neighbours : option neighbours_type),
    get_neighbours_spec lneighbours idx opt_neighbours ->
    get_neighbours lneighbours idx = opt_neighbours.
  Proof.
     intros. induction H.
    (* Case get_neighbours_err *)
    - simpl; auto.
    (* Case get_neighbours_if *)
    - rewrite H. simpl.
      rewrite H0.
      rewrite Nat.eqb_refl.
      auto.
    (* Case get_neighbours_else *)
    - rewrite H. simpl.
      apply Nat.eqb_neq in H0.
      rewrite H0.
      assumption.
  Qed.
  
  (* 
   * There are 2 parallel calculus in spn_fire_pre_aux : 
   * 1. pumping tokens to get "decreasingm" (fired pre)
   * 2. returning group of transitions (fired_pre_group)
   *
   * and 2 markings are recorded : 
   * 1. the initial one to check with inhib and test arcs
   * 2. a floating (decreasing) intermediate marking to check classic arcs
   *)
  
  (* Function : Given 1 priority group of transitions (a list pgroup), 
   *            returns 1 list of transitions "fired_pre_group" 
   *            and marking "decreasingm" accordingly ...
   *
   *            Returns a couple (list of transitions, marking)
   *            For each sensitized transition of the list,
   *            the marking of the pre-condition places are updated (the 
   *            transition is fired). "decreasingm" is then the resulting marking.
   *)
  Fixpoint spn_fire_pre_aux
           (lneighbours : list neighbours_type)
           (pre test inhib : weight_type)  
           (steadym : marking_type)
           (decreasingm : marking_type)
           (* "fired_pre_group" meant  to be empty at first *)
           (fired_pre_group pgroup : list trans_type) :
    option (list trans_type * marking_type) :=
    match pgroup with
    | (tr i) :: tail =>
      match get_neighbours lneighbours i with
      (* Checks neighbours of t. *)
      | Some neighbours_t =>
        (* If t is sensitized. *)
        match check_all_edges neighbours_t (pre (tr i)) (test (tr i)) (inhib (tr i)) steadym decreasingm with
        | Some true =>
          (* Updates the marking for the pre places, neighbours of t. *)
          match update_marking_pre (tr i) pre decreasingm (pre_pl neighbours_t) with
          | Some marking' =>
            (spn_fire_pre_aux lneighbours pre test inhib steadym marking' (fired_pre_group ++ [(tr i)]) tail)
          (* Something went wrong, error! *)
          | None => None
          end
        | Some false =>
          (* Else no changes but inductive progress. *)
          (spn_fire_pre_aux lneighbours pre test inhib steadym decreasingm fired_pre_group tail)
        (* Something went wrong, error! *)
        | None => None
        end
      (* If transition t have no neighbours, then error! *)
      | None => None
      end
    | []  => Some (fired_pre_group, decreasingm)
    end.

  Functional Scheme spn_fire_pre_aux_ind := Induction for spn_fire_pre_aux Sort Prop. 
  
  (*** Formal specification : spn_fire_pre_aux ***)
  Inductive spn_fire_pre_aux_spec
            (lneighbours : list neighbours_type)
            (pre test inhib : weight_type) 
            (steadym : marking_type) 
            (decreasingm : marking_type)
            (fired_pre_group : list trans_type) :
    list trans_type -> option (list trans_type * marking_type) -> Prop :=
  | spn_fire_pre_aux_nil :
      spn_fire_pre_aux_spec lneighbours pre test inhib steadym decreasingm fired_pre_group []
                            (Some (fired_pre_group, decreasingm))
  (* Case get_neighbours returns an error. *)
  | spn_fire_pre_aux_neighbours_err :
      forall (i : nat) (pgroup : list trans_type),
        get_neighbours_spec lneighbours i None ->
        spn_fire_pre_aux_spec lneighbours pre test inhib steadym decreasingm fired_pre_group ((tr i) :: pgroup)
                              None
  (* Case check_all_edges returns an error. *)
  | spn_fire_pre_aux_edges_err :
      forall (i : nat) (pgroup : list trans_type) (neighbours_t : neighbours_type),
        get_neighbours_spec lneighbours i (Some neighbours_t) ->
        check_all_edges_spec neighbours_t (pre (tr i)) (test (tr i)) (inhib (tr i)) steadym decreasingm
                             None ->
        spn_fire_pre_aux_spec lneighbours pre test inhib steadym decreasingm fired_pre_group ((tr i) :: pgroup)
                              None
  (* Case check_all_edges returns false. *)
  | spn_fire_pre_aux_edges_false :
      forall (i : nat)
             (pgroup : list trans_type)
             (neighbours_t : neighbours_type)
             (option_final_couple : option (list trans_type * marking_type)),
        get_neighbours_spec lneighbours i (Some neighbours_t) ->
        check_all_edges_spec neighbours_t (pre (tr i)) (test (tr i)) (inhib (tr i)) steadym decreasingm
                             (Some false) ->
        spn_fire_pre_aux_spec lneighbours pre test inhib steadym decreasingm fired_pre_group pgroup
                              option_final_couple ->
        spn_fire_pre_aux_spec lneighbours pre test inhib steadym decreasingm fired_pre_group ((tr i) :: pgroup)
                              option_final_couple
  (* Case update_marking_pre returns an error. *)
  | spn_fire_pre_aux_update_err :
      forall (i : nat)
             (neighbours_t : neighbours_type)
             (pgroup : list trans_type),
      get_neighbours_spec lneighbours i (Some neighbours_t) ->
      check_all_edges_spec neighbours_t (pre (tr i)) (test (tr i)) (inhib (tr i)) steadym decreasingm (Some true) ->
      update_marking_pre_spec (tr i) pre decreasingm (pre_pl neighbours_t) None ->
      spn_fire_pre_aux_spec lneighbours pre test inhib steadym decreasingm fired_pre_group ((tr i) :: pgroup) None
  (* General case, all went well. *)
  | spn_fire_pre_aux_cons :
      forall (i : nat)
             (neighbours_t : neighbours_type)
             (pgroup : list trans_type)
             (modifiedm : marking_type)
             (option_final_couple : option (list trans_type * marking_type)),
      get_neighbours_spec lneighbours i (Some neighbours_t) ->
      check_all_edges_spec neighbours_t (pre (tr i)) (test (tr i)) (inhib (tr i)) steadym decreasingm
                           (Some true) ->
      update_marking_pre_spec (tr i) pre decreasingm (pre_pl neighbours_t) (Some modifiedm) ->
      spn_fire_pre_aux_spec lneighbours pre test inhib steadym modifiedm (fired_pre_group ++ [(tr i)]) pgroup
                            option_final_couple ->
      spn_fire_pre_aux_spec lneighbours pre test inhib steadym decreasingm fired_pre_group ((tr i) :: pgroup)
                            option_final_couple.
  
  (*** Correctness proof : spn_fire_pre_aux ***)
  Theorem spn_fire_pre_aux_correct :
    forall (lneighbours : list neighbours_type)
           (pre test inhib : weight_type) 
           (steadym : marking_type) 
           (decreasingm : marking_type)
           (fired_pre_group : list trans_type)
           (pgroup : list trans_type)
           (option_final_couple : option (list trans_type * marking_type)),
      spn_fire_pre_aux lneighbours pre test inhib steadym decreasingm fired_pre_group pgroup = option_final_couple ->
      spn_fire_pre_aux_spec lneighbours pre test inhib steadym decreasingm fired_pre_group pgroup option_final_couple.
  Proof.
    intros lneighbours pre test inhib steadym decreasingm fired_pre_group pgroup option_final_couple.
    functional induction (spn_fire_pre_aux lneighbours pre test inhib steadym decreasingm fired_pre_group pgroup)
               using spn_fire_pre_aux_ind; intros.
    (* Case pgroup = [] *)
    - rewrite <- H; apply spn_fire_pre_aux_nil.
    (* General case, all went well. *)
    - apply spn_fire_pre_aux_cons with (modifiedm := marking')
                                       (neighbours_t := neighbours_t).
      + apply get_neighbours_correct; auto.
      + apply check_all_edges_correct; auto.
      + apply update_marking_pre_correct; auto.
      + apply IHo; auto.
    (* Case update_marking_pre error. *)
    - rewrite <- H; apply spn_fire_pre_aux_update_err with (neighbours_t := neighbours_t).
      + apply get_neighbours_correct; auto.
      + apply check_all_edges_correct; auto.
      + apply update_marking_pre_correct; auto.
    (* Case check_all_edges returns false. *)
    - apply spn_fire_pre_aux_edges_false with (neighbours_t := neighbours_t).
      + apply get_neighbours_correct; auto.
      + apply check_all_edges_correct; auto.
      + apply IHo; auto.
    (* Case check_all_edges returns an error. *)
    - rewrite <- H; apply spn_fire_pre_aux_edges_err with (neighbours_t := neighbours_t).
      + apply get_neighbours_correct; auto.
      + apply check_all_edges_correct; auto.
    (* Case get_neighbours returns an error. *)
    - rewrite <- H; apply spn_fire_pre_aux_neighbours_err.
      apply get_neighbours_correct; auto.
  Qed.

  (*** Completeness proof : spn_fire_pre_aux ***)
  Theorem spn_fire_pre_aux_compl :
    forall (lneighbours : list neighbours_type)
           (pre test inhib : weight_type) 
           (steadym : marking_type) 
           (decreasingm : marking_type)
           (fired_pre_group : list trans_type)
           (pgroup : list trans_type)
           (option_final_couple : option (list trans_type * marking_type)),
      spn_fire_pre_aux_spec lneighbours pre test inhib steadym decreasingm fired_pre_group pgroup option_final_couple ->
      spn_fire_pre_aux lneighbours pre test inhib steadym decreasingm fired_pre_group pgroup = option_final_couple.
  Proof.
    intros lneighbours pre test inhib steadym decreasingm fired_pre_group
           pgroup option_final_couple Hspec.
    induction Hspec.
    (* Case spn_fire_pre_aux_nil *)
    - simpl; auto.
    (* Case spn_fire_pre_aux_neighbours_err *)
    - simpl; apply get_neighbours_compl in H; rewrite H; auto.
    (* Case spn_fire_pre_aux_edges_err *)
    - simpl.
      apply get_neighbours_compl in H; rewrite H.
      apply check_all_edges_compl in H0; rewrite H0; auto.
    (* Case spn_fire_pre_aux_edges_false *)
    - simpl.
      apply get_neighbours_compl in H; rewrite H.
      apply check_all_edges_compl in H0; rewrite H0; rewrite IHHspec; auto.
    (* Case spn_fire_pre_aux_update_err *)
    - simpl.
      apply get_neighbours_compl in H; rewrite H.
      apply check_all_edges_compl in H0; rewrite H0; auto.
      apply update_marking_pre_compl in H1; rewrite H1; auto.
    (* Case spn_fire_pre_aux_cons *)
    - simpl.
      apply get_neighbours_compl in H; rewrite H.
      apply check_all_edges_compl in H0; rewrite H0; auto.
      apply update_marking_pre_compl in H1; rewrite H1; auto.
  Qed.
  
  (*  
   * Function : Wrapper function around spn_fire_pre_aux.
   *)
  Definition spn_fire_pre
             (lneighbours : list neighbours_type)
             (pre test inhib : weight_type) 
             (steadym : marking_type) 
             (decreasingm : marking_type)
             (cfgroup : list trans_type) : option (list trans_type * marking_type) :=
    spn_fire_pre_aux lneighbours pre test inhib steadym decreasingm [] cfgroup.

  Functional Scheme spn_fire_pre_ind := Induction for spn_fire_pre Sort Prop.

  (*** Formal specification : spn_fire_pre ***)
  Inductive spn_fire_pre_spec
            (lneighbours : list neighbours_type)
            (pre test inhib : weight_type) 
            (steadym : marking_type) 
            (decreasingm : marking_type)
            (pgroup : list trans_type) : option (list trans_type * marking_type) -> Prop :=
  | spn_fire_pre_cons :
      forall (option_final_couple : option (list trans_type * marking_type)),
        spn_fire_pre_aux_spec lneighbours pre test inhib steadym decreasingm [] pgroup
                              option_final_couple ->
        spn_fire_pre_spec lneighbours pre test inhib steadym decreasingm pgroup
                          option_final_couple.

  (*** Correctness proof : spn_fire_pre ***)
  Theorem spn_fire_pre_correct :
    forall (lneighbours : list neighbours_type)
           (pre test inhib : weight_type) 
           (steadym decreasingm : marking_type) 
           (pgroup : list trans_type)
           (option_final_couple : option (list trans_type * marking_type)),
      spn_fire_pre lneighbours pre test inhib steadym decreasingm pgroup = option_final_couple ->
      spn_fire_pre_spec lneighbours pre test inhib steadym decreasingm pgroup option_final_couple.
  Proof.
    intros lneighbours pre test inhib steadym decreasingm pgroup option_final_couple;
    functional induction (spn_fire_pre lneighbours pre test inhib steadym decreasingm pgroup)
               using spn_fire_pre_ind; intros.
    apply spn_fire_pre_cons; apply spn_fire_pre_aux_correct in H; auto.
  Qed.

  (*** Completeness proof : spn_fire_pre ***)
  Theorem spn_fire_pre_compl :
    forall (lneighbours : list neighbours_type)
           (pre test inhib : weight_type) 
           (steadym decreasingm : marking_type) 
           (pgroup : list trans_type)
           (option_final_couple : option (list trans_type * marking_type)),
    spn_fire_pre_spec lneighbours pre test inhib steadym decreasingm pgroup option_final_couple ->
    spn_fire_pre lneighbours pre test inhib steadym decreasingm pgroup = option_final_couple.
  Proof.
    intros lneighbours pre test inhib steadym decreasingm pgroup option_final_couple Hspec;
      elim Hspec;
      intros.
    unfold spn_fire_pre; apply spn_fire_pre_aux_compl in H; auto. 
  Qed.
  
  (*
   * Function : Returns the list of pre
   *            Apply spn_fire_pre over ALL priority group of transitions. 
   *            Begin with initial marking; End with half fired marking.  
   *            "fired_pre_transitions" is empty at first. 
   *)
  Fixpoint spn_map_fire_pre_aux
           (lneighbours : list neighbours_type)
           (pre test inhib : weight_type)
           (steadym decreasingm : marking_type)
           (pre_fired_transitions : list trans_type)
           (priority_groups : list (list trans_type)) :
    option (list trans_type * marking_type) :=
    match priority_groups with
    (* Loops over all priority group of transitions (prgroup) and
     * calls spn_fire_pre. *)
    | pgroup :: pgroups_tail =>
      match (spn_fire_pre lneighbours pre test inhib steadym decreasingm pgroup) with
      (* If spn_fire_pre succeeds, then adds the fired transitions
       * in pre_fired_transitions list. *)
      | Some (pre_fired_trs, decreasedm) =>
        spn_map_fire_pre_aux lneighbours pre test inhib steadym decreasedm
                             (pre_fired_transitions ++ pre_fired_trs) pgroups_tail
      (* Case of error! *)
      | None => None
      end
    | [] => Some (pre_fired_transitions, decreasingm)
    end.

  Functional Scheme spn_map_fire_pre_aux_ind := Induction for spn_map_fire_pre_aux Sort Prop.
  
  (*** Formal specification : spn_map_fire_pre_aux ***)
  Inductive spn_map_fire_pre_aux_spec
            (lneighbours : list neighbours_type)
            (pre test inhib : weight_type)
            (steadym decreasingm : marking_type)
            (pre_fired_transitions : list trans_type) :
    list (list trans_type) -> option (list trans_type * marking_type) -> Prop :=
  | spn_map_fire_pre_aux_nil :
      spn_map_fire_pre_aux_spec lneighbours pre test inhib steadym decreasingm pre_fired_transitions []
                                (Some (pre_fired_transitions, decreasingm))
  | spn_map_fire_pre_aux_cons :
      forall (pgroup pre_fired_trs : list trans_type)
             (decreasedm : marking_type)
             (priority_groups : list (list trans_type))
             (option_final_couple : option (list trans_type * marking_type)),
        spn_fire_pre_spec lneighbours pre test inhib steadym decreasingm pgroup
                          (Some (pre_fired_trs, decreasedm)) ->
        spn_map_fire_pre_aux_spec lneighbours pre test inhib steadym decreasedm (pre_fired_transitions ++ pre_fired_trs)
                                  priority_groups
                                  option_final_couple ->
        spn_map_fire_pre_aux_spec lneighbours pre test inhib steadym decreasingm pre_fired_transitions
                                  (pgroup :: priority_groups)
                                  option_final_couple
  | spn_map_fire_pre_aux_err :
      forall (pgroup : list trans_type)
             (priority_groups : list (list trans_type)),
        spn_fire_pre_spec lneighbours pre test inhib steadym decreasingm pgroup None ->
        spn_map_fire_pre_aux_spec lneighbours pre test inhib steadym decreasingm pre_fired_transitions
                                  (pgroup :: priority_groups) None.

  (*** Correctness proof : spn_map_fire_pre_aux ***)
  Theorem spn_map_fire_pre_aux_correct :
    forall (lneighbours : list neighbours_type)
           (pre test inhib : weight_type)
           (steadym decreasingm : marking_type)
           (priority_groups : list (list trans_type))
           (pre_fired_transitions : list trans_type)
           (option_final_couple : option (list trans_type * marking_type)),
      spn_map_fire_pre_aux lneighbours pre test inhib steadym decreasingm
                           pre_fired_transitions priority_groups = option_final_couple ->
      spn_map_fire_pre_aux_spec lneighbours pre test inhib steadym decreasingm
                                pre_fired_transitions priority_groups option_final_couple.
  Proof.
    intros lneighbours pre test inhib steadym decreasingm priority_groups
           pre_fired_transitions option_final_couple;
    functional induction (spn_map_fire_pre_aux lneighbours pre test inhib steadym decreasingm
                                               pre_fired_transitions priority_groups)
               using spn_map_fire_pre_aux_ind;
    intros.
    (* Case priority_groups = [] *)
    - rewrite <- H; apply spn_map_fire_pre_aux_nil.
    (* General case *)
    - apply spn_map_fire_pre_aux_cons with (pre_fired_trs := pre_fired_trs)
                                           (decreasedm := decreasedm).
      + apply spn_fire_pre_correct; auto.
      + apply IHo; rewrite H; auto.
    (* Case of error *)
    - rewrite <- H; apply spn_map_fire_pre_aux_err.
      apply spn_fire_pre_correct; auto.
  Qed.

  (*** Completeness proof : spn_map_fire_pre_aux ***)
  Theorem spn_map_fire_pre_aux_compl :
    forall (lneighbours : list neighbours_type)
           (pre test inhib : weight_type)
           (steadym decreasingm : marking_type)
           (priority_groups : list (list trans_type))
           (pre_fired_transitions : list trans_type)
           (option_final_couple : option (list trans_type * marking_type)),
      spn_map_fire_pre_aux_spec lneighbours pre test inhib steadym decreasingm
                                pre_fired_transitions priority_groups option_final_couple ->
      spn_map_fire_pre_aux lneighbours pre test inhib steadym decreasingm
                           pre_fired_transitions priority_groups = option_final_couple.
  Proof.
    intros lneighbours pre test inhib steadym decreasingm
           priority_groups pre_fired_transitions option_final_couple Hspec;
    elim Hspec;
    intros.
    (* Case spn_map_fire_pre_aux_nil *)
    - simpl; auto.
    (* Case spn_map_fire_pre_aux_cons *)
    - simpl; apply spn_fire_pre_compl in H; rewrite H; rewrite H1; auto.
    (* Case spn_map_fire_pre_aux_err *)
    - simpl; apply spn_fire_pre_compl in H; rewrite H; auto.
  Qed.
  
  (*
   * Function : Wrapper around spn_map_fire_pre_aux function. 
   *            Update the marking by consuming
   *            the tokens in pre-condition places.            
   *)
  Definition spn_map_fire_pre
             (lneighbours : list neighbours_type)
             (pre test inhib : weight_type)
             (steadym : marking_type)
             (priority_groups : list (list trans_type)) :
    option (list trans_type * marking_type) :=
    spn_map_fire_pre_aux lneighbours pre test inhib steadym steadym [] priority_groups.

  (*** Formal specification : spn_map_fire_pre ***)
  Inductive spn_map_fire_pre_spec
            (lneighbours : list neighbours_type)
            (pre test inhib : weight_type)
            (steadym : marking_type)
            (priority_groups : list (list trans_type)) :
    option (list trans_type * marking_type) -> Prop :=
  | spn_map_fire_pre_cons :
      forall (option_final_couple : option (list trans_type * marking_type)),
      spn_map_fire_pre_aux_spec lneighbours pre test inhib steadym steadym [] priority_groups
                                option_final_couple ->
      spn_map_fire_pre_spec lneighbours pre test inhib steadym priority_groups option_final_couple.

  (*** Correctness proof : spn_map_fire_pre ***)
  Theorem spn_map_fire_pre_correct :
    forall (lneighbours : list neighbours_type)
           (pre test inhib : weight_type)
           (steadym : marking_type)
           (priority_groups : list (list trans_type))
           (option_final_couple : option (list trans_type * marking_type)),
    spn_map_fire_pre lneighbours pre test inhib steadym priority_groups = option_final_couple ->
    spn_map_fire_pre_spec lneighbours pre test inhib steadym priority_groups
                          option_final_couple.  
  Proof.
    intros lneighbours pre test inhib steadym priority_groups option_final_couple H.
    apply spn_map_fire_pre_cons.
    apply spn_map_fire_pre_aux_correct.
    auto.
  Qed.

  (*** Completeness proof : spn_map_fire_pre ***)
  Theorem spn_map_fire_pre_compl :
    forall (lneighbours : list neighbours_type)
           (pre test inhib : weight_type)
           (steadym : marking_type)
           (priority_groups : list (list trans_type))
           (option_final_couple : option (list trans_type * marking_type)),
      spn_map_fire_pre_spec lneighbours pre test inhib steadym priority_groups
                            option_final_couple ->
      spn_map_fire_pre lneighbours pre test inhib steadym priority_groups = option_final_couple.
  Proof.
    intros lneighbours pre test inhib steadym priority_groups option_final_couple H.
    elim H; intros.
    unfold spn_map_fire_pre.
    apply spn_map_fire_pre_aux_compl; auto.
  Qed.
  
  (* 
   * Function : Given a marking "m_intermediate", resulting of the call
   *            of the function spn_map_fire_pre, and after
   *            that a given group of transs has been pre-fired
   *            (the "pre_fired_transitions" list),
   *            returns the marking increased by the post-condition edges.
   *)
  Fixpoint fire_post
           (lneighbours : list neighbours_type)
           (post : weight_type)
           (increasingm : marking_type)
           (pre_fired_transitions : list trans_type) : option marking_type :=
    match pre_fired_transitions with
    | (tr i) :: tail  =>
      match get_neighbours lneighbours i with
      (* Updates the marking
       * for all neighbour post places of (tr i). *)
      | Some neighbours_t =>
        match (update_marking_post (tr i) post increasingm (post_pl neighbours_t)) with
        | Some new_marking => (fire_post lneighbours post new_marking tail)
        (* Something went wrong, case of error. *)
        | None => None
        end
      (* If transition (tr i) has no neighbours, then error. *)
      | None => None
      end
    | []  => Some increasingm
    end.

  (*** Formal specification : fire_post ***)
  Inductive fire_post_spec
            (lneighbours : list neighbours_type)
            (post : weight_type) 
            (increasingm : marking_type) :
    list trans_type -> option marking_type -> Prop :=
  (* Case pre_fired_transitions = [] *)
  | fire_post_nil :
      fire_post_spec lneighbours post increasingm [] (Some increasingm)
  (* Case get_neighbours returns an error *)
  | fire_post_neighbours_err :
      forall (i : nat) (pre_fired_transitions : list trans_type),
        get_neighbours_spec lneighbours i None ->
        fire_post_spec lneighbours post increasingm ((tr i) :: pre_fired_transitions) None
  (* General case *)
  | fire_post_cons :
      forall (i : nat)
             (neighbours_t : neighbours_type)
             (pre_fired_transitions : list trans_type)
             (modifiedm : marking_type)
             (optionm : option marking_type),
        get_neighbours_spec lneighbours i (Some neighbours_t) ->
        update_marking_post_spec (tr i) post increasingm (post_pl neighbours_t) (Some modifiedm) ->
        fire_post_spec lneighbours post modifiedm pre_fired_transitions optionm ->
        fire_post_spec lneighbours post increasingm ((tr i) :: pre_fired_transitions) optionm
  (* Case update_marking_post returns an error. *)
  | fire_post_update_err :
      forall (i : nat)
             (neighbours_t : neighbours_type)
             (pre_fired_transitions : list trans_type),
        get_neighbours_spec lneighbours i (Some neighbours_t) ->
        update_marking_post_spec (tr i) post increasingm (post_pl neighbours_t) None ->
        fire_post_spec lneighbours post increasingm ((tr i) :: pre_fired_transitions) None.

  Functional Scheme fire_post_ind := Induction for fire_post Sort Prop.
  
  (*** Correctness proof : fire_post ***)
  Theorem fire_post_correct :
    forall (lneighbours : list neighbours_type)
           (post : weight_type) 
           (increasingm : marking_type) 
           (pre_fired_transitions : list trans_type)
           (optionm : option marking_type),
    fire_post lneighbours post increasingm pre_fired_transitions = optionm ->
    fire_post_spec lneighbours post increasingm pre_fired_transitions optionm.
  Proof.
    intros lneighbours post increasingm pre_fired_transitions optionm;
    functional induction (fire_post lneighbours post increasingm pre_fired_transitions)
               using fire_post_ind;
    intros.
    (* Case fired_pre_group = [] *)
    - rewrite <- H; apply fire_post_nil; auto.
    (* General case. *)
    - apply fire_post_cons with (neighbours_t := neighbours_t)
                                (modifiedm := new_marking).
      + apply get_neighbours_correct; auto.
      + apply update_marking_post_correct; auto.
      + apply IHo; rewrite <- H; auto.
    (* Case update_marking_post returns an error. *)
    - rewrite <- H; apply fire_post_update_err with (neighbours_t := neighbours_t).
      + apply get_neighbours_correct; auto.
      + apply update_marking_post_correct; auto.
    (* Case get_neighbours returns an error. *)
    - rewrite <- H; apply fire_post_neighbours_err.
      apply get_neighbours_correct; auto.
  Qed.

  (*** Completeness proof : fire_post ***)
  Theorem fire_post_compl :
    forall (lneighbours : list neighbours_type)
           (post : weight_type) 
           (increasingm : marking_type) 
           (pre_fired_transitions : list trans_type)
           (optionm : option marking_type),
      fire_post_spec lneighbours post increasingm pre_fired_transitions optionm ->
      fire_post lneighbours post increasingm pre_fired_transitions = optionm.
  Proof.
    intros lneighbours post increasingm pre_fired_transitions optionm H;
    elim H;
    intros.
    (* Case fire_post_nil *)
    - simpl; auto.
    (* Case fire_post_neighbours_err *)
    - simpl; apply get_neighbours_compl in H0; rewrite H0; auto.
    (* General case *)
    - simpl.
      apply get_neighbours_compl in H0; rewrite H0.
      apply update_marking_post_compl in H1; rewrite H1; auto.
    (* Case fire_post_update_err *)
    - simpl.
      apply get_neighbours_compl in H0; rewrite H0.
      apply update_marking_post_compl in H1; rewrite H1; auto.
  Qed.
  
  (*************************************************)
  (****************** SPN FIRE *********************)
  (*************************************************)

  (*
   * Function : Returns  "fired transitions (pre_fired_transitions)" + "final marking",
   *            composing fire_post with spn_map_fire_pre
   *)
  Definition spn_fire
             (lneighbours : list neighbours_type)
             (pre test inhib post : weight_type)
             (steadym : marking_type)
             (priority_groups : list (list trans_type)) :
    option (list trans_type * marking_type) :=
    (* Pre-fires the transitions in priority_groups. *)
    match (spn_map_fire_pre lneighbours pre test inhib steadym priority_groups) with 
    | Some (pre_fired_transitions, intermediatem) =>
      (* Post-fires the pre-fired transitions. *)
      match (fire_post lneighbours post intermediatem pre_fired_transitions) with
      | Some finalm => Some (pre_fired_transitions, finalm)
      (* If fire_post returned an error, then error. *)
      | None => None
      end
    (* If spn_map_fire_pre returned an error, then error. *)
    | None => None
    end.

  Functional Scheme spn_fire_ind := Induction for spn_fire Sort Prop.
  
  (*** Formal specification : spn_fire ***)
  Inductive spn_fire_spec
            (lneighbours : list neighbours_type)
            (pre test inhib post : weight_type)
            (steadym : marking_type)
            (priority_groups : list (list trans_type)) :
    option (list trans_type * marking_type) -> Prop :=
  (* General case *)
  | spn_fire_cons :
      forall (pre_fired_transitions : list trans_type)
             (intermediatem finalm : marking_type),
        spn_map_fire_pre_spec lneighbours pre test inhib steadym priority_groups
                              (Some (pre_fired_transitions, intermediatem)) ->
        fire_post_spec lneighbours post intermediatem pre_fired_transitions (Some finalm) ->
        spn_fire_spec lneighbours pre test inhib post steadym priority_groups
                      (Some (pre_fired_transitions, finalm))
  (* Case spn_map_fire_pre returns an error. *)
  | spn_fire_map_fire_pre_err :
      spn_map_fire_pre_spec lneighbours pre test inhib steadym priority_groups None ->
      spn_fire_spec lneighbours pre test inhib post steadym priority_groups None
  (* Case fire_post returns an error. *)
  | spn_fire_fire_post_err :
      forall (pre_fired_transitions : list trans_type)
             (intermediatem : marking_type),
        spn_map_fire_pre_spec lneighbours pre test inhib steadym priority_groups
                              (Some (pre_fired_transitions, intermediatem)) ->
        fire_post_spec lneighbours post intermediatem pre_fired_transitions None ->
        spn_fire_spec lneighbours pre test inhib post steadym priority_groups None.

  (*** Correctness proof : spn_fire ***)
  Theorem spn_fire_correct :
    forall (lneighbours : list neighbours_type)
           (pre test inhib post : weight_type)
           (steadym : marking_type)
           (priority_groups : list (list trans_type))
           (option_final_couple : option (list trans_type * marking_type)),
    spn_fire lneighbours pre test inhib post steadym priority_groups = option_final_couple ->
    spn_fire_spec lneighbours pre test inhib post steadym priority_groups option_final_couple.
  Proof.
    intros lneighbours pre test inhib post steadym priority_groups option_final_couple;
    functional induction (spn_fire lneighbours pre test inhib post steadym priority_groups)
               using spn_fire_ind;
    intros.
    (* General case *)
    - rewrite <- H; apply spn_fire_cons with (intermediatem := intermediatem).
      + apply spn_map_fire_pre_correct; auto.
      + apply fire_post_correct; auto.
    (* Case fire_post returns an error. *)
    - rewrite <- H; apply spn_fire_fire_post_err
                      with (pre_fired_transitions := pre_fired_transitions)
                           (intermediatem := intermediatem).
      + apply spn_map_fire_pre_correct; auto.
      + apply fire_post_correct; auto.
    (* Case spn_map_fire_pre returns an error. *)
    - rewrite <- H; apply spn_fire_map_fire_pre_err.
      apply spn_map_fire_pre_correct; auto.                             
  Qed.

  (*** Completeness proof : spn_fire ***)
  Theorem spn_fire_compl :
    forall (lneighbours : list neighbours_type)
           (pre test inhib post : weight_type)
           (steadym : marking_type)
           (priority_groups : list (list trans_type))
           (option_final_couple : option (list trans_type * marking_type)),
      spn_fire_spec lneighbours pre test inhib post steadym priority_groups option_final_couple ->
      spn_fire lneighbours pre test inhib post steadym priority_groups = option_final_couple.
  Proof.
    intros lneighbours pre test inhib post steadym priority_groups option_final_couple Hspec.
    elim Hspec; intros; unfold spn_fire.
    (* Case spn_fire_cons *)
    + apply spn_map_fire_pre_compl in H; rewrite H.
      apply fire_post_compl in H0; rewrite H0; auto.
    (* Case spn_fire_map_fire_pre_err *)
    + apply spn_map_fire_pre_compl in H; rewrite H; auto.
    (* Case spn_fire_fire_post_err *)
    + apply spn_map_fire_pre_compl in H; rewrite H.
      apply fire_post_compl in H0; rewrite H0; auto.
  Qed.
  
End FireSpn.

(*==========================================================*)
(*================= SPN CYCLE EVOLUTION ====================*)
(*==========================================================*)

Section AnimateSpn.
  
  (*  
   * Function : Returns the resulting Petri net after all the sensitized
   *            transitions in spn have been fired, and returns
   *            the list of lists containing these transitions.
   *
   *)
  Definition spn_cycle (spn : SPN) : (list (list trans_type)) * SPN :=
    match spn with
    | (mk_SPN places transs pre post test inhib m (mk_prior cfgroups) lneighbours) =>
      let (fired_groups, nextm) := (spn_fire lneighbours pre test inhib post m cfgroups) in
      (fired_groups, (mk_SPN places transs pre post test inhib nextm (mk_prior cfgroups) lneighbours))
    end.

  (*** Formal specification : spn_cycle_spec ***)
  Inductive spn_cycle_spec (spn : SPN) :
    (list (list trans_type)) * SPN -> Prop :=
  | spn_cycle_cons :
      forall (places : list place_type)
             (transs : list trans_type)
             (pre post test inhib : weight_type)
             (m nextm : marking_type)
             (fired_groups cfgroups : list (list trans_type))
             (lneighbours : list neighbours_type),
        spn = (mk_SPN places transs pre post test inhib m (mk_prior cfgroups) lneighbours) ->
        spn_fire_spec lneighbours pre test inhib post m cfgroups (fired_groups, nextm) ->
        spn_cycle_spec spn (fired_groups, (mk_SPN places transs pre post test inhib nextm
                                                  (mk_prior cfgroups) lneighbours)).

  Functional Scheme spn_cycle_ind := Induction for spn_cycle Sort Prop.
  
  (*** Correctness proof : spn_cycle ***)
  Theorem spn_cycle_correct :
    forall (spn spn' : SPN)
           (fired_groups : list (list trans_type)),
    spn_cycle spn = (fired_groups, spn') -> spn_cycle_spec spn (fired_groups, spn').
  Proof.
    intros; functional induction (spn_cycle spn) using spn_cycle_ind; intros.
    rewrite <- H; apply spn_cycle_cons with (m := m).
    - auto.
    - apply spn_fire_correct; auto.
  Qed.

  (*** Completeness proof : spn_cycle ***)
  Theorem spn_cycle_compl :
    forall (spn spn' : SPN)
           (fired_groups : list (list trans_type)),
    spn_cycle_spec spn (fired_groups, spn') -> spn_cycle spn = (fired_groups, spn').
  Proof.
    intros; elim H; intros.
    unfold spn_cycle; rewrite H0.
    apply spn_fire_compl in H1; rewrite H1; auto.
  Qed.

  (*******************************************)
  (******** ANIMATING DURING N CYCLES ********)
  (*******************************************)

  (* 
   * Function : Returns the list of (transitions_fired(i), marking(i))
   *            for each cycle i, from 0 to n, representing the evolution
   *            of the Petri net spn.
   *)
  Fixpoint spn_animate (spn : SPN) (n : nat) :
    list ((list (list trans_type)) * marking_type) :=
    match n with
    | O => [ ([], []) ]
    | S n' => let (fired_groups_at_n, spn_at_n) := (spn_cycle spn) in
             (fired_groups_at_n, (marking spn_at_n)) :: (spn_animate spn_at_n n')
    end.

  Functional Scheme spn_animate_ind := Induction for spn_animate Sort Prop.
  
  (*** Formal specification : spn_animate ***)
  Inductive spn_animate_spec (spn : SPN) :
    nat -> list ((list (list trans_type)) * marking_type) -> Prop :=
  | spn_animate_0 : spn_animate_spec spn 0 [([], [])]
  | spn_animate_cons :
      forall (n : nat)
             (fired_groups_at_n : list (list trans_type))
             (spn_at_n : SPN)
             (marking_evolution : list ((list (list trans_type)) * marking_type)),
      spn_cycle_spec spn (fired_groups_at_n, spn_at_n) ->
      spn_animate_spec spn_at_n n marking_evolution ->
      spn_animate_spec spn (S n) ((fired_groups_at_n, (marking spn_at_n)) :: marking_evolution).
  
  (*** Correctness proof : spn_animate***)
  Theorem spn_animate_correct :
    forall (spn :SPN)
           (n : nat)
           (marking_evolution : list ((list (list trans_type)) * marking_type)),
    spn_animate spn n = marking_evolution -> spn_animate_spec spn n marking_evolution.
  Proof.                                                                                
    intros spn n; functional induction (spn_animate spn n) using spn_animate_ind.
    (* Case n = 0 *)
    - intros; rewrite <- H; apply spn_animate_0.
    (* General case *)
    - intros; rewrite <- H; apply spn_animate_cons.
      + apply spn_cycle_correct in e0; auto.
      + apply IHl; auto.
  Qed.

  (*** Completeness proof : spn_animate ***)
  Theorem spn_animate_compl :
    forall (spn :SPN)
           (n : nat)
           (marking_evolution : list ((list (list trans_type)) * marking_type)),
      spn_animate_spec spn n marking_evolution -> spn_animate spn n = marking_evolution.
  Proof.                                                                                
    intros; elim H; intros.
    (* Case spn_animate_0 *)
    - simpl; auto.
    (* Case spn_animate_cons *)
    - simpl; apply spn_cycle_compl in H0; rewrite H0.
      rewrite H2; auto.
  Qed.

End AnimateSpn.

(*****************************************************************)
(*****************************************************************)
(**** HOW TO get the classes of transitions...    from what ? ****)
(*************** sections sorting ********************************)

(*
Require Import Coq.Sorting.Sorted. Search sort.

Section insertion_sort.


  Print prior_type1. Print prior_type2.
  Fixpoint insert (a : trans_type)
                  (l : list trans_type)
                  (prior1 : prior_type1) : list trans_type :=
    match l with
    | nil  => [a]
    | b :: l' => match prior1 with
                 | mk_prior_type1 rel irre assym trans =>
                   if (rel a b)
                   then a :: l
                   else b :: (insert a l' prior1)
               end
    end.
  
  Fixpoint sort (l : list trans_type)
                (prior1 : prior_type1) : list trans_type :=
    match l with
    | [] => []
    | a :: l' => insert a (sort l' prior1) prior1
    end.
  
  (* Fixpoint find_highest (A:Type) (l:list A) : (A * list A) :=
    match l with
    | nil => (a, nil)
    | b::l' => if leb a b
               then find_highest b l'
               else find_highest a l'
    end.*)

  Definition sort_transs (prior1 : prior_type1)
                         (l : list trans_type) : list trans_type := (sort l prior1).
  
End insertion_sort.

(********************************************************)

Section structural_conflicts.
  Variable pre : weight_type.
  (* Variable places : list place_type. *)

  Fixpoint common_pre
           (t t' : trans_type)
           (places : list place_type)
    : bool :=
    match places with
    | [ ] => false
    | p :: places' => match ((pre t p), (pre t' p)) with
                      | (Some _, Some _) => true
                      | (_, _) => common_pre
                                    t t'
                                    places'                                  
                      end
    end.

  Fixpoint common_pre_with_somebody
           (t : trans_type) (sometranss : list trans_type)
           (places : list place_type)
    : bool :=
    match sometranss with
    | [ ] => false
    | tr :: lesstranss => if common_pre
                               t tr
                               places
                          then true
                          else common_pre_with_somebody
                                 t lesstranss
                                 places
    end.

  Fixpoint somebody_common_pre_with_somebody
           (sometranss1 sometranss2 : list trans_type)
           (places : list place_type)
    : bool :=
    match sometranss1 with
    | [ ] => false
    | t :: lesstranss1 => if common_pre_with_somebody
                               t sometranss2
                               places
                          then true
                          else somebody_common_pre_with_somebody
                                 lesstranss1 sometranss2
                                 places
  end.    

  Search list.
  Section fusionning_lists.
    Variables (A : Type).
    
    Fixpoint fusion_two_lists
             (L : list (list A))
             (l1 l2 : list A)
      (* l1 , l2  in L *)
      : list (list A) :=
      (*match L with
    | l1 :: L'  => fusion_two_lists
                     L'
                     l1 l2
    | l2 :: L'  => fusion_two_lists
                     L'
                     l1 l2
    | _ :: L'   => fusion_two_lists
                     L
                     l1 l2
    | [ ]      => (l1 ++ l2) :: L 
    end.*)
      [].
  End fusionning_lists.
  
  Fixpoint merging_list_in_list_of_lists
           (L : list (list trans_type))      
           (sometranss1 : list trans_type)
           (places : list place_type) {struct L}
    : list (list trans_type) :=
    match L with
    | [] => L
    | sometranss2 :: L' => if somebody_common_pre_with_somebody
                                sometranss1 sometranss2
                                places
                           then ((sometranss1 ++ sometranss2) :: L')
                                  
                           else sometranss2 :: (merging_list_in_list_of_lists
                                                  L'
                                                  sometranss1
                                                  places)
  end.

  Definition building_structural_conflicts
             (transs : list (list trans_type))
             (places : list place_type)
    : list (list trans_type) :=
    match transs with
    | []  => transs
    | l :: tail  => merging_list_in_list_of_lists
                      tail
                      l
                      (places : list place_type)
    end.

End structural_conflicts.

Section effective_conflicts.
  Variable struct_conflicts : list (list trans_type).
  Variable firable_transs : list trans_type.

  Fixpoint conforming_data_pruning
           (struct_conflicts : list (list trans_type))
           (firable_transs : list trans_type)
    : list (list trans_type) :=
    [].
  (* il suffit de garder de struct_conflicts
  en supprimant toutes les transitions n'apparaissant pas dans firable_transs *)

  Print SITPN.
  Fixpoint conforming_data_ordering
           (firable_transs : list (list trans_type)) (* better *)
           (priority : prior_type2) : 
    list (list trans_type) :=
    [].
  (* il suffit d'ordonner chacune des listes *)


  Definition to_be_fired
             (conformed_firable : list (list trans_type))
             (sitpn : SITPN) : SITPN :=
    sitpn.
  (* on peut tirer les transitions autant que possible 
 il suffit de tirer les premières de listes (updating le marking)
en retirant les transitions suivantes qui ne sont plus tirables
 
et en recommançant avec la liste de listes restante
qui n'est pas forcement plus courte (zut !) *)

  
End effective_conflicts.

*)
