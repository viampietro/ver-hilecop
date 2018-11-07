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

(* There are 4 kinds of edges : pred, post, pred_inhib, pred_test 
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

Section MarkingType.
  
  (* The marking in a Petri net is represented as
   * a list of couples (index, nboftokens), where index is
   * the index of a place in the Petri net, and nboftokens
   * is the number of tokens currently assoicated to the place.
   *)
  Definition marking_type := list (nat * nat).

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
    | [] => None
    end.

  Functional Scheme get_m_ind := Induction for get_m Sort Prop.

  (*** Formal specification : get_m ***)
  Inductive get_m_spec : marking_type -> nat -> option nat -> Prop :=
  | get_m_none :
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
    do 2 intro; functional induction (get_m m index) using get_m_ind; intros.
    (* Case m = []. *)
    - rewrite <- H; apply get_m_none.
    (* Case if is true. *)
    - rewrite <- H.
      apply get_m_if with (m' := tail) (i := i);
      [auto | rewrite Nat.eqb_sym in e1; apply beq_nat_true in e1; auto].
    (* Case else *)
    - apply get_m_else with (i := i) (n := nboftokens) (m' := tail).
      + auto.
      + rewrite Nat.eqb_sym in e1. apply beq_nat_false in e1. assumption.
      + rewrite <- H. apply IHo with (opt_nboftokens := (get_m tail index)). auto.
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

End MarkingType.

(*******************************************************************)
(**********************  Priority relation *************************)
(* to DETERMINE the Petri net (along with the imperative semantic) *)
(*******************************************************************)

(* Inductive or Definition ?? *) 
Inductive prior_type : Set := mk_prior { Lol : list (list trans_type); }.

Section NeighboursType.
  
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
  | get_neighbours_none :
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
    do 3 intro;
      functional induction (get_neighbours lneighbours idx) using get_neighbours_ind; intros.
    (* Case neighbours = None *)
    - rewrite <- H; apply get_neighbours_none with (idx := idx).
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
    (* Case get_neighbours_none *)
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
  
End NeighboursType.

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
  assert (H0 : t0 = mk_trans n). { firstorder. }  
  assert (H1 : t1 = mk_trans n). { firstorder. }                   
  unfold beq_transs. rewrite H1. rewrite H0.
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

(*******************************************************)
(*** Defines the structure of Synchronous Petri Nets ***)
(*******************************************************)

(* Let's suppose 
 * 1) some properties on the places
 *    - all places have different index (NoDup)
 *   
 * 2) some properties on the transitions
 *    - all transitions are different (NoDup ...)
 *
 * 3) priority/prior_type, list of sublists of transs 
 *    A sublist in priority denotes a group of transitions
 *    being in structural conflict.
 *
 * 4) some properties on the neighbours list :
 *    - no isolated transitions are possible =>
 *      ~exists t, ((pre t) = None /\ (test t) = None /\ (inhib t) = None) \/ (post t) = None ->
 *      ((fst (neighbours t)) <> [] \/ (snd (neighbours t)) <> [] \/ (trd (neighbours t)) <> [])
 *      /\ ((fth (neighbours t)) <> [])
 *)


Structure SPN : Set :=
  mk_SPN {
      places : list place_type;
      transs : list trans_type;
      pre : weight_type;
      post : weight_type;
      test : weight_type;
      inhib : weight_type;
      marking : marking_type;                     
      priority : prior_type;

      (* Contains the list of pre places, 
       * test places, inhib places and post places associated
       * with each transition of the SPN. *)
      lneighbours : list neighbours_type;

      (* Properties on places and transitions *)
      (* nodup_places : NoDup places; *)
      (* nodup_transs : NoDup transs; *)

  }.

(*====================================================*)
(*=============== MARKING SECTION  ===================*)
(*====================================================*)
Section Marking.
 
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
             (nboftokens : option nat_star) : marking_type :=
    match p with
    | (pl i) => match nboftokens with
                | None => m
                | Some (mk_nat_star n' _) => let opt_n := get_m m i in
                                             match opt_n with
                                             (* If couple with first member i doesn't exist
                                              * in m, then add such a couple in m. *)
                                             | None => (i, (op 0 n')) :: m 
                                             (* The couple (i, n) to remove must be unique. *)
                                             | Some n =>
                                               (replace_occ prodnat_eq_dec (i, n) (i, (op n n')) m)
                                             end
                end
    end.

  Functional Scheme modify_m_ind := Induction for modify_m Sort Prop.

  (*** Formal specification : modify_m ***)
  Inductive modify_m_spec
            (m : marking_type)
            (p : place_type)
            (op : nat -> nat -> nat) :
    option nat_star -> marking_type -> Prop :=
  | modify_m_none :
      modify_m_spec m p op None m
  (* Case place of index i is not in the marking. *)
  | modify_m_some_add :
      forall (nboftokens : option nat_star)
             (i n' : nat)
             (is_positive : n' > 0),
      p = (pl i) ->
      nboftokens = Some (mk_nat_star n' is_positive) ->
      get_m_spec m i None ->
      modify_m_spec m p op nboftokens ((i, (op 0 n')) :: m)
  (* Case place of index i exists in the marking *)
  | modify_m_some_repl :
      forall (nboftokens : option nat_star)
             (i n n' : nat)
             (is_positive : n' > 0)
             (m' : marking_type),
      p = (pl i) ->
      nboftokens = Some (mk_nat_star n' is_positive) ->
      get_m_spec m i (Some n) ->
      replace_occ_spec prodnat_eq_dec (i, n) (i, (op n n')) m m' ->
      modify_m_spec m p op nboftokens m'.

  (*** Correctness proof : modify_m ***)
  Theorem modify_m_correct :
    forall (m m' : marking_type)
           (p : place_type)
           (op : nat -> nat -> nat)
           (nboftokens : option nat_star),
    modify_m m p op nboftokens = m' -> modify_m_spec m p op nboftokens m'.
  Proof.
    do 5 intro; functional induction (modify_m m p op nboftokens)
                           using modify_m_ind; intros.
    (* Case (pl i) exists in marking m *)
    - apply modify_m_some_repl with (i := i)
                                    (n := n0)
                                    (n' := n')
                                    (is_positive := _x).
      + auto.
      + auto.
      + apply get_m_correct in e2; auto.
      + apply replace_occ_correct in H; auto.
    (* Case (pl i) doesn't exist in marking m *)
    - rewrite <- H; apply modify_m_some_add with (is_positive := _x).
      + auto.
      + auto.
      + apply get_m_correct in e2; auto.
    (* Case nboftokens is None *)
    - rewrite <- H; apply modify_m_none.
  Qed.

  (*** Completeness proof : modify_m ***)
  Theorem modify_m_compl :
    forall (m m' : marking_type)
           (p : place_type)
           (op : nat -> nat -> nat)
           (nboftokens : option nat_star),
    modify_m_spec m p op nboftokens m' -> modify_m m p op nboftokens = m'.
  Proof.
    intros; induction H.
    - unfold modify_m; elim p; auto.
    - unfold modify_m; rewrite H; rewrite H0; apply get_m_compl in H1; rewrite H1; auto.
    - unfold modify_m; rewrite H; rewrite H0; apply get_m_compl in H1; rewrite H1.
      apply replace_occ_compl in H2; auto.      
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
           (places : list place_type) : marking_type :=
    match places with
    | p :: tail => update_marking_pre t pre (modify_m m p Nat.sub (pre t p)) tail
    | [] => m
    end.

  Functional Scheme update_marking_pre_ind := Induction for update_marking_pre Sort Prop.
  
  (*** Formal specification : update_marking_pre ***)
  Inductive update_marking_pre_spec
            (t : trans_type)
            (pre : weight_type)
            (m : marking_type) :
    list place_type -> marking_type -> Prop :=
  | update_marking_pre_nil :
      update_marking_pre_spec t pre m [] m
  | update_marking_pre_cons :
      forall (places : list place_type)
             (m' finalm: marking_type)
             (p : place_type),
      modify_m_spec m p Nat.sub (pre t p) m' ->
      update_marking_pre_spec t pre m' places finalm ->
      update_marking_pre_spec t pre m (p :: places) finalm.

  (*** Correctness proof : update_marking_pre ***)
  Theorem update_marking_pre_correct :
    forall (t : trans_type)
           (pre : weight_type)
           (places : list place_type)
           (m finalm : marking_type),
    update_marking_pre t pre m places = finalm -> update_marking_pre_spec t pre m places finalm.
  Proof.
    intros t pre places m finalm;
    functional induction (update_marking_pre t pre m places)
               using update_marking_pre_ind;
    intros.
    (* Case places is nil *)
    - rewrite <- H; apply update_marking_pre_nil.
    (* General case *)
    - apply update_marking_pre_cons with (m' := (modify_m m p Nat.sub (pre t p))).
      + apply modify_m_correct; auto.
      + apply (IHm0 H); auto.
  Qed.

  (*** Completeness proof : update_marking_pre ***)
  Theorem update_marking_pre_compl :
    forall (t : trans_type)
           (pre : weight_type)
           (places : list place_type)
           (m finalm : marking_type),
    update_marking_pre_spec t pre m places finalm -> update_marking_pre t pre m places = finalm.
  Proof.
    intros t pre places m finalm Hspec; induction Hspec.
    (* Case update_marking_pre_nil *)
    - simpl; auto.
    (* Case update_marking_pre_cons *)
    - simpl; apply modify_m_compl in H; rewrite H; rewrite IHHspec; auto.
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
           (places : list place_type) : marking_type :=
    match places with
    | p :: tail => update_marking_post t post (modify_m m p Nat.add (post t p)) tail
    | [] => m
    end.

  Functional Scheme update_marking_post_ind := Induction for update_marking_post Sort Prop.

  (*** Formal specification : update_marking_post ***)
  Inductive update_marking_post_spec
            (t : trans_type)
            (post : weight_type)
            (m : marking_type) :
    list place_type -> marking_type -> Prop :=
  | update_marking_post_nil :
      update_marking_post_spec t post m [] m
  | update_marking_post_cons :
      forall (p : place_type)
             (m' finalm : marking_type)
             (places : list place_type),
      modify_m_spec m p Nat.add (post t p) m' ->
      update_marking_post_spec t post m' places finalm ->
      update_marking_post_spec t post m (p :: places) finalm.

  (*** Correctness proof : update_marking_post ***)
  Theorem update_marking_post_correct :
    forall (t : trans_type)
           (post : weight_type)
           (places : list place_type)
           (m finalm : marking_type),
    update_marking_post t post m places = finalm ->
    update_marking_post_spec t post m places finalm.
  Proof.
    intros t post places m finalm;
    functional induction (update_marking_post t post m places)
               using update_marking_post_ind;
    intros.
    (* Case places is nil *)
    - rewrite <- H; apply update_marking_post_nil.
    (* General case *)
    - apply update_marking_post_cons with (m' := (modify_m m p Nat.add (post t p))).
      + apply modify_m_correct; auto.
      + apply (IHm0 H); auto.
  Qed.

  (*** Completeness proof : update_marking_post ***)
  Theorem update_marking_post_compl :
    forall (t : trans_type)
           (post : weight_type)
           (places : list place_type)
           (m finalm : marking_type),
    update_marking_post_spec t post m places finalm ->
    update_marking_post t post m places = finalm.
  Proof.
    intros t post places m finalm H; elim H; intros.
    (* Case update_marking_post_nil *)
    - simpl; auto.
    (* Case update_marking_post_cons *)
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
           (places : list place_type) : bool :=
    match places with
    | (pl i) :: tail => match pre_or_test_arcs_t (pl i) with
                        (* If there is no pre or test edge between (pl i) and t. *)
                        | None => check_pre_or_test pre_or_test_arcs_t m tail
                        (* Else some pre or test edge exists. *)
                        | Some (mk_nat_star edge_weight _) =>
                          let nboftokens := (get_m m i) in
                          match nboftokens with
                          | None => (edge_weight <=? 0)
                                    && (check_pre_or_test pre_or_test_arcs_t m tail)
                          | Some n => (edge_weight <=? n)
                                      && (check_pre_or_test pre_or_test_arcs_t m tail)
                          end
                        end
    | [] => true
    end.

  Functional Scheme check_pre_or_test_ind := Induction for check_pre_or_test Sort Prop. 
  
  (*** Formal specification : check_pre_or_test ***)
  Inductive check_pre_or_test_spec
            (pre_or_test_arcs_t : place_type -> option nat_star)
            (m : marking_type) :
    list place_type -> Prop :=
  | check_pre_or_test_nil :
      check_pre_or_test_spec pre_or_test_arcs_t m []
  | check_pre_or_test_edge_none :
      forall (places : list place_type)
             (i : nat),
      pre_or_test_arcs_t (pl i) = None ->
      check_pre_or_test_spec pre_or_test_arcs_t m places ->
      check_pre_or_test_spec pre_or_test_arcs_t m ((pl i) :: places)
  | check_pre_or_test_tokens_none :
      forall (places : list place_type) 
             (i edge_weight : nat)
             (is_positive : edge_weight > 0),
        pre_or_test_arcs_t (pl i) = Some (mk_nat_star edge_weight is_positive) ->
        get_m_spec m i None ->
        edge_weight <= 0 ->
        check_pre_or_test_spec pre_or_test_arcs_t m places ->
        check_pre_or_test_spec pre_or_test_arcs_t m ((pl i) :: places)
  | check_pre_or_test_tokens_some :
      forall (places : list place_type) 
             (i n edge_weight : nat)
             (is_positive : edge_weight > 0),
      pre_or_test_arcs_t (pl i) = Some (mk_nat_star edge_weight is_positive) ->
      get_m_spec m i (Some n) ->
      edge_weight <= n ->
      check_pre_or_test_spec pre_or_test_arcs_t m places ->
      check_pre_or_test_spec pre_or_test_arcs_t m ((pl i) :: places).

  (*** Correctness proof : check_pre_or_test ***)
  Theorem check_pre_or_test_correct :
    forall (pre_or_test_arcs_t : place_type -> option nat_star)
           (m : marking_type)
           (places : list place_type),
    check_pre_or_test pre_or_test_arcs_t m places = true ->
    check_pre_or_test_spec pre_or_test_arcs_t m places.
  Proof.
    intros pre_or_test_arcs_t m places;
    functional induction (check_pre_or_test pre_or_test_arcs_t m places)
               using check_pre_or_test_ind;
    intros.
    (* Case places = [] *)
    - apply check_pre_or_test_nil.
    (* Case edge and tokens exist *)
    - apply check_pre_or_test_tokens_some with (i := i)
                                               (n := n0)
                                               (edge_weight := edge_weight)
                                               (is_positive := _x).
      + rewrite e1; auto.
      + apply get_m_correct; auto.
      + apply andb_prop in H; elim H; intros; apply leb_complete in H0; auto.
      + apply IHb; apply andb_prop in H; elim H; intros; auto.
    (* Case edge exists but no tokens *)
    - apply check_pre_or_test_tokens_none with (i := i)
                                               (edge_weight := edge_weight)
                                               (is_positive := _x).
      + rewrite e1; auto.
      + apply get_m_correct; auto.
      + apply andb_prop in H; elim H; intros; apply leb_complete in H0; auto.
      + apply IHb; apply andb_prop in H; elim H; intros; auto.
    (* Case edge doesn't exist *)
    - apply check_pre_or_test_edge_none.
      + auto.
      + apply IHb; auto.
  Qed.


  (*** Completeness proof : check_pre_or_test ***)
  Theorem check_pre_or_test_compl :
   forall (pre_or_test_arcs_t : place_type -> option nat_star)
          (m : marking_type)
          (places : list place_type),
   check_pre_or_test_spec pre_or_test_arcs_t m places ->
   check_pre_or_test pre_or_test_arcs_t m places = true.
  Proof.
    intros pre_or_test_arcs_t m places H; induction H.
    (* Case check_pre_or_test_nil *)
    - simpl; auto.
    (* Case check_pre_or_test_edge_none *)
    - simpl; rewrite H; auto.
    (* Case check_pre_or_test_tokens_none *)
    - simpl; rewrite H; apply get_m_compl in H0; rewrite H0; apply andb_true_intro.
      split; [apply leb_correct in H1; rewrite H1; auto | auto].
    (* Case check_pre_or_test_tokens_some *)
    - simpl; rewrite H; apply get_m_compl in H0; rewrite H0; apply andb_true_intro.
      split; [apply leb_correct in H1; rewrite H1; auto | auto].
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
           (places : list place_type) : bool :=
    match places with
    | (pl i) :: tail => match inhib_arcs_t (pl i) with
                        (* If there is inhib edge between (pl i) and t. *)
                        | None => (check_inhib inhib_arcs_t m tail)
                        (* Else some inhib edge exists. *)
                        | Some (mk_nat_star edge_weight _) =>
                          let nboftokens := (get_m m i) in
                          match nboftokens with
                          | None => (check_inhib inhib_arcs_t m tail)
                          | Some n => (n <? edge_weight)
                                      && (check_inhib inhib_arcs_t m tail)
                          end
                          
                        end
    | [] => true
    end.

  Functional Scheme check_inhib_ind := Induction for check_inhib Sort Prop.

  (*** Formal specification ***)
  Inductive check_inhib_spec
            (inhib_arcs_t : place_type -> option nat_star)
            (m : marking_type) :
    list place_type -> Prop :=
  | check_inhib_nil :
      check_inhib_spec inhib_arcs_t m []
  | check_inhib_edge_none :
      forall (places : list place_type)
             (i : nat),
      inhib_arcs_t (pl i) = None ->
      check_inhib_spec inhib_arcs_t m places ->
      check_inhib_spec inhib_arcs_t m ((pl i) :: places)
  | check_inhib_tokens_none :
      forall (places : list place_type) 
             (i edge_weight : nat)
             (is_positive : edge_weight > 0),
        inhib_arcs_t (pl i) = Some (mk_nat_star edge_weight is_positive) ->
        get_m_spec m i None ->
        check_inhib_spec inhib_arcs_t m places ->
        check_inhib_spec inhib_arcs_t m ((pl i) :: places)
  | check_inhib_tokens_some :
      forall (places : list place_type) 
             (i n edge_weight : nat)
             (is_positive : edge_weight > 0),
      inhib_arcs_t (pl i) = Some (mk_nat_star edge_weight is_positive) ->
      get_m_spec m i (Some n) ->
      n < edge_weight ->
      check_inhib_spec inhib_arcs_t m places ->
      check_inhib_spec inhib_arcs_t m ((pl i) :: places).

  (*** Correctness proof : check_inhib ***)
   Theorem check_inhib_correct :
    forall (inhib_arcs_t : place_type -> option nat_star)
           (m : marking_type)
           (places : list place_type),
    check_inhib inhib_arcs_t m places = true ->
    check_inhib_spec inhib_arcs_t m places.
  Proof.
    intros inhib_arcs_t m places;
    functional induction (check_inhib inhib_arcs_t m places)
               using check_inhib_ind;
    intros.
    (* Case places = [] *)
    - apply check_inhib_nil.
    (* Case edge and tokens exist *)
    - apply check_inhib_tokens_some with (i := i)
                                               (n := n0)
                                               (edge_weight := edge_weight)
                                               (is_positive := _x).
      + rewrite e1; auto.
      + apply get_m_correct; auto.
      + apply andb_prop in H; elim H; intros; apply leb_complete in H0; auto.
      + apply IHb; apply andb_prop in H; elim H; intros; auto.
    (* Case edge exists but no tokens *)
    - apply check_inhib_tokens_none with (i := i)
                                               (edge_weight := edge_weight)
                                               (is_positive := _x).
      + rewrite e1; auto.
      + apply get_m_correct; auto.
      + apply IHb; auto.
    (* Case edge doesn't exist *)
    - apply check_inhib_edge_none.
      + auto.
      + apply IHb; auto.
  Qed.

  (*** Completeness proof : check_inhib ***)
  Theorem check_inhib_compl :
   forall (inhib_arcs_t : place_type -> option nat_star)
          (m : marking_type)
          (places : list place_type),
   check_inhib_spec inhib_arcs_t m places ->
   check_inhib inhib_arcs_t m places = true.
  Proof.
    intros inhib_arcs_t m places H; induction H.
    (* Case check_inhib_nil *)
    - simpl; auto.
    (* Case check_inhib_edge_none *)
    - simpl; rewrite H; auto.
    (* Case check_inhib_tokens_none *)
    - simpl; rewrite H; apply get_m_compl in H0; rewrite H0; auto.
    (* Case check_inhib_tokens_some *)
    - simpl; rewrite H; apply get_m_compl in H0; rewrite H0; apply andb_true_intro.
      split; [apply <- Nat.ltb_lt in H1; rewrite H1; auto | auto].
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
             (steadym decreasingm : marking_type) : bool :=
    (check_pre_or_test pre_arcs_t decreasingm (pre_pl neighbours_t))
    && (check_pre_or_test test_arcs_t steadym (test_pl neighbours_t))
    && (check_inhib inhib_arcs_t steadym (inhib_pl neighbours_t)).

  Functional Scheme check_all_edges_ind := Induction for check_all_edges Sort Prop.

  (*** Formal specification : check_all_edges ***)
  Inductive check_all_edges_spec
            (neighbours_t : neighbours_type)
            (pre_arcs_t : place_type -> option nat_star)
            (test_arcs_t : place_type -> option nat_star)
            (inhib_arcs_t : place_type -> option nat_star)
            (steadym decreasingm : marking_type) : Prop :=
  | check_all_edges_cons :
      (check_pre_or_test_spec pre_arcs_t decreasingm (pre_pl neighbours_t) /\
       check_pre_or_test_spec test_arcs_t steadym (test_pl neighbours_t) /\
       check_inhib_spec inhib_arcs_t steadym (inhib_pl neighbours_t)) ->
      check_all_edges_spec neighbours_t pre_arcs_t test_arcs_t inhib_arcs_t steadym decreasingm.

  (*** Correctness proof : check_all_edges *)
  Theorem check_all_edges_correct :
    forall (neighbours_t : neighbours_type)
           (pre_arcs_t : place_type -> option nat_star)
           (test_arcs_t : place_type -> option nat_star)
           (inhib_arcs_t : place_type -> option nat_star)
           (steadym decreasingm : marking_type),
    check_all_edges neighbours_t pre_arcs_t test_arcs_t inhib_arcs_t steadym decreasingm = true ->
    check_all_edges_spec neighbours_t pre_arcs_t test_arcs_t inhib_arcs_t steadym decreasingm.
  Proof.
    intros.
    unfold check_all_edges in H. do 2 (apply andb_prop in H; elim H; clear H; intros).
    apply check_all_edges_cons.
    repeat
      split; (apply check_pre_or_test_correct in H; auto ||
              apply check_pre_or_test_correct in H1; auto ||
              apply check_inhib_correct in H0; auto).
  Qed.

  (*** Completeness proof : check_all_edges ***)
  Theorem check_all_edges_compl :
    forall (neighbours_t : neighbours_type)
           (pre_arcs_t : place_type -> option nat_star)
           (test_arcs_t : place_type -> option nat_star)
           (inhib_arcs_t : place_type -> option nat_star)
           (steadym decreasingm : marking_type),
    check_all_edges_spec neighbours_t pre_arcs_t test_arcs_t inhib_arcs_t steadym decreasingm ->
    check_all_edges neighbours_t pre_arcs_t test_arcs_t inhib_arcs_t steadym decreasingm = true.
  Proof.
    intros. induction H.
    unfold check_all_edges.
    elim H; intros; elim H1; intros; clear H H1.
    repeat (apply andb_true_intro; intros; split); 
    repeat (apply check_pre_or_test_compl in H0; auto ||
            apply check_pre_or_test_compl in H2; auto ||
            apply check_inhib_compl in H3; auto).    
  Qed.
  
  Theorem prop_bool_true_false :
    forall (b :bool) (P : Prop), ((b = true) <-> P) -> ((b = false) <-> ~P).
  Proof.
  Admitted.
  
  Theorem check_all_edges_false :
    forall (neighbours_t : neighbours_type)
           (pre_arcs_t : place_type -> option nat_star)
           (test_arcs_t : place_type -> option nat_star)
           (inhib_arcs_t : place_type -> option nat_star)
           (steadym decreasingm : marking_type),
    ~check_all_edges_spec neighbours_t pre_arcs_t test_arcs_t inhib_arcs_t steadym decreasingm ->
    check_all_edges neighbours_t pre_arcs_t test_arcs_t inhib_arcs_t steadym decreasingm = false.
  Proof.
    intros neighbours_t pre_arcs_t test_arcs_t inhib_arcs_t steadym decreasingm.
    apply prop_bool_true_false.
    split.
    - intro; apply check_all_edges_correct; auto.
    - intro; apply check_all_edges_compl; auto.
  Qed.
  
End Edges.

(*==============================================================*)
(*================= FIRING ALGORITHM for SPN ===================*)
(*==============================================================*)

Section FireSpn.

  (* 
   * There are 2 parallel calculus in spn_fire_pre_aux : 
   * 1. pumping tokens to get "decreasingm" (fired pre)
   * 2. returning group of transitions (fired_pre_group)
   *
   * and 2 markings are recorded : 
   * 1. the initial one to check with inhib and test arcs
   * 2. a floating (decreasing) intermediate marking to check classic arcs
   *)
  
  (* Function : Given 1 conflict-free group of transitions (a list cfgroup), 
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
           (fired_pre_group cfgroup : list trans_type) :
    (list trans_type) * marking_type :=
    match cfgroup with
    | (tr i) :: tail =>
      match get_neighbours lneighbours i with
      (* If transition t have no neighbours, then continues. *)
      | None => (spn_fire_pre_aux lneighbours pre test inhib steadym decreasingm fired_pre_group tail)
      (* Else checks neighbours of t. *)
      | Some neighbours_t =>
        (* If t is sensitized. *)
        if (check_all_edges neighbours_t (pre (tr i)) (test (tr i)) (inhib (tr i)) steadym decreasingm) then
          (* Updates the marking for the pre places, neighbours of t. *)
          let new_decreasing := (update_marking_pre (tr i) pre decreasingm (pre_pl neighbours_t)) in
          (spn_fire_pre_aux lneighbours pre test inhib steadym new_decreasing (fired_pre_group ++ [(tr i)]) tail)
        (* Else no changes but inductive progress. *)
        else (spn_fire_pre_aux lneighbours pre test inhib steadym decreasingm fired_pre_group tail)
      end
    | []  => (fired_pre_group, decreasingm)
    end.

  Functional Scheme spn_fire_pre_aux_ind := Induction for spn_fire_pre_aux Sort Prop. 
  
  (*** Formal specification : spn_fire_pre_aux ***)
  Inductive spn_fire_pre_aux_spec
            (lneighbours : list neighbours_type)
            (pre test inhib : weight_type) 
            (steadym : marking_type) 
            (decreasingm : marking_type)
            (fired_pre_group : list trans_type) :
    list trans_type -> (list trans_type * marking_type) -> Prop :=
  | spn_fire_pre_aux_nil :
      spn_fire_pre_aux_spec lneighbours pre test inhib steadym decreasingm fired_pre_group []
                                  (fired_pre_group, decreasingm)
  | spn_fire_pre_aux_neighbours_none :
      forall (i : nat) (cfgroup : list trans_type) (finalfired : list trans_type) (finalm : marking_type),
      get_neighbours_spec lneighbours i None ->
      spn_fire_pre_aux_spec lneighbours pre test inhib steadym decreasingm fired_pre_group cfgroup
                                  (finalfired, finalm) ->
      spn_fire_pre_aux_spec lneighbours pre test inhib steadym decreasingm fired_pre_group ((tr i) :: cfgroup)
                                  (finalfired, finalm)
  | spn_fire_pre_aux_if :
      forall (i : nat)
             (neighbours_t : neighbours_type)
             (cfgroup : list trans_type)
             (finalfired : list trans_type)
             (modifiedm finalm : marking_type),
      get_neighbours_spec lneighbours i (Some neighbours_t) ->
      check_all_edges_spec neighbours_t (pre (tr i)) (test (tr i)) (inhib (tr i)) steadym decreasingm ->
      update_marking_pre_spec (tr i) pre decreasingm (pre_pl neighbours_t) modifiedm ->
      spn_fire_pre_aux_spec lneighbours pre test inhib steadym modifiedm (fired_pre_group ++ [(tr i)]) cfgroup
                                  (finalfired, finalm) ->
      spn_fire_pre_aux_spec lneighbours pre test inhib steadym decreasingm fired_pre_group ((tr i) :: cfgroup)
                                  (finalfired, finalm)
  | spn_fire_pre_aux_else :
      forall (i : nat)
             (neighbours_t : neighbours_type)
             (cfgroup : list trans_type)
             (finalfired : list trans_type)
             (finalm : marking_type),
      get_neighbours_spec lneighbours i (Some neighbours_t) ->
      ~check_all_edges_spec neighbours_t (pre (tr i)) (test (tr i)) (inhib (tr i)) steadym decreasingm ->
      spn_fire_pre_aux_spec lneighbours pre test inhib steadym decreasingm fired_pre_group cfgroup
                                  (finalfired, finalm) ->
      spn_fire_pre_aux_spec lneighbours pre test inhib steadym decreasingm fired_pre_group ((tr i) :: cfgroup)
                                  (finalfired, finalm).
  
  (*** Correctness proof : spn_fire_pre_aux ***)
  Theorem spn_fire_pre_aux_correct :
  forall (lneighbours : list neighbours_type)
         (pre test inhib : weight_type) 
         (steadym : marking_type) 
         (finalm decreasingm : marking_type)
         (finalfired fired_pre_group : list trans_type)
         (cfgroup : list trans_type),
  spn_fire_pre_aux lneighbours pre test inhib steadym decreasingm fired_pre_group cfgroup = (finalfired, finalm) ->
  spn_fire_pre_aux_spec lneighbours pre test inhib steadym decreasingm fired_pre_group cfgroup (finalfired, finalm).
  Proof.
    intros lneighbours pre test inhib steadym finalm decreasingm finalfired fired_pre_group cfgroup.
    functional induction (spn_fire_pre_aux lneighbours pre test inhib steadym decreasingm fired_pre_group cfgroup)
               using spn_fire_pre_aux_ind; intros.
    (* Case cfgroup = [] *)
    - rewrite <- H; apply spn_fire_pre_aux_nil.
    (* Case t is sensitized, check_all_edges = true *)
    - apply spn_fire_pre_aux_if with (modifiedm := (update_marking_pre (tr i) pre decreasingm (pre_pl neighbours_t)))
                                           (neighbours_t := neighbours_t).
      + apply get_neighbours_correct; auto.
      + apply check_all_edges_correct; auto.
      + apply update_marking_pre_correct; auto.
      + apply IHp; auto.
    (* Case t is disabled, check_all_edges = false *)
    - apply spn_fire_pre_aux_else with (neighbours_t := neighbours_t).
      + apply get_neighbours_correct; auto.
      + intro; apply check_all_edges_compl in H0; rewrite H0 in e2; apply diff_true_false in e2; elim e2.
      + apply IHp; auto.
    (* Case no neighbours for t *)
    - apply spn_fire_pre_aux_neighbours_none.
      + apply get_neighbours_correct; auto.
      + apply IHp; auto.
  Qed.

  (*** Completeness proof : spn_fire_pre_aux ***)
  Theorem spn_fire_pre_aux_compl :
    forall (lneighbours : list neighbours_type)
           (pre test inhib : weight_type) 
           (steadym : marking_type) 
           (finalm decreasingm : marking_type)
           (finalfired fired_pre_group : list trans_type)
           (cfgroup : list trans_type),
    spn_fire_pre_aux_spec lneighbours pre test inhib steadym decreasingm fired_pre_group cfgroup (finalfired, finalm) ->
    spn_fire_pre_aux lneighbours pre test inhib steadym decreasingm fired_pre_group cfgroup = (finalfired, finalm).
  Proof.
    intros lneighbours pre test inhib steadym finalm decreasingm finalfired fired_pre_group cfgroup Hspec.
    induction Hspec.
    (* Case spn_fire_pre_aux_nil *)
    - simpl; auto.
    (* Case spn_fire_pre_aux_neighbours_none *)
    - simpl; apply get_neighbours_compl in H; rewrite H; rewrite IHHspec; auto.
    (* Case spn_fire_pre_aux_if *)
    - simpl.
      apply get_neighbours_compl in H; rewrite H.
      apply check_all_edges_compl in H0; rewrite H0.
      apply update_marking_pre_compl in H1; rewrite H1; auto.
    (* Case spn_fire_pre_aux_else *)
    - simpl.
      apply get_neighbours_compl in H; rewrite H.
      apply check_all_edges_false in H0. rewrite H0. rewrite IHHspec; auto.
  Qed.
  
  (*  
   * Function : Wrapper function around spn_fire_pre_aux.
   *)
  Definition spn_fire_pre
             (lneighbours : list neighbours_type)
             (pre test inhib : weight_type) 
             (steadym : marking_type) 
             (decreasingm : marking_type)
             (cfgroup : list trans_type) : (list trans_type) * marking_type :=
    spn_fire_pre_aux lneighbours pre test inhib steadym decreasingm [] cfgroup.

  Functional Scheme spn_fire_pre_ind := Induction for spn_fire_pre Sort Prop.

  (*** Formal specification : spn_fire_pre ***)
  Inductive spn_fire_pre_spec
            (lneighbours : list neighbours_type)
            (pre test inhib : weight_type) 
            (steadym : marking_type) 
            (decreasingm : marking_type)
            (cfgroup : list trans_type) : (list trans_type) * marking_type -> Prop :=
  | spn_fire_pre_cons :
      forall (finalfired : list trans_type) (finalm : marking_type),
      spn_fire_pre_aux_spec lneighbours pre test inhib steadym decreasingm [] cfgroup
                                  (finalfired, finalm) ->
      spn_fire_pre_spec lneighbours pre test inhib steadym decreasingm cfgroup
                              (finalfired, finalm).

  (*** Correctness proof : spn_fire_pre ***)
  Theorem spn_fire_pre_correct :
    forall (lneighbours : list neighbours_type)
           (pre test inhib : weight_type) 
           (steadym decreasingm finalm : marking_type) 
           (finalfired cfgroup : list trans_type),
      spn_fire_pre lneighbours pre test inhib steadym decreasingm cfgroup = (finalfired, finalm) ->
      spn_fire_pre_spec lneighbours pre test inhib steadym decreasingm cfgroup (finalfired, finalm).
  Proof.
    intros lneighbours pre test inhib steadym decreasingm finalm finalfired cfgroup;
    functional induction (spn_fire_pre lneighbours pre test inhib steadym decreasingm cfgroup)
               using spn_fire_pre_ind; intros.
    apply spn_fire_pre_cons; apply spn_fire_pre_aux_correct in H; auto.
  Qed.

  (*** Completeness proof : spn_fire_pre ***)
  Theorem spn_fire_pre_compl :
    forall (lneighbours : list neighbours_type)
           (pre test inhib : weight_type) 
           (steadym decreasingm finalm : marking_type) 
           (finalfired cfgroup : list trans_type),
    spn_fire_pre_spec lneighbours pre test inhib steadym decreasingm cfgroup (finalfired, finalm) ->
    spn_fire_pre lneighbours pre test inhib steadym decreasingm cfgroup = (finalfired, finalm).
  Proof.
    intros lneighbours pre test inhib steadym decreasingm finalm finalfired cfgroup Hspec; elim Hspec; intros.
    unfold spn_fire_pre; apply spn_fire_pre_aux_compl in H; auto. 
  Qed.
  
  (*
   * Function : Apply spn_fire_pre over ALL cfgroups of transitions. 
   *            Begin with initial marking; End with half fired marking.  
   *            "fired_pre_groups" is empty at first 
   *)
  Fixpoint spn_map_fire_pre_aux
           (lneighbours : list neighbours_type)
           (pre test inhib : weight_type)
           (steadym decreasingm : marking_type)
           (fired_pre_groups cfgroups : list (list trans_type)) :
    (list (list trans_type)) * marking_type :=
    match cfgroups with
    (* Loops over all cfgroups of transitions (priority group) and
     * calls spn_fire_pre. *)
    | cfgroup :: cfgroups_tail =>
      let (fired_pre_group, m_decreased) :=
          (spn_fire_pre lneighbours pre test inhib steadym decreasingm cfgroup) in
      spn_map_fire_pre_aux lneighbours pre test inhib steadym m_decreased
                           (fired_pre_group :: fired_pre_groups) cfgroups_tail
    | [] => (fired_pre_groups, decreasingm)
    end.

  Functional Scheme spn_map_fire_pre_aux_ind := Induction for spn_map_fire_pre_aux Sort Prop.
  
  (*** Formal specification : spn_map_fire_pre_aux ***)
  Inductive spn_map_fire_pre_aux_spec
            (lneighbours : list neighbours_type)
            (pre test inhib : weight_type)
            (steadym decreasingm : marking_type)
            (fired_pre_groups : list (list trans_type)) :
    list (list trans_type) -> (list (list trans_type)) * marking_type -> Prop :=
  | spn_map_fire_pre_aux_nil :
      spn_map_fire_pre_aux_spec lneighbours pre test inhib steadym decreasingm fired_pre_groups []
                            (fired_pre_groups, decreasingm)
  | spn_map_fire_pre_aux_cons :
      forall (cfgroup finalfired : list trans_type)
             (modifiedm finalm : marking_type)
             (cfgroups final_groups : list (list trans_type)),
        spn_fire_pre_spec lneighbours pre test inhib steadym decreasingm cfgroup (finalfired, modifiedm) ->
        spn_map_fire_pre_aux_spec lneighbours pre test inhib steadym modifiedm (finalfired :: fired_pre_groups) cfgroups
                              (final_groups, finalm) ->
        spn_map_fire_pre_aux_spec lneighbours pre test inhib steadym decreasingm fired_pre_groups (cfgroup :: cfgroups)
                              (final_groups, finalm).

  (*** Correctness proof : spn_map_fire_pre_aux ***)
  Theorem spn_map_fire_pre_aux_correct :
    forall (lneighbours : list neighbours_type)
           (pre test inhib : weight_type)
           (steadym decreasingm finalm : marking_type)
           (fired_pre_groups cfgroups final_groups : list (list trans_type)),
   spn_map_fire_pre_aux lneighbours pre test inhib steadym decreasingm fired_pre_groups cfgroups =
   (final_groups, finalm) ->
   spn_map_fire_pre_aux_spec lneighbours pre test inhib steadym decreasingm fired_pre_groups cfgroups
                         (final_groups, finalm).
  Proof.
    intros lneighbours pre test inhib steadym decreasingm finalm fired_pre_groups cfgroups final_groups;
    functional induction (spn_map_fire_pre_aux lneighbours pre test inhib steadym decreasingm fired_pre_groups cfgroups)
               using spn_map_fire_pre_aux_ind; intros.
    (* Case cfgroups = [] *)
    - rewrite <- H; apply spn_map_fire_pre_aux_nil.
    (* General case *)
    - apply spn_map_fire_pre_aux_cons with (finalfired := fired_pre_group) (modifiedm := m_decreased).
      + apply spn_fire_pre_correct; auto.
      + apply IHp; rewrite H; auto.
  Qed.

  (*** Completeness proof : spn_map_fire_pre_aux ***)
  Theorem spn_map_fire_pre_aux_compl :
    forall (lneighbours : list neighbours_type)
           (pre test inhib : weight_type)
           (steadym decreasingm finalm : marking_type)
           (fired_pre_groups cfgroups final_groups : list (list trans_type)),
    spn_map_fire_pre_aux_spec lneighbours pre test inhib steadym decreasingm fired_pre_groups cfgroups (final_groups, finalm) ->
    spn_map_fire_pre_aux lneighbours pre test inhib steadym decreasingm fired_pre_groups cfgroups = (final_groups, finalm).
  Proof.
    intros lneighbours pre test inhib steadym decreasingm finalm fired_pre_groups cfgroups final_groups Hspec; elim Hspec; intros.
    (* Case spn_map_fire_pre_aux_nil *)
    - simpl; auto.
    (* Case spn_map_fire_pre_aux_cons *)
    - simpl; apply spn_fire_pre_compl in H; rewrite H; rewrite H1; auto.
  Qed.
  
  (*
   * Function : Update the marking by consuming
   *            the tokens in pre-condition places.            
   *)
  Definition spn_map_fire_pre
             (lneighbours : list neighbours_type)
             (pre test inhib : weight_type)
             (steadym : marking_type)
             (cfgroups : list (list trans_type)) :
    (list (list trans_type)) * marking_type :=
    spn_map_fire_pre_aux lneighbours pre test inhib steadym steadym [] cfgroups.

  (*** Formal specification : spn_map_fire_pre ***)
  Inductive spn_map_fire_pre_spec
            (lneighbours : list neighbours_type)
            (pre test inhib : weight_type)
            (steadym : marking_type)
            (cfgroups : list (list trans_type)) :
    (list (list trans_type)) * marking_type -> Prop :=
  | spn_map_fire_pre_cons :
      forall (final_groups : (list (list trans_type))) (finalm : marking_type),
      spn_map_fire_pre_aux_spec lneighbours pre test inhib steadym steadym [] cfgroups
                                (final_groups, finalm) ->
      spn_map_fire_pre_spec lneighbours pre test inhib steadym cfgroups (final_groups, finalm).

  (*** Correctness proof : spn_map_fire_pre ***)
  Theorem spn_map_fire_pre_correct :
    forall (lneighbours : list neighbours_type)
           (pre test inhib : weight_type)
           (steadym finalm : marking_type)
           (cfgroups final_groups : list (list trans_type)),
    spn_map_fire_pre lneighbours pre test inhib steadym cfgroups = (final_groups, finalm) ->
    spn_map_fire_pre_spec lneighbours pre test inhib steadym cfgroups
                      (final_groups, finalm).  
  Proof.
    intros lneighbours pre test inhib steadym finalm cfgroups final_groups H.
    apply spn_map_fire_pre_cons.
    unfold spn_map_fire_pre in H.
    apply spn_map_fire_pre_aux_correct.
    auto.
  Qed.

  (*** Completeness proof : spn_map_fire_pre ***)
  Theorem spn_map_fire_pre_compl :
    forall (lneighbours : list neighbours_type)
           (pre test inhib : weight_type)
           (steadym finalm : marking_type)
           (cfgroups final_groups : list (list trans_type)),
    spn_map_fire_pre_spec lneighbours pre test inhib steadym cfgroups (final_groups, finalm) ->
    spn_map_fire_pre lneighbours pre test inhib steadym cfgroups = (final_groups, finalm).
  Proof.
    intros lneighbours pre test inhib steadym finalm cfgroups final_groups H.
    unfold spn_map_fire_pre.
    elim H; intros.
    apply spn_map_fire_pre_aux_compl.
    auto.
  Qed.
  
  (* 
   * Function : Given a marking "m_intermediate", resulting of the call
   *            of the function spn_map_fire_pre, and after
   *            that a given group of transs has been pre-fired
   *            (the "fired_pre_group" list of transitions),
   *            returns the marking increased by the post-condition edges.
   *)
  Fixpoint fire_post
           (lneighbours : list neighbours_type)
           (post : weight_type)
           (increasingm : marking_type)
           (fired_pre_group : list trans_type) : marking_type :=
    match fired_pre_group with
    | []  => increasingm
    | (tr i) :: tail  =>
      match get_neighbours lneighbours i with
      (* If transition (tr i) has no neighbours, then continues. *)
      | None => (fire_post lneighbours post increasingm tail)
      (* Else updates the marking
       * for all neighbour post places of (tr i). *)
      | Some neighbours_t =>
        (fire_post lneighbours
                         post
                         (update_marking_post (tr i) post increasingm (post_pl neighbours_t))
                         tail)
      end
    end.

  (*** Formal specification : fire_post ***)
  Inductive fire_post_spec
            (lneighbours : list neighbours_type)
            (post : weight_type) 
            (increasingm : marking_type) :
    list trans_type -> marking_type -> Prop :=
  | fire_post_nil :
      fire_post_spec lneighbours post increasingm [] increasingm
  | fire_post_none :
      forall (i : nat) (fired_pre_group : list trans_type) (finalm : marking_type),
      get_neighbours_spec lneighbours i None ->
      fire_post_spec lneighbours post increasingm fired_pre_group finalm ->
      fire_post_spec lneighbours post increasingm ((tr i) :: fired_pre_group) finalm
  | fire_post_some :
      forall (i : nat)
             (neighbours_t : neighbours_type)
             (fired_pre_group : list trans_type)
             (modifiedm finalm : marking_type),
      get_neighbours_spec lneighbours i (Some neighbours_t) ->
      update_marking_post_spec (tr i) post increasingm (post_pl neighbours_t) modifiedm ->
      fire_post_spec lneighbours post modifiedm fired_pre_group finalm ->
      fire_post_spec lneighbours post increasingm ((tr i) :: fired_pre_group) finalm.

  Functional Scheme fire_post_ind := Induction for fire_post Sort Prop.
  
  (*** Correctness proof : fire_post ***)
  Theorem fire_post_correct :
    forall (lneighbours : list neighbours_type)
           (post : weight_type) 
           (increasingm finalm : marking_type) 
           (fired_pre_group : list trans_type),
    fire_post lneighbours post increasingm fired_pre_group = finalm ->
    fire_post_spec lneighbours post increasingm fired_pre_group finalm.
  Proof.
    intros lneighbours post increasingm finalm fired_pre_group;
    functional induction (fire_post lneighbours post increasingm fired_pre_group)
               using fire_post_ind;
    intros.
    (* Case fired_pre_group = [] *)
    - rewrite <- H; apply fire_post_nil; auto.
    (* Case (tr i) has neighbours *)
    - apply fire_post_some with (neighbours_t := neighbours_t)
                                      (modifiedm := (update_marking_post (tr i) post increasingm (post_pl neighbours_t))).
      + apply get_neighbours_correct; auto.
      + apply update_marking_post_correct; auto.
      + apply IHm; rewrite <- H; auto.
    (* Case (tr i) has no neighbours *)
    - apply fire_post_none.
      + apply get_neighbours_correct; auto.
      + apply IHm; rewrite <- H; auto.
  Qed.

  (*** Completeness proof : fire_post ***)
  Theorem fire_post_compl :
    forall (lneighbours : list neighbours_type)
           (post : weight_type) 
           (increasingm finalm : marking_type) 
           (fired_pre_group : list trans_type),
    fire_post_spec lneighbours post increasingm fired_pre_group finalm ->
    fire_post lneighbours post increasingm fired_pre_group = finalm. 
  Proof.
    intros lneighbours post increasingm finalm fired_pre_group H;
    elim H;
    intros.
    (* Case fire_post_nil *)
    - simpl; auto.
    (* Case fire_post_none *)
    - simpl; apply get_neighbours_compl in H0; rewrite H0; auto.
    (*  *)
    - simpl; apply get_neighbours_compl in H0; rewrite H0; simpl.
      apply update_marking_post_compl in H1; rewrite H1; auto.
  Qed.
  
  (*  
   * Function : Meant to begin with intermediate marking
   *            computed by "fire_pre", after half (pre arcs)
   *            firing of ALL the chosen transitions.
   *            Ends with the FINAL marking of the cycle !
   *)
  Fixpoint map_fire_post
           (lneighbours : list neighbours_type)
           (post : weight_type)
           (increasingm : marking_type)
           (fired_pre_groups : list (list trans_type)) : marking_type :=
    match fired_pre_groups with
    | []  => increasingm
    | fired_pre_group :: tail  =>
      let greater_m := (fire_post lneighbours post increasingm fired_pre_group) in
      (map_fire_post lneighbours post greater_m tail)
    end.

  (*** Formal specification : map_fire_post ***)
  Inductive map_fire_post_spec
            (lneighbours : list neighbours_type)
            (post : weight_type)
            (increasingm : marking_type) :
    list (list trans_type) -> marking_type -> Prop :=
  | map_fire_post_nil :
      map_fire_post_spec lneighbours post increasingm [] increasingm
  | map_fire_post_cons :
      forall (fired_pre_group : list trans_type)
             (fired_pre_groups : list (list trans_type))
             (modifiedm finalm : marking_type),
      fire_post_spec lneighbours post increasingm fired_pre_group modifiedm ->
      map_fire_post_spec lneighbours post modifiedm fired_pre_groups finalm ->  
      map_fire_post_spec lneighbours post increasingm (fired_pre_group :: fired_pre_groups) finalm.

  Functional Scheme map_fire_post_ind := Induction for map_fire_post Sort Prop.
  
  (*** Correctness proof : map_fire_post ***)
  Theorem map_fire_post_correct :
    forall (lneighbours : list neighbours_type)
           (post : weight_type)
           (increasingm finalm : marking_type)
           (fired_pre_groups : list (list trans_type)),
    map_fire_post lneighbours post increasingm fired_pre_groups = finalm ->
    map_fire_post_spec lneighbours post increasingm fired_pre_groups finalm.
  Proof.
    intros lneighbours post increasingm finalm fired_pre_groups;
    functional induction (map_fire_post lneighbours post increasingm fired_pre_groups)
               using map_fire_post_ind;
    intros.
    (* Case fired_pre_groups = [] *)
    - rewrite <- H; apply map_fire_post_nil.
    (* General case *)
    - apply map_fire_post_cons with (modifiedm := (fire_post lneighbours post increasingm fired_pre_group)).
      + apply fire_post_correct; auto.
      + apply IHm; rewrite H; auto.
  Qed.  

  (*** Completeness proof : map_fire_post ***)
  Theorem map_fire_post_compl :
    forall (lneighbours : list neighbours_type)
           (post : weight_type)
           (increasingm finalm : marking_type)
           (fired_pre_groups : list (list trans_type)),
    map_fire_post_spec lneighbours post increasingm fired_pre_groups finalm ->
    map_fire_post lneighbours post increasingm fired_pre_groups = finalm.
  Proof.
    intros lneighbours post increasingm finalm fired_pre_groups H;
    elim H;
    intros.
    (* Case map_fire_post_nil *)
    - simpl; auto.
    (* Case map_fire_post_cons *)
    - simpl; apply fire_post_compl in H0; rewrite H0; auto.
  Qed.
  
  (*************************************************)
  (****************** SPN FIRE *********************)
  (*************************************************)

  (*
   * Function : Returns  "transitions fired (fire_groups)" + "final marking",
   *            composing spn_map_fire_post with spn_map_fire_pre
   *)
  Definition spn_fire
             (lneighbours : list neighbours_type)
             (pre test inhib post : weight_type)
             (steadym : marking_type)
             (cfgroups : list (list trans_type)) :
    (list (list trans_type)) * marking_type :=
    let (fired_groups, intermediatem) := (spn_map_fire_pre lneighbours pre test inhib steadym cfgroups) in
    (fired_groups, (map_fire_post lneighbours post intermediatem fired_groups)).

  Functional Scheme spn_fire_ind := Induction for spn_fire Sort Prop.
  
  (*** Formal specification : spn_fire ***)
  Inductive spn_fire_spec
            (lneighbours : list neighbours_type)
            (pre test inhib post : weight_type)
            (steadym : marking_type)
            (cfgroups : list (list trans_type)) :
    (list (list trans_type)) * marking_type -> Prop :=
  | spn_fire_cons :
      forall (fired_groups : list (list trans_type))
             (intermediatem finalm : marking_type),
      spn_map_fire_pre_spec lneighbours pre test inhib steadym cfgroups (fired_groups, intermediatem) ->
      map_fire_post_spec lneighbours post intermediatem fired_groups finalm ->
      spn_fire_spec lneighbours pre test inhib post steadym cfgroups (fired_groups, finalm).

  (*** Correctness proof : spn_fire ***)
  Theorem spn_fire_correct :
    forall (lneighbours : list neighbours_type)
           (pre test inhib post : weight_type)
           (steadym finalm : marking_type)
           (cfgroups fired_groups : list (list trans_type)),
    spn_fire lneighbours pre test inhib post steadym cfgroups = (fired_groups, finalm) ->
    spn_fire_spec lneighbours pre test inhib post steadym cfgroups (fired_groups, finalm).
  Proof.
    intros lneighbours pre test inhib post steadym finalm cfgroups fired_groups;
    functional induction (spn_fire lneighbours pre test inhib post steadym cfgroups)
               using spn_fire_ind;
    intros.
    apply spn_fire_cons with (intermediatem := intermediatem).
    (* Case spn_map_fire_pre *)
    Search (fst _).
    - apply spn_map_fire_pre_correct. rewrite e.
      injection H; intros.
      rewrite H1; auto.
    (* Case map_fire_post *)
    - injection H; intros; apply map_fire_post_correct.
      rewrite <- H1; rewrite <- H0; auto.                             
  Qed.

  (*** Completeness proof : spn_fire ***)
  Theorem spn_fire_compl :
    forall (lneighbours : list neighbours_type)
           (pre test inhib post : weight_type)
           (steadym finalm : marking_type)
           (cfgroups fired_groups : list (list trans_type)),
    spn_fire_spec lneighbours pre test inhib post steadym cfgroups (fired_groups, finalm) ->
    spn_fire lneighbours pre test inhib post steadym cfgroups = (fired_groups, finalm).
  Proof.
    intros lneighbours pre test inhib post steadym finalm cfgroups fired_groups Hspec;
      elim Hspec; intros.
    unfold spn_fire.
    apply spn_map_fire_pre_compl in H; rewrite H.
    apply map_fire_post_compl in H0; rewrite H0; auto.
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
