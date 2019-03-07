Require Export Hilecop.Utils.HilecopLemmas.
Require Export Hilecop.Utils.HilecopTactics.

(*
 * ============ CODING GUIDELINES ============
 * 
 * - Function names, records, lemmas and theorems idents : 
 *   first letter in lower case, then snake case.
 *
 * - Logical propositions, predicates idents, or every ident that returns a Prop : 
 *   first letter in upper case, then camel case.  
 *  
 *)

(** * Types for generalized, extended and synchronous Petri nets. *)

(*===================================================================*)
(*=== TYPES FOR GENERALIZED, EXTENDED AND SYNCHRONOUS PETRI NETS. ===*)
(*===================================================================*)

(** A place is identified by a unique index. *)

Definition Place := nat.

(** A transition is identified by a unique index. *)

Definition Trans := nat.

(** There are 4 kinds of edges : pre, post, inhib, test 
    along with "some" positive weight (default is 1 usually). *)

(** A given edge, either reaching in or coming out of a place,
    has some weight over 0 or 0 if the edge doesn't exist *)

Definition Weight := Trans -> Place -> nat.

(** Defines a structure containing multiple list of places,
    each one of them corresponding to the pre, test, inhib and post neighbour places
    which will be associated with a transition t (see the lneighbours
    attribute in the Spn Structure). *)

Structure Neighbours : Set := mk_neighbours {
                                  pre_pl : list Place;
                                  test_pl : list Place;
                                  inhib_pl : list Place;
                                  post_pl : list Place
                                }.

(** Returns the concatenation of all list of places contained in neighb. 
    
    Useful for [NoIsolatedPlace] spn's property. *)

Definition flatten_neighbours (neighb : Neighbours) : list Place :=
  neighb.(pre_pl) ++ neighb.(test_pl) ++ neighb.(inhib_pl) ++ neighb.(post_pl).

(** Returns the list of all places referenced in lneighbours.
    A same place can possibly appear multiple times in the
    resulting list.            
    
    Useful for NoIsolatedPlace spn's property. *)

Fixpoint flatten_lneighbours (lneighbours : list (Trans * Neighbours)) :
  list Place :=
  match lneighbours with
  | (t, neighb) :: tail => (flatten_neighbours neighb) ++ (flatten_lneighbours tail)
  | [] => []
  end.

Functional Scheme flatten_lneighbours_ind := Induction for flatten_lneighbours Sort Prop.

(** ** Structure of Synchronous Petri Nets. *)

(*==================================================================*)
(*============== STRUCTURE OF SYNCHRONOUS PETRI NETS ===============*)
(*==================================================================*)

Structure Spn : Set :=
  mk_Spn {
      
      places : list Place;
      transs : list Trans;
      pre : Weight;
      post : Weight;
      test : Weight;
      inhib : Weight;
      initial_marking : list (Place * nat);

      (* Each list of transitions contained in priority_groups is 
       * a priority-ordered list of transitions.
       * Defines priority relation between transitions,
       * necessary to obtain a deterministic Petri net. *)
      priority_groups : list (list Trans);

      (* Contains the list of pre, test, inhib and post places 
       * associated with each transition of the Spn. *)
      lneighbours : list (Trans * Neighbours);
      
    }.


(** ------------------------------------------------------- *)
(** ------------------------------------------------------- *)

(** ** Properties on the Spn structure. *)

(*==============================================*)
(*============ PROPERTIES ON Spn ===============*)
(*==============================================*)

(** *** Spn helpers predicates *)

(* The same places are referenced in m and m'. *)

Definition MarkingHaveSameStruct
           (m : list (Place * nat))
           (m' : list (Place * nat)) := fst (split m) = fst (split m').

(** [m] is a weaker marking compared to [m'], if all places 
    in [m] are marked with the same amount or less tokens than
    places in [m'].

    Condition: [m] and [m'] are comparable, verify MarkingHaveSameStruct. 
 *)

Definition IsWeakerMarking (m m' : list (Place * nat)) : Prop :=
  MarkingHaveSameStruct m m' ->
  forall (p : Place) (n n' : nat), In (p, n) m -> In (p, n') m' -> n <= n'.

(** All transitions in [priority_groups] are referenced 
    in the list of neighbours [lneighbours]. *)

Definition PriorityGroupsAreRefInLneighbours
           (priority_groups : list (list Trans))
           (lneighbours : list (Trans * Neighbours)) :=
  forall pgroup : list Trans,
    In pgroup priority_groups ->
    forall t : Trans, In t pgroup -> In t (fst (split lneighbours)).

(** *** Properties on places and transitions *)

Definition NoDupPlaces (spn : Spn) := NoDup spn.(places).  
Definition NoDupTranss (spn : Spn) := NoDup spn.(transs).

(** *** Properties on priority_groups *)

(** For all transition t, t is in [spn.(transs)] iff 
    there exists a group in [spn.(priority_groups)] containing t. *)

Definition NoUnknownInPriorityGroups (spn : Spn) :=
  Permutation spn.(transs) (concat spn.(priority_groups)).

(** For all transition t in one of the group of priority_groups, 
    t is contained in only one group of priority_groups. *)

Definition NoIntersectInPriorityGroups (spn : Spn) :=
  NoDup (concat spn.(priority_groups)).

(** *** Properties on lneighbours *)

Definition NoDupLneighbours (spn : Spn) := NoDup spn.(lneighbours).

(** For all place p, p is in places iff p is in the neighbourhood 
    of at least one transition. *)

Definition NoIsolatedPlace (spn : Spn) := 
  incl spn.(places) (flatten_lneighbours spn.(lneighbours)).

(** All places in [flatten_lneighbours spn.(lneighbours)] are in [spn.(places)]. *)

Definition NoUnknownPlaceInNeighbours (spn : Spn) :=
  incl (flatten_lneighbours spn.(lneighbours)) spn.(places).

(** For all transition t, t is in spn.transs iff t is referenced in [spn.(lneighbours)]. *)

Definition NoUnknownTransInLNeighbours (spn : Spn) :=
  spn.(transs) = fst (split spn.(lneighbours)).

(** Forall neighbours_of_t in spn.(lneighbours), there exists one list of places that is not empty.
    i.e. A transition has at least one neighbour place. *)

Definition NoIsolatedTrans (spn : Spn) :=
  forall (t : Trans) (neighbours_of_t : Neighbours),
    In (t, neighbours_of_t) spn.(lneighbours) ->
    (flatten_neighbours neighbours_of_t) <> [].

(** ∀ p ∈ P, ∀ (t, neighb) ∈ spn.(lneighbours), 
    if p ∈ (pre_pl neighb) then pre(p, t) >= 1 and
    if p ∉ (pre_pl neighb) then pre(p, t) = 0.
 *)

Definition AreWellDefinedPreEdges (spn : Spn) :=
  forall (t : Trans)
    (neighbours_of_t : Neighbours)
    (p : Place),
    In (t, neighbours_of_t) spn.(lneighbours) ->
    (In p (pre_pl neighbours_of_t) -> (pre spn t p) >= 1) /\
    (~In p (pre_pl neighbours_of_t) -> (pre spn t p) = 0).

(** ∀ p ∈ P, ∀ (t, neighb) ∈ spn.(lneighbours), 
    if p ∈ (test_pl neighb) then test(p, t) >= 1 and
    if p ∉ (test_pl neighb) then test(p, t) = 0.
 *)

Definition AreWellDefinedTestEdges (spn : Spn) :=
  forall (t : Trans)
    (neighbours_of_t : Neighbours)
    (p : Place),
    In (t, neighbours_of_t) spn.(lneighbours) ->
    (In p (test_pl neighbours_of_t) -> (test spn t p) >= 1) /\
    (~In p (test_pl neighbours_of_t) -> (test spn t p) = 0).

(** ∀ p ∈ P, ∀ (t, neighb) ∈ spn.(lneighbours), 
    if p ∈ (inhib_pl neighb) then inhib(p, t) >= 1 and
    if p ∉ (inhib_pl neighb) then inhib(p, t) = 0.
 *)

Definition AreWellDefinedInhibEdges (spn : Spn) :=
  forall (t : Trans)
    (neighbours_of_t : Neighbours)
    (p : Place),
    In (t, neighbours_of_t) spn.(lneighbours) ->
    (In p (inhib_pl neighbours_of_t) -> (inhib spn t p) >= 1) /\
    (~In p (inhib_pl neighbours_of_t) -> (inhib spn t p) = 0).

(** *** Properties on marking *)

(** For all place p, p is in spn.(places) iff p is referenced in marking. *)
Definition NoUnmarkedPlace (spn : Spn)  :=
  spn.(places) = (fst (split spn.(initial_marking))).

(** *** Checks if a Spn is well-defined. *)

Definition IsWellDefinedSpn (spn : Spn) :=
  NoDupPlaces spn /\
  NoDupTranss spn /\
  NoUnknownInPriorityGroups spn /\
  NoIntersectInPriorityGroups spn /\
  NoDupLneighbours spn /\
  NoIsolatedPlace spn /\
  NoUnknownPlaceInNeighbours spn /\
  NoUnknownTransInLNeighbours spn /\
  NoIsolatedTrans spn /\
  AreWellDefinedPreEdges spn /\
  AreWellDefinedTestEdges spn /\
  AreWellDefinedInhibEdges spn /\
  NoUnmarkedPlace spn.

(** ** Lemmas on the Spn structure. *)

(*==========================================*)
(*============ LEMMAS ON Spn ===============*)
(*==========================================*)

(** For all well-defined Spn, If a Place p ∈ neighbourhood of Trans t,
    such that (t, neigh_of_t) ∈ spn.(lneighbours), then 
    p ∈ (flatten_lneighbours spn.(lneighbours))
 *)

Lemma in_neigh_in_flatten :
  forall (spn : Spn) (t : Trans) (neigh_of_t : Neighbours) (p : Place),
    IsWellDefinedSpn spn ->
    In (t, neigh_of_t) spn.(lneighbours) ->
    In p (flatten_neighbours neigh_of_t) ->
    In p (flatten_lneighbours spn.(lneighbours)).
Proof.
  intros spn t neigh_of_t p; intros.
  functional induction (flatten_lneighbours (lneighbours spn))
             using flatten_lneighbours_ind; intros.
  - elim H0.
  - apply in_or_app.
    apply in_inv in H0; elim H0; intros.
    + injection H2; intros; rewrite H3; left; assumption.
    + apply IHl0 in H2; right; assumption.
Qed.

(** ** Spn state. *)

(** Defines the state of an Spn. *)

Structure SpnState := mk_SpnState { fired : list Trans; marking : list (Place * nat) }.

(** Checks that state s is well-defined compared to spn's structure. *)

Definition IsWellDefinedSpnState (spn : Spn) (s : SpnState) :=
  MarkingHaveSameStruct spn.(initial_marking) s.(marking) /\
  incl s.(fired) spn.(transs).

(*===============================================*)
(*===== EQUALITY DECIDABILITY FOR Spn TYPES =====*)
(*===============================================*)

(** *** Equality decidability for Neighbours *)

Definition neighbours_eq_dec :
  forall x y : Neighbours, {x = y} + {x <> y}.
Proof.
  repeat decide equality.    
Defined.

(*====================================================*)
(*=============== MARKING SECTION  ===================*)
(*====================================================*)

Section Marking.
  
  (** Returns the number of tokens associated with the place [p]
      in marking [marking].
      
       Returns None if [p] doesn't belong to the marking. *)
  
  Fixpoint get_m (marking : list (Place * nat)) (p : Place) : option nat :=
    match marking with
    | (place, nboftokens) :: tail => if p =? place then
                                       Some nboftokens
                                     else get_m tail p
    (* Exception : p is not in marking. *)
    | [] => None
    end.

  Functional Scheme get_m_ind := Induction for get_m Sort Prop.

  (** Correctness proof for get_m. *)
  
  Lemma get_m_correct :
    forall (marking : list (Place * nat)) (p : Place) (n : nat),
      get_m marking p = Some n -> In (p, n) marking.
  Proof.
    intros marking p; functional induction (get_m marking p) using get_m_ind; intros.
    - inversion H.
    - apply beq_nat_true in e1; rewrite e1.
      injection H; intro; rewrite H0.
      apply in_eq.
    - apply in_cons; apply IHo; assumption.
  Qed.

  (** Correctness proof for get_m. *)
  
  Lemma get_m_complete :
    forall (marking : list (Place * nat)) (p : Place) (n : nat),
      NoDup (fst (split marking)) ->
      In (p, n) marking -> get_m marking p = Some n.
  Proof.
    intros marking p n; intros.
    functional induction (get_m marking p) using get_m_ind; intros.
    - elim H0.
    - rewrite fst_split_cons_app in H; simpl in H.
      apply NoDup_cons_iff in H.
      apply in_inv in H0.
      elim H0; intro.
      + injection H1; intros; rewrite H2; reflexivity.
      + elim H; intros.
        apply beq_nat_true in e1; rewrite e1 in H1.
        apply in_fst_split in H1; contradiction.
    - apply IHo.
      + rewrite fst_split_cons_app in H; simpl in H.
        apply NoDup_cons_iff in H.
        elim H; auto.
      + apply in_inv in H0.
        elim H0; intro.
        -- injection H1; intros; symmetry in H3.
           apply beq_nat_false in e1; contradiction.
        -- assumption.
  Qed.
  
  (** Equality decidability between two pairs of nat. 
      Necessary to use the replace_occ function. *)
  
  Definition prodnat_eq_dec :
    forall (x y : (nat * nat)), {x = y} + {x <> y}.
  Proof.
    decide equality.
    decide equality.
    decide equality.
  Defined.

  (** Replaces every occurence of occ by repl
      in list l.
      Inspired from the remove function. *)
  
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
  
  (** Function : Given a marking m, add/remove nboftokens tokens (if not None)
                 inside place p and returns the new marking.
   
      Param nboftokens : number of tokens to add or sub for place p.
   
      Param op : addition or substraction operator. *)
  
  Definition modify_m
             (marking : list (Place * nat))
             (p : Place)
             (op : nat -> nat -> nat)
             (nboftokens : nat) : option (list (Place * nat)) :=
    match get_m marking p with
    (* The couple (i, n) to remove must be unique. *)
    | Some n =>
      Some (replace_occ prodnat_eq_dec (p, n) (p, (op n nboftokens)) marking)
    | None => None 
    end.
  
End Marking.

(*====================================================*)
(*=============== NEIGHBOURS SECTION  ================*)
(*====================================================*)

Section Neighbours.

  (** Function : Returns the element of type Neighbours
                 associated with transition t in the list lneighbours.
               
                 Returns None if transition t is not referenced
                 in lneighbours. *)
  
  Fixpoint get_neighbours
           (lneighbours : list (Trans * Neighbours))
           (t : Trans) {struct lneighbours} : option Neighbours :=
    match lneighbours with
    | (t', neighbours) :: tail => if t' =? t then
                                    Some neighbours
                                  else get_neighbours tail t
    | [] => None 
    end.
  
End Neighbours.

(*===============================================================*)
(*== CHECKS NB OF TOKENS IN NEIGHBOUR PLACES OF A TRANSITION T ==*)
(*== WITH WEIGHT OF ITS ADJACENT EDGES.                        ==*)
(*===============================================================*)

Section Edges.
  
  (** Returns [Some true] if M(p) >= pre(p, t), [Some false] otherwise. 
                 
      Raises an error (i.e. None) if [get_m] fail. *)
  
  Definition check_pre
             (spn : Spn)
             (marking : list (Place * nat))
             (p : Place)
             (t : Trans) : option bool :=
    match get_m marking p with
    | Some nboftokens => Some ((pre spn t p) <=? nboftokens)
    | None => None
    end.

  Functional Scheme check_pre_ind := Induction for check_pre Sort Prop.

  (** Correctness proof for check_pre. *)

  Lemma check_pre_correct :
    forall (spn : Spn)
      (marking : list (Place * nat))
      (p : Place)
      (t : Trans)
      (n : nat),
      IsWellDefinedSpn spn ->
      MarkingHaveSameStruct spn.(initial_marking) marking ->
      In (p, n) marking ->
      check_pre spn marking p t = Some true ->
      (pre spn t p) <= n.
  Proof.
    intros spn marking p t;
      functional induction (check_pre spn marking p t) using check_pre_ind;
      intros.
    (* General case, all went well. *)
    - apply get_m_correct in e.
      (* Proves that ∀ (p, n), (p, nboftokens) ∈ marking ⇒ n = nboftokens. *)
      unfold IsWellDefinedSpn in H; decompose [and] H; clear H; intros.
      unfold MarkingHaveSameStruct in H0.
      unfold NoUnmarkedPlace in H16.
      unfold NoDupPlaces in H3.
      rewrite H0 in H16; rewrite H16 in H3.
      assert (fst (p, n) = fst (p, nboftokens)) by (simpl; reflexivity).
      generalize (nodup_same_pair marking H3 (p, n) (p, nboftokens) H1 e H); intro.
      injection H15; intro.
      rewrite <- H17 in H2; injection H2; intro.
      apply (leb_complete (pre spn t p) n H18).
    - inversion H2.
  Qed.

  (** Completeness proof for check_pre. *)

  Lemma check_pre_complete :
    forall (spn : Spn)
      (marking : list (Place * nat))
      (p : Place)
      (t : Trans)
      (n : nat),
      IsWellDefinedSpn spn ->
      MarkingHaveSameStruct spn.(initial_marking) marking ->
      In (p, n) marking ->
      (pre spn t p) <= n ->
      check_pre spn marking p t = Some true.
  Proof.
    intros spn marking p t n; intros.
    unfold check_pre.
    (* Builds the condition NoDup (fst (split marking)). 
       Necessary to apply get_m_complete. *)
    unfold IsWellDefinedSpn in H; decompose [and] H; clear H; intros.
    unfold NoDupPlaces in H3.
    unfold MarkingHaveSameStruct in H0.
    unfold NoUnmarkedPlace in H16.
    rewrite H16 in H3; rewrite H0 in H3.
    generalize (get_m_complete marking p n H3 H1); intro.
    rewrite H.
    apply leb_correct in H2; rewrite H2; reflexivity.
  Qed.
  
  (** Function : Returns [Some true] if ∀ p ∈ [pre_places], M(p) >= pre(p, t).
                 
                 Raises an error if [get_m] fails. *)
  
  Fixpoint map_check_pre_aux
           (spn : Spn)
           (marking : list (Place * nat))
           (pre_places : list Place)
           (t : Trans)
           (check_result : bool) {struct pre_places} : option bool :=
    match pre_places with
    | p :: tail =>
      match check_pre spn marking p t with
      | None => None
      | Some b =>
        map_check_pre_aux spn marking tail t (b && check_result)
      end 
    | [] => Some check_result
    end.  

  Functional Scheme map_check_pre_aux_ind := Induction for map_check_pre_aux Sort Prop.

    (** ∀ spn, marking, pre_places, t, b,
      map_check_pre_aux spn marking pre_places t b = Some true ⇒
      b = true.
   *)
  Lemma map_check_pre_aux_true_if_true :
    forall (spn : Spn)
      (marking : list (Place * nat))
      (pre_places : list Place)
      (t : Trans)
      (b : bool),
      map_check_pre_aux spn marking pre_places t b = Some true ->
      b = true.
  Proof.
    intros spn marking pre_places t b;
      functional induction (map_check_pre_aux spn marking pre_places t b)
                 using map_check_pre_aux_ind;
      intros.
    - injection H; auto.
    - apply IHo in H; apply andb_prop in H; elim H; auto.
    - inversion H.
  Qed.

  
  (** Correctness proof for map_check_pre_aux. *)
  
  Lemma map_check_pre_aux_correct :
    forall (spn : Spn)
      (marking : list (Place * nat))
      (pre_places : list Place)
      (t : Trans)
      (b : bool)
      (neighbours_of_t : Neighbours),
      IsWellDefinedSpn spn ->
      MarkingHaveSameStruct spn.(initial_marking) marking ->
      In (t, neighbours_of_t) spn.(lneighbours) ->
      incl pre_places (pre_pl neighbours_of_t) ->
      map_check_pre_aux spn marking pre_places t b = Some true ->
      forall (p : Place) (n : nat),
        In p pre_places -> In (p, n) marking -> (pre spn t p) <= n.
  Proof.
    intros spn marking pre_places t b;
      functional induction (map_check_pre_aux spn marking pre_places t b)
                 using map_check_pre_aux_ind;
      intros.
    - inversion H4.
    - apply in_inv in H4; elim H4; intro.
      + apply map_check_pre_aux_true_if_true in H3.
        apply andb_prop in H3; elim H3; intros.
        rewrite H7 in e0.
        rewrite H6 in e0.
        generalize (check_pre_correct spn marking p0 t n H H0 H5 e0); intro.
        assumption.
      + apply IHo with (neighbours_of_t := neighbours_of_t);
          (assumption ||
           unfold incl in H2;
           unfold incl; intros;
           apply in_cons with (a := p) in H7;
           apply (H2 a H7)).
    - inversion H3.
  Qed.

  (** Completeness proof for map_check_pre_aux. *)
  
  Lemma map_check_pre_aux_complete :
    forall (spn : Spn)
           (marking : list (Place * nat))
           (pre_places : list Place)
           (t : Trans)
           (neighbours_of_t : Neighbours),
      IsWellDefinedSpn spn ->
      MarkingHaveSameStruct spn.(initial_marking) marking ->
      In (t, neighbours_of_t) spn.(lneighbours) ->
      incl pre_places (pre_pl neighbours_of_t) ->
      (forall (p : Place) (n : nat),
          In p pre_places -> In (p, n) marking -> (pre spn t p) <= n) ->
      map_check_pre_aux spn marking pre_places t true = Some true.
  Proof.
    intros spn marking pre_places t.
    functional induction (map_check_pre_aux spn marking pre_places t true)
               using map_check_pre_aux_ind;
      intros.
    - simpl; reflexivity.
    - simpl.
      (* Deduces hypotheses necessary to apply check_pre_complete. *)
      assert (In p (p :: tail)) by apply in_eq.
      generalize (H2 p H4); intro.
      assert (In p (flatten_neighbours neighbours_of_t))
        by (unfold flatten_neighbours; apply in_or_app; left; assumption).
      generalize (in_neigh_in_flatten spn t neighbours_of_t p H H1 H6); intro.
      assert (H' := H).
      unfold IsWellDefinedSpn in H; decompose [and] H; clear H; intros.
      unfold NoUnknownPlaceInNeighbours in H14.
      unfold incl in H14.
      apply (H14 p) in H7.
      unfold NoUnmarkedPlace in H21; rewrite H21 in H7.
      unfold MarkingHaveSameStruct in H0; rewrite H0 in H7.
      generalize (in_fst_split_in_pair p marking H7); intro.
      elim H; intros; generalize (H3 p x H4 H20); intro.
      (* Applies check_pre_complete, then the induction hypothesis. *)
      generalize (check_pre_complete spn marking p t x H' H0 H20 H22); intro.
      (* Use b = true to rewrite the goal and apply the induction hypothesis. *)
      rewrite H23 in e0; injection e0; intro.
      rewrite <- H24 in IHo; rewrite andb_comm in IHo; rewrite andb_true_r in IHo.
      rewrite <- H24; rewrite andb_comm; rewrite andb_true_r.
      apply IHo with (neighbours_of_t := neighbours_of_t).
      + assumption.
      + assumption.
      + assumption.
      + unfold incl; intros.
        unfold incl in H2.
        apply in_cons with (a := p) in H25.
        apply (H2 a H25).
      + intros; apply in_cons with (a := p) in H25.
        apply (H3 p0 n H25 H26).
    (* Deduces hypotheses necessary to apply check_pre_complete. *)
    - assert (In p (p :: tail)) by apply in_eq.
      generalize (H2 p H4); intro.
      assert (In p (flatten_neighbours neighbours_of_t))
        by (unfold flatten_neighbours; apply in_or_app; left; assumption).
      generalize (in_neigh_in_flatten spn t neighbours_of_t p H H1 H6); intro.
      assert (H' := H); unfold IsWellDefinedSpn in H; decompose [and] H; clear H; intros.
      unfold NoUnknownPlaceInNeighbours in H14; unfold incl in H14; apply (H14 p) in H7.
      unfold NoUnmarkedPlace in H21; rewrite H21 in H7.
      unfold MarkingHaveSameStruct in H0; rewrite H0 in H7.
      generalize (in_fst_split_in_pair p marking H7); intro; elim H; intros.
      generalize (H3 p x H4 H20); intro.
      generalize (check_pre_complete spn marking p t x H' H0 H20 H22); intro.
      (* Then, shows a contradiction. *)
      rewrite e0 in H23; inversion H23.
  Qed.
  
  (** Wrapper around [map_check_pre_aux]. *)
  
  Definition map_check_pre
             (spn : Spn)
             (marking : list (Place * nat))
             (pre_places : list Place)
             (t : Trans) : option bool :=
    map_check_pre_aux spn marking pre_places t true.

  Functional Scheme map_check_pre_ind := Induction for map_check_pre Sort Prop.

  (** Correctness proof for map_check_pre. *)

  Lemma map_check_pre_correct :
    forall (spn : Spn)
      (marking : list (Place * nat))
      (t : Trans)
      (neighbours_of_t : Neighbours),
      IsWellDefinedSpn spn ->
      MarkingHaveSameStruct spn.(initial_marking) marking ->
      In (t, neighbours_of_t) spn.(lneighbours) ->
      map_check_pre spn marking (pre_pl neighbours_of_t) t = Some true ->
      forall (p : Place) (n : nat), In (p, n) marking -> (pre spn t p) <= n.
  Proof.
    intros spn marking t neighbours_of_t.
    functional induction (map_check_pre spn marking (pre_pl neighbours_of_t) t)
               using map_check_pre_ind;
      intros.
    assert (incl (pre_pl neighbours_of_t) (pre_pl neighbours_of_t)) by apply incl_refl.
    (* Proof in two stages. *)
    assert (H' := classic (In p (pre_pl neighbours_of_t))).
    elim H'; intro.
    (* First stage, p ∈ pre_places, then we apply map_check_pre_aux_correct. *)
    - generalize (map_check_pre_aux_correct
                    spn marking (pre_pl neighbours_of_t) t true neighbours_of_t
                    H H0 H1 H4 H2); intro. 
      apply (H6 p n H5 H3).
    (* Second stage, p ∉ pre_places, then (pre spn t p) = 0 *)
    - unfold IsWellDefinedSpn in H; decompose [and] H; clear H; intros.
      unfold AreWellDefinedPreEdges in H15.
      generalize (H15 t neighbours_of_t p H1); intro.
      elim H; clear H; intros.
      generalize (H18 H5); intro; rewrite H20; apply Peano.le_0_n.
  Qed.

  (** Correctness proof for map_check_pre. *)

  Lemma map_check_pre_complete :
    forall (spn : Spn)
           (marking : list (Place * nat))
           (t : Trans)
           (neighbours_of_t : Neighbours),
      IsWellDefinedSpn spn ->
      MarkingHaveSameStruct spn.(initial_marking) marking ->
      In (t, neighbours_of_t) spn.(lneighbours) ->
      (forall (p : Place) (n : nat), In (p, n) marking -> (pre spn t p) <= n) ->
      map_check_pre spn marking (pre_pl neighbours_of_t) t = Some true.
  Proof.
    intros spn marking t neighbours_of_t.
    functional induction (map_check_pre spn marking (pre_pl neighbours_of_t) t)
               using map_check_pre_ind;
      intros.
    (* Hypothesis : incl (pre_pl neighbours_of_t) (pre_pl neighbours_of_t) 
       for map_check_pre_aux_complete. *)
    assert (incl (pre_pl neighbours_of_t) (pre_pl neighbours_of_t)) by apply incl_refl.
    (* Apply map_check_pre_aux_complete. *)
    apply map_check_pre_aux_complete with (neighbours_of_t := neighbours_of_t).
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - intros; apply (H2 p n H5).
  Qed.
  
  (** Returns [Some true] if M(p) >= test(p, t), [Some false] otherwise. 
                 
      Raises an error (i.e. None) if [get_m] fail. *)
  
  Definition check_test
             (spn : Spn)
             (marking : list (Place * nat))
             (p : Place)
             (t : Trans) : option bool :=
    match get_m marking p with
    | Some nboftokens => Some ((test spn t p) <=? nboftokens)
    | None => None
    end.

  Functional Scheme check_test_ind := Induction for check_test Sort Prop.
  
  (** Correctness proof for check_test. *)

  Lemma check_test_correct :
    forall (spn : Spn)
      (marking : list (Place * nat))
      (p : Place)
      (t : Trans)
      (n : nat),
      IsWellDefinedSpn spn ->
      MarkingHaveSameStruct spn.(initial_marking) marking ->
      In (p, n) marking ->
      check_test spn marking p t = Some true ->
      (test spn t p) <= n.
  Proof.
    intros spn marking p t;
      functional induction (check_test spn marking p t) using check_test_ind;
      intros.
    (* General case, all went well. *)
    - apply get_m_correct in e.
      (* Proves that ∀ (p, n), (p, nboftokens) ∈ marking ⇒ n = nboftokens. *)
      unfold IsWellDefinedSpn in H; decompose [and] H; clear H; intros.
      unfold MarkingHaveSameStruct in H0.
      unfold NoUnmarkedPlace in H16.
      unfold NoDupPlaces in H3.
      rewrite H0 in H16; rewrite H16 in H3.
      assert (fst (p, n) = fst (p, nboftokens)) by (simpl; reflexivity).
      generalize (nodup_same_pair marking H3 (p, n) (p, nboftokens) H1 e H); intro.
      injection H15; intro.
      rewrite <- H17 in H2; injection H2; intro.
      apply (leb_complete (test spn t p) n H18).
    - inversion H2.
  Qed.

  (** Completeness proof for check_test. *)

  Lemma check_test_complete :
    forall (spn : Spn)
           (marking : list (Place * nat))
           (p : Place)
           (t : Trans)
           (n : nat),
      IsWellDefinedSpn spn ->
      MarkingHaveSameStruct spn.(initial_marking) marking ->
      In (p, n) marking ->
      (test spn t p) <= n ->
      check_test spn marking p t = Some true.
  Proof.
    intros spn marking p t n; intros.
    unfold check_test.
    (* Builds the condition NoDup (fst (split marking)). 
       Necessary to apply get_m_complete. *)
    unfold IsWellDefinedSpn in H; decompose [and] H; clear H; intros.
    unfold NoDupPlaces in H3.
    unfold MarkingHaveSameStruct in H0.
    unfold NoUnmarkedPlace in H16.
    rewrite H16 in H3; rewrite H0 in H3.
    generalize (get_m_complete marking p n H3 H1); intro.
    rewrite H.
    apply leb_correct in H2; rewrite H2; reflexivity.
  Qed.
  
  (** Function : Returns [Some true] if ∀ p ∈ [test_places], M(p) >= test(p, t).
                 
                 Raises an error if [get_m] fails. *)
  
  Fixpoint map_check_test_aux
           (spn : Spn)
           (marking : list (Place * nat))
           (test_places : list Place)
           (t : Trans)
           (check_result : bool) {struct test_places} : option bool :=
    match test_places with
    | p :: tail =>
      match check_test spn marking p t with
      | None => None
      | Some b =>
        map_check_test_aux spn marking tail t (b && check_result)
      end 
    | [] => Some check_result
    end.  

  Functional Scheme map_check_test_aux_ind := Induction for map_check_test_aux Sort Prop.

    (** ∀ spn, marking, test_places, t, b,
      map_check_test_aux spn marking test_places t b = Some true ⇒
      b = true.
   *)
  Lemma map_check_test_aux_true_if_true :
    forall (spn : Spn)
      (marking : list (Place * nat))
      (test_places : list Place)
      (t : Trans)
      (b : bool),
      map_check_test_aux spn marking test_places t b = Some true ->
      b = true.
  Proof.
    intros spn marking test_places t b;
      functional induction (map_check_test_aux spn marking test_places t b)
                 using map_check_test_aux_ind;
      intros.
    - injection H; auto.
    - apply IHo in H; apply andb_prop in H; elim H; auto.
    - inversion H.
  Qed.
  
  (** Correctness proof for map_check_test_aux. *)
  
  Lemma map_check_test_aux_correct :
    forall (spn : Spn)
      (marking : list (Place * nat))
      (test_places : list Place)
      (t : Trans)
      (b : bool)
      (neighbours_of_t : Neighbours),
      IsWellDefinedSpn spn ->
      MarkingHaveSameStruct spn.(initial_marking) marking ->
      In (t, neighbours_of_t) spn.(lneighbours) ->
      incl test_places (test_pl neighbours_of_t) ->
      map_check_test_aux spn marking test_places t b = Some true ->
      forall (p : Place) (n : nat),
        In p test_places -> In (p, n) marking -> (test spn t p) <= n.
  Proof.
    intros spn marking test_places t b;
      functional induction (map_check_test_aux spn marking test_places t b)
                 using map_check_test_aux_ind;
      intros.
    - inversion H4.
    - apply in_inv in H4; elim H4; intro.
      + apply map_check_test_aux_true_if_true in H3.
        apply andb_prop in H3; elim H3; intros.
        rewrite H7 in e0.
        rewrite H6 in e0.
        generalize (check_test_correct spn marking p0 t n H H0 H5 e0); intro.
        assumption.
      + apply IHo with (neighbours_of_t := neighbours_of_t);
          (assumption ||
           unfold incl in H2;
           unfold incl; intros;
           apply in_cons with (a := p) in H7;
           apply (H2 a H7)).
    - inversion H3.
  Qed.
  
  (** Completeness proof for map_check_test_aux. *)
  
  Lemma map_check_test_aux_complete :
    forall (spn : Spn)
           (marking : list (Place * nat))
           (test_places : list Place)
           (t : Trans)
           (neighbours_of_t : Neighbours),
      IsWellDefinedSpn spn ->
      MarkingHaveSameStruct spn.(initial_marking) marking ->
      In (t, neighbours_of_t) spn.(lneighbours) ->
      incl test_places (test_pl neighbours_of_t) ->
      (forall (p : Place) (n : nat),
          In p test_places -> In (p, n) marking -> (test spn t p) <= n) ->
      map_check_test_aux spn marking test_places t true = Some true.
  Proof.
    intros spn marking test_places t.
    functional induction (map_check_test_aux spn marking test_places t true)
               using map_check_test_aux_ind;
      intros.
    - simpl; reflexivity.
    - simpl.
      (* Deduces hypotheses necessary to apply check_test_complete. *)
      assert (In p (p :: tail)) by apply in_eq.
      generalize (H2 p H4); intro.
      assert (In p (flatten_neighbours neighbours_of_t))
        by (unfold flatten_neighbours; apply in_or_app; right; apply in_or_app; left; assumption).
      generalize (in_neigh_in_flatten spn t neighbours_of_t p H H1 H6); intro.
      assert (H' := H).
      unfold IsWellDefinedSpn in H; decompose [and] H; clear H; intros.
      unfold NoUnknownPlaceInNeighbours in H14.
      unfold incl in H14.
      apply (H14 p) in H7.
      unfold NoUnmarkedPlace in H21; rewrite H21 in H7.
      unfold MarkingHaveSameStruct in H0; rewrite H0 in H7.
      generalize (in_fst_split_in_pair p marking H7); intro.
      elim H; intros; generalize (H3 p x H4 H20); intro.
      (* Applies check_test_complete, then the induction hypothesis. *)
      generalize (check_test_complete spn marking p t x H' H0 H20 H22); intro.
      (* Use b = true to rewrite the goal and apply the induction hypothesis. *)
      rewrite H23 in e0; injection e0; intro.
      rewrite <- H24 in IHo; rewrite andb_comm in IHo; rewrite andb_true_r in IHo.
      rewrite <- H24; rewrite andb_comm; rewrite andb_true_r.
      apply IHo with (neighbours_of_t := neighbours_of_t).
      + assumption.
      + assumption.
      + assumption.
      + unfold incl; intros.
        unfold incl in H2.
        apply in_cons with (a := p) in H25.
        apply (H2 a H25).
      + intros; apply in_cons with (a := p) in H25.
        apply (H3 p0 n H25 H26).
    (* Deduces hypotheses necessary to apply check_test_complete. *)
    - assert (In p (p :: tail)) by apply in_eq.
      generalize (H2 p H4); intro.
      (* p ∈ (flatten_neighbours neighbours_of_t) *)
      assert (In p (flatten_neighbours neighbours_of_t))
        by (unfold flatten_neighbours; apply in_or_app; right; apply in_or_app; left; assumption).
      (* p ∈ (flatten_neighbours neighbours_of_t) ⇒ p ∈ (flatten spn.(lneighbours)) *)
      generalize (in_neigh_in_flatten spn t neighbours_of_t p H H1 H6); intro.
      assert (H' := H); unfold IsWellDefinedSpn in H; decompose [and] H; clear H; intros.
      unfold NoUnknownPlaceInNeighbours in H14; unfold incl in H14; apply (H14 p) in H7.
      unfold NoUnmarkedPlace in H21; rewrite H21 in H7.
      unfold MarkingHaveSameStruct in H0; rewrite H0 in H7.
      (* ∃ n, (p, n) ∈ marking *)
      generalize (in_fst_split_in_pair p marking H7); intro; elim H; intros.
      (* Applies the completeness hypothesis. *)
      generalize (H3 p x H4 H20); intro.
      (* Applies check_test_complete *)
      generalize (check_test_complete spn marking p t x H' H0 H20 H22); intro.
      (* Then, shows a contradiction. *)
      rewrite e0 in H23; inversion H23.
  Qed.
  
  (** Wrapper around [map_check_test_aux]. *)
  
  Definition map_check_test
             (spn : Spn)
             (marking : list (Place * nat))
             (test_places : list Place)
             (t : Trans) : option bool :=
    map_check_test_aux spn marking test_places t true.

  Functional Scheme map_check_test_ind := Induction for map_check_test Sort Prop.
  
  (** Correctness proof for map_check_test. *)

  Lemma map_check_test_correct :
    forall (spn : Spn)
      (marking : list (Place * nat))
      (t : Trans)
      (neighbours_of_t : Neighbours),
      IsWellDefinedSpn spn ->
      MarkingHaveSameStruct spn.(initial_marking) marking ->
      In (t, neighbours_of_t) spn.(lneighbours) ->
      map_check_test spn marking (test_pl neighbours_of_t) t = Some true ->
      forall (p : Place) (n : nat), In (p, n) marking -> (test spn t p) <= n.
  Proof.
    intros spn marking t neighbours_of_t.
    functional induction (map_check_test spn marking (test_pl neighbours_of_t) t)
               using map_check_test_ind;
      intros.
    assert (incl (test_pl neighbours_of_t) (test_pl neighbours_of_t)) by apply incl_refl.
    (* Proof in two stages. *)
    assert (H' := classic (In p (test_pl neighbours_of_t))).
    elim H'; intro.
    (* First stage, p ∈ test_places, then we apply map_check_test_aux_correct. *)
    - generalize (map_check_test_aux_correct
                    spn marking (test_pl neighbours_of_t) t true neighbours_of_t
                    H H0 H1 H4 H2); intro. 
      apply (H6 p n H5 H3).
    (* Second stage, p ∉ test_places, then (test spn t p) = 0 *)
    - unfold IsWellDefinedSpn in H; decompose [and] H; clear H; intros.
      unfold AreWellDefinedTestEdges in H16.
      generalize (H16 t neighbours_of_t p H1); intro.
      elim H; clear H; intros.
      generalize (H18 H5); intro; rewrite H20; apply Peano.le_0_n.
  Qed.

  (** Correctness proof for map_check_test. *)

  Lemma map_check_test_complete :
    forall (spn : Spn)
           (marking : list (Place * nat))
           (t : Trans)
           (neighbours_of_t : Neighbours),
      IsWellDefinedSpn spn ->
      MarkingHaveSameStruct spn.(initial_marking) marking ->
      In (t, neighbours_of_t) spn.(lneighbours) ->
      (forall (p : Place) (n : nat), In (p, n) marking -> (test spn t p) <= n) ->
      map_check_test spn marking (test_pl neighbours_of_t) t = Some true.
  Proof.
    intros spn marking t neighbours_of_t.
    unfold map_check_test; intros.
    assert (incl (test_pl neighbours_of_t) (test_pl neighbours_of_t)) by apply incl_refl.
    (* Apply map_check_test_aux_complete. *)
    apply map_check_test_aux_complete with (neighbours_of_t := neighbours_of_t).
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - intros; apply (H2 p n H5).
  Qed.
  
  (** Returns [Some true] if M(p) >= inhib(p, t), [Some false] otherwise. 
                 
      Raises an error (i.e. None) if [get_m] fail. *)
  
  Definition check_inhib
             (spn : Spn)
             (marking : list (Place * nat))
             (p : Place)
             (t : Trans) : option bool :=
    match get_m marking p with
    | Some nboftokens => Some ((nboftokens <? (inhib spn t p)) || ((inhib spn t p) =? 0))
    | None => None
    end.

  Functional Scheme check_inhib_ind := Induction for check_inhib Sort Prop.
  
  (** Correctness proof for check_inhib. *)

  Lemma check_inhib_correct :
    forall (spn : Spn)
      (marking : list (Place * nat))
      (p : Place)
      (t : Trans)
      (n : nat),
      IsWellDefinedSpn spn ->
      MarkingHaveSameStruct spn.(initial_marking) marking ->
      In (p, n) marking ->
      check_inhib spn marking p t = Some true ->
      (n < (inhib spn t p) \/ (inhib spn t p) = 0).
  Proof.
    intros spn marking p t;
      functional induction (check_inhib spn marking p t) using check_inhib_ind;
      intros.
    (* General case, all went well. *)
    - apply get_m_correct in e.
      (* Proves that ∀ (p, n), (p, nboftokens) ∈ marking ⇒ n = nboftokens. *)
      unfold IsWellDefinedSpn in H; decompose [and] H; clear H; intros.
      unfold MarkingHaveSameStruct in H0.
      unfold NoUnmarkedPlace in H16.
      unfold NoDupPlaces in H3.
      rewrite H0 in H16; rewrite H16 in H3.
      assert (fst (p, n) = fst (p, nboftokens)) by (simpl; reflexivity).
      (* Determines n = nboftokens *)
      generalize (nodup_same_pair marking H3 (p, n) (p, nboftokens) H1 e H); intro.
      injection H15; intro.
      rewrite <- H17 in H2; injection H2; intro.
      apply orb_prop in H18.
      (* First case: n < (inhib spn t p), second case: (inhib spn t p) = 0 *)
      elim H18; intro.
      + left; apply Nat.ltb_lt; assumption.
      + right; apply Nat.eqb_eq; assumption.
    - inversion H2.
  Qed.

  (** Completeness proof for check_inhib. *)

  Lemma check_inhib_complete :
    forall (spn : Spn)
      (marking : list (Place * nat))
      (p : Place)
      (t : Trans)
      (n : nat),
      IsWellDefinedSpn spn ->
      MarkingHaveSameStruct spn.(initial_marking) marking ->
      In (p, n) marking ->
      (n < (inhib spn t p) \/ (inhib spn t p) = 0) ->
      check_inhib spn marking p t = Some true.
  Proof.
    intros spn marking p t n; intros.
    unfold check_inhib.
    (* Builds the condition NoDup (fst (split marking)). 
       Necessary to apply get_m_complete. *)
    unfold IsWellDefinedSpn in H; decompose [and] H; clear H; intros.
    unfold NoDupPlaces in H3.
    unfold MarkingHaveSameStruct in H0.
    unfold NoUnmarkedPlace in H16.
    rewrite H16 in H3; rewrite H0 in H3.
    (* Applies get_m_complte *)
    generalize (get_m_complete marking p n H3 H1); intro.
    rewrite H; elim H2; intros.
    - apply Nat.ltb_lt in H15; rewrite H15.
      rewrite orb_true_l; reflexivity.
    - apply Nat.eqb_eq in H15; rewrite H15.
      rewrite orb_comm; rewrite orb_true_l; reflexivity.
  Qed.
  
  (** Function : Returns [Some true] if ∀ p ∈ [inhib_places], M(p) >= inhib(p, t).
                 
                 Raises an error if [get_m] fails. *)
  
  Fixpoint map_check_inhib_aux
           (spn : Spn)
           (marking : list (Place * nat))
           (inhib_places : list Place)
           (t : Trans)
           (check_result : bool) {struct inhib_places} : option bool :=
    match inhib_places with
    | p :: tail =>
      match check_inhib spn marking p t with
      | None => None
      | Some b =>
        map_check_inhib_aux spn marking tail t (b && check_result)
      end 
    | [] => Some check_result
    end.  

    Functional Scheme map_check_inhib_aux_ind := Induction for map_check_inhib_aux Sort Prop.

    (** ∀ spn, marking, inhib_places, t, b,
      map_check_inhib_aux spn marking inhib_places t b = Some true ⇒
      b = true.
   *)
  Lemma map_check_inhib_aux_true_if_true :
    forall (spn : Spn)
      (marking : list (Place * nat))
      (inhib_places : list Place)
      (t : Trans)
      (b : bool),
      map_check_inhib_aux spn marking inhib_places t b = Some true ->
      b = true.
  Proof.
    intros spn marking inhib_places t b;
      functional induction (map_check_inhib_aux spn marking inhib_places t b)
                 using map_check_inhib_aux_ind;
      intros.
    - injection H; auto.
    - apply IHo in H; apply andb_prop in H; elim H; auto.
    - inversion H.
  Qed.
  
  (** Correctness proof for map_check_inhib_aux. *)
  
  Lemma map_check_inhib_aux_correct :
    forall (spn : Spn)
      (marking : list (Place * nat))
      (inhib_places : list Place)
      (t : Trans)
      (b : bool)
      (neighbours_of_t : Neighbours),
      IsWellDefinedSpn spn ->
      MarkingHaveSameStruct spn.(initial_marking) marking ->
      In (t, neighbours_of_t) spn.(lneighbours) ->
      incl inhib_places (inhib_pl neighbours_of_t) ->
      map_check_inhib_aux spn marking inhib_places t b = Some true ->
      forall (p : Place) (n : nat),
        In p inhib_places ->
        In (p, n) marking ->
        (n < (inhib spn t p) \/ (inhib spn t p) = 0).
  Proof.
    intros spn marking inhib_places t b;
      functional induction (map_check_inhib_aux spn marking inhib_places t b)
                 using map_check_inhib_aux_ind;
      intros.
    - inversion H4.
    - apply in_inv in H4; elim H4; intro.
      + apply map_check_inhib_aux_true_if_true in H3.
        apply andb_prop in H3; elim H3; intros.
        rewrite H7 in e0.
        rewrite H6 in e0.
        generalize (check_inhib_correct spn marking p0 t n H H0 H5 e0); intro.
        assumption.
      + apply IHo with (neighbours_of_t := neighbours_of_t);
          (assumption ||
           unfold incl in H2;
           unfold incl; intros;
           apply in_cons with (a := p) in H7;
           apply (H2 a H7)).
    - inversion H3.
  Qed.

  (** Completeness proof for map_check_inhib_aux. *)
  
  Lemma map_check_inhib_aux_complete :
    forall (spn : Spn)
           (marking : list (Place * nat))
           (inhib_places : list Place)
           (t : Trans)
           (neighbours_of_t : Neighbours),
      IsWellDefinedSpn spn ->
      MarkingHaveSameStruct spn.(initial_marking) marking ->
      In (t, neighbours_of_t) spn.(lneighbours) ->
      incl inhib_places (inhib_pl neighbours_of_t) ->
      (forall (p : Place) (n : nat),
          In p inhib_places -> In (p, n) marking -> (n < (inhib spn t p) \/ (inhib spn t p) = 0)) ->
      map_check_inhib_aux spn marking inhib_places t true = Some true.
  Proof.
    intros spn marking inhib_places t.
    functional induction (map_check_inhib_aux spn marking inhib_places t true)
               using map_check_inhib_aux_ind;
      intros.
    - simpl; reflexivity.
    - simpl.
      (* Deduces hypotheses necessary to apply check_inhib_complete. *)
      assert (In p (p :: tail)) by apply in_eq.
      generalize (H2 p H4); intro.
      (* p ∈ (flatten_neighbours neighbours_of_t) *)
      assert (In p (flatten_neighbours neighbours_of_t))
        by (unfold flatten_neighbours;
            do 2 (apply in_or_app; right);
            apply in_or_app; left; assumption).
      (* p ∈ (flatten_neighbours neighbours_of_t) ⇒ p ∈ (flatten spn.(lneighbours)) *)
      generalize (in_neigh_in_flatten spn t neighbours_of_t p H H1 H6); intro.
      assert (H' := H).
      unfold IsWellDefinedSpn in H; decompose [and] H; clear H; intros.
      unfold NoUnknownPlaceInNeighbours in H14.
      unfold incl in H14.
      apply (H14 p) in H7.
      unfold NoUnmarkedPlace in H21; rewrite H21 in H7.
      unfold MarkingHaveSameStruct in H0; rewrite H0 in H7.
      (* ∃ n, (p, n) ∈ marking *)
      generalize (in_fst_split_in_pair p marking H7); intro; elim H; intros.
      (* Applies the completeness hypothesis. *)
      generalize (H3 p x H4 H20); intro.
      (* Applies check_inhib_complete, then the induction hypothesis. *)
      generalize (check_inhib_complete spn marking p t x H' H0 H20 H22); intro.
      (* Use b = true to rewrite the goal and apply the induction hypothesis. *)
      rewrite H23 in e0; injection e0; intro.
      rewrite <- H24 in IHo; rewrite andb_comm in IHo; rewrite andb_true_r in IHo.
      rewrite <- H24; rewrite andb_comm; rewrite andb_true_r.
      apply IHo with (neighbours_of_t := neighbours_of_t).
      + assumption.
      + assumption.
      + assumption.
      + unfold incl; intros.
        unfold incl in H2.
        apply in_cons with (a := p) in H25.
        apply (H2 a H25).
      + intros; apply in_cons with (a := p) in H25.
        apply (H3 p0 n H25 H26).
    (* Deduces hypotheses necessary to apply check_inhib_complete. *)
    - assert (In p (p :: tail)) by apply in_eq.
      generalize (H2 p H4); intro.
      (* p ∈ (flatten_neighbours neighbours_of_t) *)
      assert (In p (flatten_neighbours neighbours_of_t))
        by (unfold flatten_neighbours;
            do 2 (apply in_or_app; right);
            apply in_or_app; left; assumption).
      (* p ∈ (flatten_neighbours neighbours_of_t) ⇒ p ∈ (flatten spn.(lneighbours)) *)
      generalize (in_neigh_in_flatten spn t neighbours_of_t p H H1 H6); intro.
      assert (H' := H); unfold IsWellDefinedSpn in H; decompose [and] H; clear H; intros.
      unfold NoUnknownPlaceInNeighbours in H14; unfold incl in H14; apply (H14 p) in H7.
      unfold NoUnmarkedPlace in H21; rewrite H21 in H7.
      unfold MarkingHaveSameStruct in H0; rewrite H0 in H7.
      (* ∃ n, (p, n) ∈ marking *)
      generalize (in_fst_split_in_pair p marking H7); intro; elim H; intros.
      (* Applies the completeness hypothesis. *)
      generalize (H3 p x H4 H20); intro.
      (* Applies check_inhib_complete *)
      generalize (check_inhib_complete spn marking p t x H' H0 H20 H22); intro.
      (* Then, shows a contradiction. *)
      rewrite e0 in H23; inversion H23.
  Qed.
  
  (** Wrapper around [map_check_inhib_aux]. *)
  
  Definition map_check_inhib
             (spn : Spn)
             (marking : list (Place * nat))
             (inhib_places : list Place)
             (t : Trans) : option bool :=
    map_check_inhib_aux spn marking inhib_places t true.

  Functional Scheme map_check_inhib_ind := Induction for map_check_inhib Sort Prop.
  
  (** Correctness proof for map_check_inhib. *)

  Lemma map_check_inhib_correct :
    forall (spn : Spn)
           (marking : list (Place * nat))
           (t : Trans)
           (neighbours_of_t : Neighbours),
      IsWellDefinedSpn spn ->
      MarkingHaveSameStruct spn.(initial_marking) marking ->
      In (t, neighbours_of_t) spn.(lneighbours) ->
      map_check_inhib spn marking (inhib_pl neighbours_of_t) t = Some true ->
      forall (p : Place) (n : nat),
        In (p, n) marking -> (n < (inhib spn t p) \/ (inhib spn t p) = 0).
  Proof.
    intros spn marking t neighbours_of_t.
    functional induction (map_check_inhib spn marking (inhib_pl neighbours_of_t) t)
               using map_check_inhib_ind;
      intros.
    assert (incl (inhib_pl neighbours_of_t) (inhib_pl neighbours_of_t)) by (apply incl_refl).
    (* Proof in two stages. *)
    assert (H' := classic (In p (inhib_pl neighbours_of_t))).
    elim H'; intro.
    (* First stage, p ∈ inhib_places, then we apply map_check_inhib_aux_correct. *)
    - generalize (map_check_inhib_aux_correct
                    spn marking (inhib_pl neighbours_of_t) t true neighbours_of_t
                    H H0 H1 H4 H2); intro. 
      apply (H6 p n H5 H3).
    (* Second stage, p ∉ inhib_places, then (inhib spn t p) = 0 *)
    - unfold IsWellDefinedSpn in H; decompose [and] H; clear H; intros.
      unfold AreWellDefinedInhibEdges in H17.
      generalize (H17 t neighbours_of_t p H1); intro.
      elim H; clear H; intros.
      generalize (H18 H5); intro; right; assumption.
  Qed.

  (** Correctness proof for map_check_inhib. *)

  Lemma map_check_inhib_complete :
    forall (spn : Spn)
           (marking : list (Place * nat))
           (t : Trans)
           (neighbours_of_t : Neighbours),
      IsWellDefinedSpn spn ->
      MarkingHaveSameStruct spn.(initial_marking) marking ->
      In (t, neighbours_of_t) spn.(lneighbours) ->
      (forall (p : Place) (n : nat), In (p, n) marking -> (n < (inhib spn t p) \/ (inhib spn t p) = 0)) ->
      map_check_inhib spn marking (inhib_pl neighbours_of_t) t = Some true.
  Proof.
    intros spn marking t neighbours_of_t.
    unfold map_check_inhib; intros.
    assert (incl (inhib_pl neighbours_of_t) (inhib_pl neighbours_of_t)) by apply incl_refl.
    (* Apply map_check_inhib_aux_complete. *)
    apply map_check_inhib_aux_complete with (neighbours_of_t := neighbours_of_t).
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - intros; apply (H2 p n H5).
  Qed.
  
End Edges.


