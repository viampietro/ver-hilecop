Require Export Arith Omega List Bool FunInd Coq.Lists.ListDec.
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
  | [] => None
  | (i, nboftokens) :: tail => if i =? index then
                                 Some nboftokens
                               else get_m tail index
  end.

(*******************************************************************)
(**********************  Priority relation *************************)
(* to DETERMINE the Petri net (along with the imperative semantic) *)
(*******************************************************************)

(* Inductive or Definition  ?? *) 
Inductive prior_type : Set := mk_prior { Lol : list (list trans_type); }.

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
  | [] => None 
  | neighbours :: tail => if (index neighbours) =? idx then
                            Some neighbours
                          else get_neighbours tail idx
  end.

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

Functional Scheme beq_places_ind :=
  Induction for beq_places Sort Prop.

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

Functional Scheme beq_transs_ind :=
  Induction for beq_transs Sort Prop.

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
       * with each transition of the SPN.
       *)
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
   * Function : Replaces every occurence of occ
   *            in list l by repl.
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
    | [] => l
    | x :: tl => if eq_dec x occ then
                   repl :: (replace_occ eq_dec occ repl tl)
                 else x :: (replace_occ eq_dec occ repl tl)
    end.
  
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
             (nboftokens : option nat_star)     
             (op : nat -> nat -> nat) : marking_type :=
    match p with
    | (pl i) => match get_m m i with
                (* if no place of index i, returns the current marking *)
                | None => m
                (* else removes the old couple and adds the new *)
                | Some n => match nboftokens with
                            | None => m
                            | Some (mk_nat_star n' _) =>
                              (* The couple (i, n) to remove must be unique. *)
                              (replace_occ prodnat_eq_dec (i, n) (i, (op n n')) m)
                            end
                end
    end.

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
    | [] => m
    | p :: tail => update_marking_pre t pre (modify_m m p (pre t p) Nat.sub) tail
    end.

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
    | [] => m
    | p :: tail => update_marking_post t post (modify_m m p (post t p) Nat.add) tail
    end.


  (****************************************************)
  (***          Update marking post and pre.        ***)
  (*** (only useful for asynchronous Petri nets...) ***)
  (****************************************************)

  (* Function : Updates the marking for all the places in
   *            the list places, resulting of the firing
   *            of transition t.
   *            Returns an updated marking application.
   *)
  Definition update_marking
             (places : list place_type) 
             (t : trans_type)
             (pre post : weight_type)
             (m : marking_type) : marking_type :=
    update_marking_post t post (update_marking_pre t pre m places) places.

End Marking.

(*==================================================*)
(*== CHECKS NEIGHBOUR PLACES WITH ADJACENT EDGES. ==*)
(*==================================================*)

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
    | nil => true
    | (pl i) :: tail => match pre_or_test_arcs_t (pl i) with
                        (* If there is no pre or test edge between (pl i) and t. *)
                        | None => check_pre_or_test pre_or_test_arcs_t m tail
                        (* Else some pre or test edge exists. *)
                        | Some (mk_nat_star edge_weight _) =>
                          match (get_m m i) with
                          (* If there is no marking for place of index i
                           * then return false. *)
                          | None => false
                          | Some nboftokens => (edge_weight <=? nboftokens)
                                                 && (check_pre_or_test pre_or_test_arcs_t m tail)
                          end
                        end
    end.

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
    | nil => true
    | (pl i) :: tail => match inhib_arcs_t (pl i) with
                        (* If there is inhib edge between (pl i) and t. *)
                        | None => (check_inhib inhib_arcs_t m tail)
                        (* Else some inhib edge exists. *)
                        | Some (mk_nat_star edge_weight _) =>
                          match (get_m m i) with
                          (* If there is no marking for place of index i
                           * then return false. *)
                          | None => false
                          | Some nboftokens => (nboftokens <? edge_weight)
                                                 && (check_inhib inhib_arcs_t m tail)
                          end
                        end
    end.

  (*****************************************************)
  (*****************************************************)

  (* 
   * Function : Returns true if a certain transition t
   *            is sensitized according to a marking m_steady
   *            (or m_decreasing) on the neighbour places of t and
   *            to some weight functions pre_arcs_t, test_arcs_t
   *            and inhib_arcs_t.
   *)
  Definition check_all_edges
             (neighbours_t : neighbours_type)
             (pre_arcs_t : place_type -> option nat_star)
             (test_arcs_t : place_type -> option nat_star)
             (inhib_arcs_t : place_type -> option nat_star)
             (m_steady m_decreasing : marking_type) : bool :=
    (check_pre_or_test pre_arcs_t m_decreasing (pre_pl neighbours_t))
    && (check_pre_or_test test_arcs_t m_steady (test_pl neighbours_t))
    && (check_inhib inhib_arcs_t m_steady (inhib_pl neighbours_t)).

End Edges.

(*==============================================================*)
(*================= FIRING ALGORITHM for SPN ===================*)
(*==============================================================*)

Section FireSpn.

  (* 
   * There are 2 parallel calculus in spn_class_fire_pre_aux : 
   * 1. pumping tokens to get "m_decreasing" (fired pre)
   * 2. returning subclass of transitions (fired_pre_class)
   *
   * and 2 markings are recorded : 
   * 1. the initial one to check with inhib and test arcs
   * 2. a floating (decreasing) intermediate marking to check classic arcs
   *)
  
  (* Function : Given 1 ordered class of transitions 
   *            in structural conflict (a list class_transs), 
   *            returns 1 list of transitions "fired_pre_class" 
   *            and marking "m_decreasing" accordingly ...
   *
   *            Returns a couple (list of transitions, marking)
   *            For each sensitized transition of the list,
   *            the marking of the pre-condition places are updated (the 
   *            transition is fired). "m_decreasing" is then the resulting marking.
   *)
  Fixpoint spn_class_fire_pre_aux
           (lneighbours : list neighbours_type)
           (pre test inhib : weight_type)  
           (m_steady : marking_type)
           (* "fired_pre_class" meant  to be empty at first *)
           (class_transs fired_pre_class : list trans_type)  
           (m_decreasing : marking_type) : (list trans_type) * marking_type :=
    match class_transs with
    | (tr i) :: tail =>
      match get_neighbours lneighbours i with
      (* If transition t have no neighbours, then continues. *)
      | None => (spn_class_fire_pre_aux lneighbours pre test inhib m_steady tail
                                        fired_pre_class m_decreasing)
      (* Else checks neighbours of t. *)
      | Some neighbours_t =>
        (* If t is sensitized. *)
        if (check_all_edges neighbours_t (pre (tr i)) (test (tr i)) (inhib (tr i))
                            m_steady m_decreasing) then
          (* Updates the marking for the pre places neighbours of t. *)
          let new_decreasing := (update_marking_pre (tr i) pre m_decreasing
                                                    (pre_pl neighbours_t)) in
          (spn_class_fire_pre_aux lneighbours pre test inhib m_steady tail
                                  (fired_pre_class ++ [(tr i)]) new_decreasing)
        (* Else no changes but inductive progress. *)
        else (spn_class_fire_pre_aux lneighbours pre test inhib m_steady tail
                                     fired_pre_class m_decreasing)
      end
    | []  => (fired_pre_class, m_decreasing)
    end.

  (*  
   * Function : Wrapper function around spn_class_fire_pre_aux.
   *)
  Definition spn_class_fire_pre
             (lneighbours : list neighbours_type)
             (pre test inhib : weight_type) 
             (m_steady : marking_type) 
             (class_transs : list trans_type)
             (m_decreasing : marking_type) : (list trans_type) * marking_type :=
    spn_class_fire_pre_aux lneighbours pre test inhib m_steady class_transs [] m_decreasing.

  (*
   * Function : Apply spn_class_fire_pre over ALL classes of transitions. 
   *            Begin with initial marking; End with half fired marking.  
   *            "classes_fired_pre" is empty at first 
   *)
  Fixpoint spn_fire_pre_aux
           (lneighbours : list neighbours_type)
           (pre test inhib : weight_type)
           (m_steady : marking_type)
           (classes classes_fired_pre : list (list trans_type))
           (m_decreasing : marking_type) : (list (list trans_type)) * marking_type :=
    match classes with
    | [] => (classes_fired_pre, m_decreasing)
    (* Loops over all classes of transitions (priority group) and
     * calls spn_class_fire_pre.
     *)
    | class :: classes_tail =>
      let (class_fired_pre, m_decreased_class) :=
          (spn_class_fire_pre lneighbours pre test inhib m_steady class m_decreasing) in
      (spn_fire_pre_aux lneighbours pre test inhib m_steady   
                        classes_tail
                        (class_fired_pre :: classes_fired_pre)
                        m_decreased_class)
    end.
 
  (*
   * Function : Update the marking by consuming
   *            the tokens in pre-condition places.            
   *)
  Definition spn_fire_pre
             (lneighbours : list neighbours_type)
             (pre test inhib : weight_type)
             (m_steady : marking_type)
             (classes_transs  : list (list trans_type)) :
    (list (list trans_type)) * marking_type :=
    spn_fire_pre_aux lneighbours pre test inhib m_steady classes_transs [] m_steady.


  (* 
   * Function : Given a marking "m_intermediate", resulting of the call
   *            of the function spn_fire_pre, and after
   *            that a given subclass of transs has been pre-fired
   *            (the "class_fired_pre" list of transitions),
   *            returns the marking increased by the post-condition edges.
   *)
  Fixpoint class_fire_post
           (lneighbours : list neighbours_type)
           (post : weight_type)
           (m_increasing : marking_type)
           (class_fired_pre : list trans_type) : marking_type :=
    match class_fired_pre with
    | []  => m_increasing
    | (tr i) :: tail  =>
      match get_neighbours lneighbours i with
      (* If transition (tr i) has no neighbours, then continues. *)
      | None => (class_fire_post lneighbours post m_increasing tail)
      (* Else updates the marking
       * for all neighbour post places of (tr i). *)
      | Some neighbours_t =>
        (class_fire_post lneighbours
                         post
                         (update_marking_post (tr i) post m_increasing (post_pl neighbours_t))
                         tail)
      end
    end.

  (*  
   * Function : Meant to begin with intermediate marking
   *            computed by "fire_pre", after half (pre arcs)
   *            firing of ALL the chosen transitions.
   *            Ends with the FINAL marking of the cycle !
   *)
  Fixpoint fire_post
           (lneighbours : list neighbours_type)
           (post : weight_type)
           (m_increasing : marking_type)
           (fired_pre_classes : list (list trans_type)) : marking_type :=
    match fired_pre_classes with
    | []  => m_increasing
    | class :: tail  =>
      let greater_m := (class_fire_post lneighbours post m_increasing class) in
      (fire_post lneighbours post greater_m tail)
    end.

  (*************************************************)
  (****************** SPN FIRE *********************)
  (*************************************************)

  (*
   * Function : Returns  "transitions fired (Lol)" + "final marking",
   *            composing spn_fire_post with spn_fire_pre
   *)
  Definition spn_fire
             (lneighbours : list neighbours_type)
             (pre test inhib post : weight_type)
             (m_steady : marking_type)
             (classes_transs : list (list trans_type)) :
    (list (list trans_type)) * marking_type :=
    let (sub_Lol, m_inter) := (spn_fire_pre lneighbours pre test inhib m_steady classes_transs) in
    (sub_Lol, (fire_post lneighbours post m_inter sub_Lol)).

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
    | (mk_SPN places transs pre post test inhib m (mk_prior Lol) lneighbours) =>
      let (sub_Lol, next_m) := (spn_fire lneighbours pre test inhib post m Lol) in
      (sub_Lol, (mk_SPN places transs pre post test inhib next_m (mk_prior Lol) lneighbours))
    end.

  (*******************************************)
  (******** ANIMATING DURING N CYCLES ********)
  (*******************************************)

  (* 
   * Function : Returns the list of (transitions_fired(i), marking(i))
   *            for each cycle i, from 0 to n, representing the evolution
   *            of the Petri net spn.
   *)
  Fixpoint spn_animate (spn : SPN) (n : nat) :
    list ((list (list trans_type)) * (list (nat * nat))) :=
    match n with
    | O => [ ([], []) ]
    | S n' => let (Lol_fired, next_spn) := (spn_cycle spn) in
              (Lol_fired, (marking next_spn)) :: (spn_animate next_spn n')
    end.
  
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
