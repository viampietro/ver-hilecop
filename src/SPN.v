Require Export Arith List Lists.ListDec Bool Bool.Sumbool Bool.Bool FunInd.
Require Export Sorting.Sorting.

Export ListNotations.
Export Permutation.

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
  NoIsolatedPlace spn /\
  NoUnknownPlaceInNeighbours spn /\
  NoUnknownTransInLNeighbours spn /\
  NoIsolatedTrans spn /\
  AreWellDefinedPreEdges spn /\
  AreWellDefinedTestEdges spn /\
  AreWellDefinedInhibEdges spn /\
  NoUnmarkedPlace spn.

(** ** Spn state. *)

(** Defines the state of an Spn. *)

Structure SpnState := mk_SpnState { fired : list Trans; marking : list (Place * nat) }.

(** Checks that state s is well-defined compared to spn's structure. *)

Definition IsWellDefinedSpnState (spn : Spn) (s : SpnState) :=
  MarkingHaveSameStruct spn.(initial_marking) s.(marking) /\
  incl s.(fired) spn.(transs) /\
  NoDup s.(fired).

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

  Functional Scheme replace_occ_ind := Induction for replace_occ Sort Prop.
  
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

  Functional Scheme modify_m_ind := Induction for modify_m Sort Prop.
  
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

  Functional Scheme get_neighbours_ind := Induction for get_neighbours Sort Prop.
  
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

  (** Wrapper around [map_check_pre_aux]. *)
  
  Definition map_check_pre
             (spn : Spn)
             (marking : list (Place * nat))
             (pre_places : list Place)
             (t : Trans) : option bool :=
    map_check_pre_aux spn marking pre_places t true.

  Functional Scheme map_check_pre_ind := Induction for map_check_pre Sort Prop.
  
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

  (** Wrapper around [map_check_test_aux]. *)
  
  Definition map_check_test
             (spn : Spn)
             (marking : list (Place * nat))
             (test_places : list Place)
             (t : Trans) : option bool :=
    map_check_test_aux spn marking test_places t true.

  Functional Scheme map_check_test_ind := Induction for map_check_test Sort Prop.
  
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
  
  (** Wrapper around [map_check_inhib_aux]. *)
  
  Definition map_check_inhib
             (spn : Spn)
             (marking : list (Place * nat))
             (inhib_places : list Place)
             (t : Trans) : option bool :=
    map_check_inhib_aux spn marking inhib_places t true.

  Functional Scheme map_check_inhib_ind := Induction for map_check_inhib Sort Prop.
  
End Edges.


