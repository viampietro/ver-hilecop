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

Definition place_type := nat.

(** A transition is identified by a unique index. *)

Definition trans_type := nat.

(** Set of natural numbers that are strictly over zero. *)
(** The second member, posi, must be a lemma of the form [n > 0]. *)

Structure nat_star : Set := mk_nat_star { int : nat ; posi : int > 0 }.

(** There are 4 kinds of edges : pre, post, inhib, test 
    along with "some" positive weight (default is 1 usually). *)

(** A given edge, either reaching in or coming out of a place,
    has some weight over 0 or no weight at all, meaning it
    doesn't exist (which is why weight_type returns a option nat_star 
    that can take the None value). *)

Definition weight_type := trans_type -> place_type -> option nat_star.

(** The marking in a Petri net is represented as
    a list of couples (index, nboftokens), where index is
    the index of a place in the Petri net, and nboftokens
    is the number of tokens currently assoicated to the place. *)

Definition marking_type := list (place_type * nat).

(** Defines a structure containing multiple list of places,
    each one of them corresponding to the pre, test, inhib and post neighbour places
    which will be associated with a transition t (see the lneighbours
    attribute in the SPN Structure). *)

Structure neighbours_type : Set := mk_neighbours {
                                       pre_pl : list place_type;
                                       test_pl : list place_type;
                                       inhib_pl : list place_type;
                                       post_pl : list place_type
                                     }.

(** Returns the concatenation of all list of places contained in neighb. 
    
    Useful for [NoIsolatedPlace] spn's property. *)

Definition flatten_neighbours (neighb : neighbours_type) : list place_type :=
  neighb.(pre_pl) ++ neighb.(test_pl) ++ neighb.(inhib_pl) ++ neighb.(post_pl).

(** Returns the list of all places referenced in lneighbours.
    A same place can possibly appear multiple times in the
    resulting list.            
    
    Useful for NoIsolatedPlace spn's property. *)

Fixpoint flatten_lneighbours (lneighbours : list (trans_type * neighbours_type)) :
  list place_type :=
  match lneighbours with
  | (t, neighb) :: tail => (flatten_neighbours neighb) ++ (flatten_lneighbours tail)
  | [] => []
  end.

Functional Scheme flatten_lneighbours_ind := Induction for flatten_lneighbours Sort Prop.

(** Formal specification : flatten_lneighbours. *)

Inductive FlattenLneighbours :
  list (trans_type * neighbours_type) -> list place_type -> Prop :=
| FlattenLneighbours_nil :
    FlattenLneighbours [] []
| FlattenLneighbours_cons :
    forall (lneighbours : list (trans_type * neighbours_type))
           (places : list place_type)
           (t : trans_type)
           (neighbours : neighbours_type),
      FlattenLneighbours lneighbours places ->
      FlattenLneighbours ((t, neighbours) :: lneighbours)
                         ((flatten_neighbours neighbours) ++ places).

(** Correctness proof : flatten_lneighbours *)

Theorem flatten_lneighbours_correct :
  forall (lneighbours : list (trans_type * neighbours_type))
         (places : list place_type),
    flatten_lneighbours lneighbours = places -> FlattenLneighbours lneighbours places.
Proof.
  intros lneighbours.
  functional induction (flatten_lneighbours lneighbours)
             using flatten_lneighbours_ind;
  intros.
  (* Base case : lneighbours = []. *)
  - rewrite <- H; apply FlattenLneighbours_nil.
  (* General case. *)
  - rewrite <- H; apply FlattenLneighbours_cons; apply IHl; auto.
Qed.

(** Completeness proof : flatten_lneighbours *)

Theorem flatten_lneighbours_compl :
  forall (lneighbours : list (trans_type * neighbours_type))
         (places : list place_type),
    FlattenLneighbours lneighbours places -> flatten_lneighbours lneighbours = places.
Proof.
  intros.
  induction H.
  (* Case FlattenLneighbours_nil. *)
  - simpl; auto.
  (* Case FlattenLneighbours_cons. *)
  - simpl; rewrite IHFlattenLneighbours; auto.
Qed.

(** ** Structure of Synchronous Petri Nets. *)

(*==================================================================*)
(*============== STRUCTURE OF SYNCHRONOUS PETRI NETS ===============*)
(*==================================================================*)

Structure SPN : Set :=
  mk_SPN {
      
      places : list place_type;
      transs : list trans_type;
      pre : weight_type;
      post : weight_type;
      test : weight_type;
      inhib : weight_type;
      marking : marking_type;

      (* Each list of transitions contained in priority_groups is 
       * a priority-ordered list of transitions.
       * Defines priority relation between transitions,
       * necessary to obtain a deterministic Petri net.*)
      priority_groups : list (list trans_type);

      (* Contains the list of pre, test, inhib and post places 
       * associated with each transition of the SPN. *)
      lneighbours : list (trans_type * neighbours_type);
      
    }.

(** ** Setter for SPN structure. *)

Definition set_m (spn : SPN) (newm : marking_type) : SPN :=
  {| places := spn.(places);
     transs := spn.(transs);
     pre := spn.(pre);
     post := spn.(post);
     test := spn.(test);
     inhib := spn.(inhib);
     marking := newm;
     priority_groups := spn.(priority_groups);
     lneighbours := spn.(lneighbours)
  |}.

(** ------------------------------------------------------- *)
(** ------------------------------------------------------- *)

(** ** Properties on the SPN structure. *)

(*==============================================*)
(*============ PROPERTIES ON SPN ===============*)
(*==============================================*)

(** *** SPN helpers predicates *)

Definition MarkingHaveSameStruct
           (m1 : marking_type)
           (m2 : marking_type) := fst (split m1) = fst (split m2).

Definition PriorityGroupsAreRefInLneighbours
           (priority_groups : list (list trans_type))
           (lneighbours : list (trans_type * neighbours_type)) :=
  (forall pgroup : list trans_type,
      In pgroup priority_groups ->
      (forall t : trans_type, In t pgroup -> In t (fst (split lneighbours)))).

(** *** Properties on places and transitions *)

Definition NoDupPlaces (spn : SPN) := NoDup spn.(places).  
Definition NoDupTranss (spn : SPN) := NoDup spn.(transs).

(** *** Properties on priority_groups *)

(** For all transition t, t is in [spn.(transs)] iff 
    there exists a group in [spn.(priority_groups)] containing t. *)

Definition NoUnknownInPriorityGroups (spn : SPN) :=
  Permutation spn.(transs) (concat spn.(priority_groups)).

(** For all transition t in one of the group of priority_groups, 
    t is contained in only one group of priority_groups. *)

Definition NoIntersectInPriorityGroups (spn : SPN) :=
  NoDup (concat spn.(priority_groups)).

(** *** Properties on lneighbours *)

Definition NoDupLneighbours (spn : SPN) := NoDup spn.(lneighbours).

(** For all place p, p is in places iff p is in the neighbourhood 
    of at least one transition. *)

Definition NoIsolatedPlace (spn : SPN) := 
  incl spn.(places) (flatten_lneighbours spn.(lneighbours)).

(** All places in [flatten_lneighbours spn.(lneighbours)] are in [spn.(places)]. *)

Definition NoUnknownPlaceInNeighbours (spn : SPN) :=
  incl (flatten_lneighbours spn.(lneighbours)) spn.(places).

(** For all transition t, t is in spn.transs iff t is referenced in [spn.(lneighbours)]. *)

Definition NoUnknownTransInLNeighbours (spn : SPN) :=
  spn.(transs) = fst (split spn.(lneighbours)).

(** Forall neighbours_of_t in spn.(lneighbours), there exists one list of places that is not empty.
    i.e. A transition has at least one neighbour place. *)

Definition NoIsolatedTrans (spn : SPN) :=
  forall (t : trans_type) (neighbours_of_t : neighbours_type),
    In (t, neighbours_of_t) spn.(lneighbours) ->
    (flatten_neighbours neighbours_of_t) <> [].

(** *** Properties on marking *)

(** For all place p, p is in spn.(places) iff p is referenced in marking. *)
Definition NoUnmarkedPlace (spn : SPN)  :=
  spn.(places) = (fst (split spn.(marking))).

(** *** Predicate defining if a SPN is well-structured. *)

Definition IsWellStructuredSpn (spn : SPN) :=
  NoDupPlaces spn /\
  NoDupTranss spn /\
  NoUnknownInPriorityGroups spn /\
  NoIntersectInPriorityGroups spn /\
  NoDupLneighbours spn /\
  NoIsolatedPlace spn /\
  NoUnknownPlaceInNeighbours spn /\
  NoUnknownTransInLNeighbours spn /\
  NoIsolatedTrans spn /\
  NoUnmarkedPlace spn.

(*===============================================*)
(*===== EQUALITY DECIDABILITY FOR SPN TYPES =====*)
(*===============================================*)

(** *** Equality decidability for neighbours_type *)
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
   *            associated with the place [p]
   *            in marking [marking].
   *            Returns None if [p] doesn't belong
   *            to the marking.
   *)
  Fixpoint get_m (marking : marking_type) (p : place_type) : option nat :=
    match marking with
    | (place, nboftokens) :: tail => if p =? place then
                                       Some nboftokens
                                     else get_m tail p
    (* Exception : p is not in marking. *)
    | [] => None
    end.
  
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
  
  (** Function : Given a marking m, add/remove nboftokens tokens (if not None)
                 inside place p and returns the new marking.
   
      Param nboftokens : number of tokens to add or sub for place p.
   
      Param op : addition or substraction operator. *)
  
  Definition modify_m
             (marking : marking_type)
             (p : place_type)
             (op : nat -> nat -> nat)
             (nboftokens : option nat_star) : option marking_type :=
    match nboftokens with
    | None => Some marking
    | Some (mk_nat_star n' _) =>
      let opt_n := get_m marking p in
      match opt_n with
      (* The couple (i, n) to remove must be unique. *)
      | Some n =>
        Some (replace_occ prodnat_eq_dec (p, n) (p, (op n n')) marking)
      (* If couple with first member i doesn't exist
       * in m, then returns None (it's an exception). *)
      | None => None 
      end
    end.
  
End Marking.

(*====================================================*)
(*=============== NEIGHBOURS SECTION  ================*)
(*====================================================*)

Section Neighbours.

  (** Function : Returns the element of type neighbours_type
                 associated with transition t in the list lneighbours.
               
                 Returns None if transition t is not referenced
                 in lneighbours. *)
  
  Fixpoint get_neighbours
           (lneighbours : list (trans_type * neighbours_type))
           (t : trans_type) {struct lneighbours} : option neighbours_type :=
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

  (** Function : Returns [Some true] if M(p) >= pre(p, t), [Some false] otherwise. 
                 
                 Raises an error (i.e. None) if [get_m] fail.
   *)
  
  Definition check_pre
             (pre : weight_type)
             (marking : marking_type)
             (p : place_type)
             (t : trans_type) : option bool :=
    match pre t p with
    | None => Some true
    | Some (mk_nat_star weight _) =>
      match get_m marking p with
      | Some nboftokens => Some (weight <=? nboftokens)
      | None => None
      end
    end.
  
  (** Function : Returns [Some true] if ∀ p ∈ [pre_places], M(p) >= pre(p, t).
                 
                 Raises an error if [get_m] fails. *)
  
  Fixpoint map_check_pre_aux
           (pre : weight_type)
           (marking : marking_type)
           (pre_places : list place_type)
           (t : trans_type)
           (check_result : bool) {struct pre_places} : option bool :=
    match pre_places with
    | p :: tail =>
      match check_pre pre marking p t with
      | None => None
      | Some b =>
        map_check_pre_aux pre marking tail t (b && check_result)
      end 
    | [] => Some check_result
    end.  

  (** Function : Wrapper around [map_check_pre_aux]. *)
  
  Definition map_check_pre
             (pre : weight_type)
             (marking : marking_type)
             (pre_places : list place_type)
             (t : trans_type) : option bool :=
    map_check_pre_aux pre marking pre_places t true.

  (** Function : Returns [Some true] if M(p) >= test(p, t), [Some false] otherwise. 
                 
                 Raises an error (i.e. None) if [get_m] fail.
   *)
  
  Definition check_test
             (test : weight_type)
             (marking : marking_type)
             (p : place_type)
             (t : trans_type) : option bool :=
    match test t p with
    | None => Some true
    | Some (mk_nat_star weight _) =>
      match get_m marking p with
      | Some nboftokens => Some (weight <=? nboftokens)
      | None => None
      end
    end.
  
  (** Function : Returns [Some true] if ∀ p ∈ [test_places], M(p) >= test(p, t).
                 
                 Raises an error if [get_m] fails. *)
  
  Fixpoint map_check_test_aux
           (test : weight_type)
           (marking : marking_type)
           (test_places : list place_type)
           (t : trans_type)
           (check_result : bool) {struct test_places} : option bool :=
    match test_places with
    | p :: tail =>
      match check_test test marking p t with
      | None => None
      | Some b =>
        map_check_test_aux test marking tail t (b && check_result)
      end 
    | [] => Some check_result
    end.  

  (** Function : Wrapper around [map_check_test_aux]. *)
  
  Definition map_check_test
             (test : weight_type)
             (marking : marking_type)
             (test_places : list place_type)
             (t : trans_type) : option bool :=
    map_check_test_aux test marking test_places t true.

  (** Function : Returns [Some true] if M(p) >= inhib(p, t), [Some false] otherwise. 
                 
                 Raises an error (i.e. None) if [get_m] fail.
   *)
  
  Definition check_inhib
             (inhib : weight_type)
             (marking : marking_type)
             (p : place_type)
             (t : trans_type) : option bool :=
    match inhib t p with
    | None => Some true
    | Some (mk_nat_star weight _) =>
      match get_m marking p with
      | Some nboftokens => Some (nboftokens <? weight)
      | None => None
      end
    end.
  
  (** Function : Returns [Some true] if ∀ p ∈ [inhib_places], M(p) >= inhib(p, t).
                 
                 Raises an error if [get_m] fails. *)
  
  Fixpoint map_check_inhib_aux
           (inhib : weight_type)
           (marking : marking_type)
           (inhib_places : list place_type)
           (t : trans_type)
           (check_result : bool) {struct inhib_places} : option bool :=
    match inhib_places with
    | p :: tail =>
      match check_inhib inhib marking p t with
      | None => None
      | Some b =>
        map_check_inhib_aux inhib marking tail t (b && check_result)
      end 
    | [] => Some check_result
    end.  

  (** Function : Wrapper around [map_check_inhib_aux]. *)
  
  Definition map_check_inhib
             (inhib : weight_type)
             (marking : marking_type)
             (inhib_places : list place_type)
             (t : trans_type) : option bool :=
    map_check_inhib_aux inhib marking inhib_places t true.

  
End Edges.

