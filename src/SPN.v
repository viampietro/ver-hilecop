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

(** There are 4 kinds of edges : pre, post, inhib, test 
    along with "some" positive weight (default is 1 usually). *)

(** A given edge, either reaching in or coming out of a place,
    has some weight over 0 or 0 if the edge doesn't exist *)

Definition weight_type := trans_type -> place_type -> nat.

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

  (** Formal specification for [get_m] *)
  
  Inductive GetM : marking_type -> place_type -> option nat -> Prop :=
  | GetM_hd :
      forall (marking : marking_type)
        (p : place_type)
        (n : nat),
        GetM ((p, n) :: marking) p (Some n)
  | GetM_cons :
      forall (marking : marking_type)
             (p p' : place_type)
             (n : nat)
             (opt_n : option nat),
        p' <> p ->
        GetM marking p opt_n ->
        GetM ((p', n) :: marking) p opt_n
  | GetM_err :
      forall (marking : marking_type)
        (p : place_type),
        ~In p (fst (split marking)) -> GetM marking p None.
  
  (** Returns the number of tokens associated with the place [p]
      in marking [marking].
      
       Returns None if [p] doesn't belong to the marking. *)
  
  Fixpoint get_m (marking : marking_type) (p : place_type) : option nat :=
    match marking with
    | (place, nboftokens) :: tail => if p =? place then
                                       Some nboftokens
                                     else get_m tail p
    (* Exception : p is not in marking. *)
    | [] => None
    end.

  Functional Scheme get_m_ind := Induction for get_m Sort Prop.

  (** Correctness proof for get_m and GetM *)
  
  Theorem get_m_correct :
    forall (marking : marking_type)
           (p : place_type)
           (opt_n : option nat),
      get_m marking p = opt_n -> GetM marking p opt_n.
  Proof.
    intros marking p; functional induction (get_m marking p) using get_m_ind; intros.
    - rewrite <- H; eapply GetM_err; auto.
    - apply beq_nat_true in e1; rewrite <- e1; rewrite <- H; apply GetM_hd.
    - apply GetM_cons; [apply beq_nat_false in e1; auto | apply IHo; rewrite H; reflexivity].      
  Qed.

  (** Completeness proof for get_m and GetM *)
  
  Theorem get_m_complete :
    forall (marking : marking_type)
           (p : place_type)
           (opt_n : option nat),
      GetM marking p opt_n -> get_m marking p = opt_n.
  Proof.
    intros; elim H; intros.
    - simpl; rewrite Nat.eqb_refl; reflexivity.
    - simpl; rewrite Nat.eqb_sym; apply Nat.eqb_neq in H0; rewrite H0; assumption.
    - induction marking1.
      + simpl; reflexivity.
      + dependent induction a; intros; simpl.
        rewrite fst_split_cons_app in H0.
        simpl in H0.
        apply not_or_and in H0.
        elim H0; intros.
        apply Nat.neq_sym in H1.
        apply Nat.eqb_neq in H1.
        rewrite H1.
        apply IHmarking1; assumption.
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
  
  (** Formal specification : replace_occ ***)
  
  Inductive ReplaceOcc
            {A : Type}
            (eq_dec : forall x y : A, {x = y} + {x <> y})
            (occ : A)
            (repl : A) :
    list A -> list A -> Prop :=
  | ReplaceOcc_nil :
      ReplaceOcc eq_dec occ repl [] []
  | ReplaceOcc_if :
      forall (l l' : list A),
        ReplaceOcc eq_dec occ repl l l' ->
        ReplaceOcc eq_dec occ repl (occ :: l) (repl :: l')
  | ReplaceOcc_else :
      forall (l l' : list A) (x : A),
        x <> occ ->
        ReplaceOcc eq_dec occ repl l l' ->
        ReplaceOcc eq_dec occ repl (x :: l) (x :: l').

  (** Correctness proof : replace_occ ***)
  
  Theorem replace_occ_correct {A : Type} :
    forall (eq_dec : forall x y : A, {x = y} + {x <> y}) (occ repl : A) (l l' : list A),
      replace_occ eq_dec occ repl l = l' -> ReplaceOcc eq_dec occ repl l l'.
  Proof.
    do 4 intro; functional induction (replace_occ eq_dec occ repl l)
                           using replace_occ_ind; intros.
    (* Case l = nil *)
    - rewrite <- H; apply ReplaceOcc_nil.
    (* Case occ is head *)
    - rewrite <- H; apply ReplaceOcc_if; apply IHl0; auto.
    (* Case occ is not head *)
    - rewrite <- H; apply ReplaceOcc_else; [auto |apply IHl0; auto].
  Qed.

  (** Completeness proof : replace_occ ***)
  
  Theorem replace_occ_compl {A : Type} :
    forall (eq_dec : forall x y : A, {x = y} + {x <> y}) (occ repl : A) (l l' : list A),
      ReplaceOcc eq_dec occ repl l l' -> replace_occ eq_dec occ repl l = l'.
  Proof.
    intros; induction H.
    (* Case ReplaceOcc_nil *)
    - simpl; auto.
    (* Case ReplaceOcc_if *)
    - simpl. elim eq_dec; [intro; rewrite IHReplaceOcc; auto | intro; contradiction].
    (* Case ReplaceOcc_else *)
    - simpl. elim eq_dec; [intro; contradiction | intro; rewrite IHReplaceOcc; auto].
  Qed.
  
  (** Function : Given a marking m, add/remove nboftokens tokens (if not None)
                 inside place p and returns the new marking.
   
      Param nboftokens : number of tokens to add or sub for place p.
   
      Param op : addition or substraction operator. *)
  
  Definition modify_m
             (marking : marking_type)
             (p : place_type)
             (op : nat -> nat -> nat)
             (nboftokens : nat) : option marking_type :=
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

  (** Formal specification for check_pre *)
  
  Inductive CheckPre
            (spn : SPN)
            (marking : marking_type)
            (p : place_type)
            (t : trans_type) :
    option bool -> Prop := 
  | CheckPre_cons :
      forall (tokens : nat),
        GetM marking p (Some tokens) ->
        CheckPre spn marking p t (Some ((pre spn t p) <=? tokens))
  | CheckPre_err :
      GetM marking p None ->
      CheckPre spn marking p t None.
  
  (** Returns [Some true] if M(p) >= pre(p, t), [Some false] otherwise. 
                 
      Raises an error (i.e. None) if [get_m] fail. *)
  
  Definition check_pre
             (spn : SPN)
             (marking : marking_type)
             (p : place_type)
             (t : trans_type) : option bool :=
    match get_m marking p with
    | Some nboftokens => Some ((pre spn t p) <=? nboftokens)
    | None => None
    end.

  Functional Scheme check_pre_ind := Induction for check_pre Sort Prop.
  
  (** Soundness proof for check_pre and CheckPre. *)
  
  Theorem check_pre_correct :
    forall (spn : SPN)
      (marking : marking_type)
      (p : place_type)
      (t : trans_type)
      (opt_b : option bool),
      check_pre spn marking p t = opt_b -> CheckPre spn marking p t opt_b.
  Proof.
    intros spn marking p t;
      functional induction (check_pre spn marking p t) using check_pre_ind;
      intros.
    - rewrite <- H;
        apply CheckPre_cons;
        apply get_m_correct; assumption.
    - rewrite <- H;
        apply CheckPre_err;
        apply get_m_correct; assumption.
  Qed.

  (** Completeness proof for check_pre and CheckPre. *)
  
  Theorem check_pre_complete :
    forall (spn : SPN)
      (marking : marking_type)
      (p : place_type)
      (t : trans_type)
      (opt_b : option bool),
      CheckPre spn marking p t opt_b -> check_pre spn marking p t = opt_b.
  Proof.
    intros; elim H; intros.
    - apply get_m_complete in H0.
      unfold check_pre; rewrite H0; reflexivity.
    - apply get_m_complete in H0.
      unfold check_pre; rewrite H0; reflexivity.
  Qed.

   (** Formal specification for map_check_pre. *)

  Inductive MapCheckPreAux
            (spn : SPN)
            (marking : marking_type) :
    list place_type -> trans_type -> bool -> option bool -> Prop :=
  | MapCheckPreAux_nil :
      forall (t : trans_type)
        (check_result : bool),
        MapCheckPreAux spn marking [] t check_result (Some check_result)
  | MapCheckPreAux_cons :
      forall (pre_places : list place_type)
        (t : trans_type)
        (p : place_type)
        (b check_result : bool)
        (opt_b : option bool),
        CheckPre spn marking p t (Some b) ->
        MapCheckPreAux spn marking pre_places t (b && check_result) opt_b ->
        MapCheckPreAux spn marking (p :: pre_places) t check_result opt_b
  | MapCheckPreAux_err :
      forall (pre_places : list place_type)
        (t : trans_type)
        (p : place_type)
        (check_result : bool),
        CheckPre spn marking p t None ->
        MapCheckPreAux spn marking (p :: pre_places) t check_result None.
  
  (** Function : Returns [Some true] if ∀ p ∈ [pre_places], M(p) >= pre(p, t).
                 
                 Raises an error if [get_m] fails. *)
  
  Fixpoint map_check_pre_aux
           (spn : SPN)
           (marking : marking_type)
           (pre_places : list place_type)
           (t : trans_type)
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

  (** Soundness proof map_check_pre_aux and MapCheckPreAux. *)
  
  Theorem map_check_pre_aux_correct :
    forall (spn : SPN)
      (marking : marking_type)
      (pre_places : list place_type)
      (t : trans_type)
      (check_result : bool)
      (opt_b : option bool),
      map_check_pre_aux spn marking pre_places t check_result = opt_b ->
      MapCheckPreAux spn marking pre_places t check_result opt_b.
  Proof.
    intros spn marking pre_places t check_result;
      functional induction (map_check_pre_aux spn marking pre_places t check_result)
                 using map_check_pre_aux_ind;
      intros.
    - rewrite <- H; apply MapCheckPreAux_nil.
    - apply MapCheckPreAux_cons with (b := b); [apply check_pre_correct; assumption |
                                                apply IHo; assumption].
    - rewrite <- H; apply MapCheckPreAux_err; apply check_pre_correct; assumption.
  Qed.

  (** Completeness proof map_check_pre_aux and MapCheckPreAux. *)

  Theorem map_check_pre_aux_complete :
    forall (spn : SPN)
      (marking : marking_type)
      (pre_places : list place_type)
      (t : trans_type)
      (check_result : bool)
      (opt_b : option bool),
      MapCheckPreAux spn marking pre_places t check_result opt_b ->
      map_check_pre_aux spn marking pre_places t check_result = opt_b.
  Proof.
    intros; elim H; intros.
    - simpl; reflexivity.
    - simpl; apply check_pre_complete in H0; rewrite H0; assumption.
    - simpl; apply check_pre_complete in H0; rewrite H0; reflexivity.
  Qed.
  
  (** Wrapper around [map_check_pre_aux]. *)
  
  Definition map_check_pre
             (spn : SPN)
             (marking : marking_type)
             (pre_places : list place_type)
             (t : trans_type) : option bool :=
    map_check_pre_aux spn marking pre_places t true.

  (** Formal specification for map_check_pre *)
  Inductive MapCheckPre
            (spn : SPN)
            (marking : marking_type)
            (pre_places : list place_type)
            (t : trans_type) :
    option bool -> Prop := 
  | MapCheckPre_cons :
      forall opt_b : option bool,
        MapCheckPreAux spn marking pre_places t  true opt_b ->
        MapCheckPre spn marking pre_places t opt_b.
  
  (** Soundness proof for map_check_pre and MapCheckPre. *)
  
  Theorem map_check_pre_correct :
    forall (spn : SPN)
      (marking : marking_type)
      (pre_places : list place_type)
      (t : trans_type)
      (opt_b : option bool),
      map_check_pre spn marking pre_places t = opt_b ->
      MapCheckPre spn marking pre_places t opt_b.
  Proof.
    intros spn marking pre_places t; unfold map_check_pre; intros.
    apply MapCheckPre_cons; apply map_check_pre_aux_correct; assumption.
  Qed.

  (** Completeness proof for map_check_pre and MapCheckPre. *)

  Theorem map_check_pre_complete :
    forall (spn : SPN)
      (marking : marking_type)
      (pre_places : list place_type)
      (t : trans_type)
      (opt_b : option bool),
      MapCheckPre spn marking pre_places t opt_b ->
      map_check_pre spn marking pre_places t = opt_b.
  Proof.
    intros; elim H; intros.
    unfold map_check_pre; apply map_check_pre_aux_complete; assumption.
  Qed.

  (** Formal specification for check_test *)
  
  Inductive CheckTest
            (spn : SPN)
            (marking : marking_type)
            (p : place_type)
            (t : trans_type) :
    option bool -> Prop := 
  | CheckTest_cons :
      forall (tokens : nat),
        GetM marking p (Some tokens) ->
        CheckTest spn marking p t (Some ((test spn t p) <=? tokens))
  | CheckTest_err :
      GetM marking p None ->
      CheckTest spn marking p t None.
  
  (** Returns [Some true] if M(p) >= test(p, t), [Some false] otherwise. 
                 
      Raises an error (i.e. None) if [get_m] fail. *)
  
  Definition check_test
             (spn : SPN)
             (marking : marking_type)
             (p : place_type)
             (t : trans_type) : option bool :=
    match get_m marking p with
    | Some nboftokens => Some ((test spn t p) <=? nboftokens)
    | None => None
    end.

  Functional Scheme check_test_ind := Induction for check_test Sort Prop.
  
  (** Soundness proof for check_test and CheckTest. *)
  
  Theorem check_test_correct :
    forall (spn : SPN)
      (marking : marking_type)
      (p : place_type)
      (t : trans_type)
      (opt_b : option bool),
      check_test spn marking p t = opt_b -> CheckTest spn marking p t opt_b.
  Proof.
    intros spn marking p t;
      functional induction (check_test spn marking p t) using check_test_ind;
      intros.
    - rewrite <- H;
        apply CheckTest_cons;
        apply get_m_correct; assumption.
    - rewrite <- H;
        apply CheckTest_err;
        apply get_m_correct; assumption.
  Qed.

  (** Completeness proof for check_test and CheckTest. *)
  
  Theorem check_test_complete :
    forall (spn : SPN)
      (marking : marking_type)
      (p : place_type)
      (t : trans_type)
      (opt_b : option bool),
      CheckTest spn marking p t opt_b -> check_test spn marking p t = opt_b.
  Proof.
    intros; elim H; intros.
    - apply get_m_complete in H0.
      unfold check_test; rewrite H0; reflexivity.
    - apply get_m_complete in H0.
      unfold check_test; rewrite H0; reflexivity.
  Qed.

  (** Formal specification for map_check_test. *)

  Inductive MapCheckTestAux
            (spn : SPN)
            (marking : marking_type) :
    list place_type -> trans_type -> bool -> option bool -> Prop :=
  | MapCheckTestAux_nil :
      forall (t : trans_type)
        (check_result : bool),
        MapCheckTestAux spn marking [] t check_result (Some check_result)
  | MapCheckTestAux_cons :
      forall (test_places : list place_type)
        (t : trans_type)
        (p : place_type)
        (b check_result : bool)
        (opt_b : option bool),
        CheckTest spn marking p t (Some b) ->
        MapCheckTestAux spn marking test_places t (b && check_result) opt_b ->
        MapCheckTestAux spn marking (p :: test_places) t check_result opt_b
  | MapCheckTestAux_err :
      forall (test_places : list place_type)
        (t : trans_type)
        (p : place_type)
        (check_result : bool),
        CheckTest spn marking p t None ->
        MapCheckTestAux spn marking (p :: test_places) t check_result None.
  
  (** Function : Returns [Some true] if ∀ p ∈ [test_places], M(p) >= test(p, t).
                 
                 Raises an error if [get_m] fails. *)
  
  Fixpoint map_check_test_aux
           (spn : SPN)
           (marking : marking_type)
           (test_places : list place_type)
           (t : trans_type)
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

  (** Soundness proof map_check_test_aux and MapCheckTestAux. *)
  
  Theorem map_check_test_aux_correct :
    forall (spn : SPN)
      (marking : marking_type)
      (test_places : list place_type)
      (t : trans_type)
      (check_result : bool)
      (opt_b : option bool),
      map_check_test_aux spn marking test_places t check_result = opt_b ->
      MapCheckTestAux spn marking test_places t check_result opt_b.
  Proof.
    intros spn marking test_places t check_result;
      functional induction (map_check_test_aux spn marking test_places t check_result)
                 using map_check_test_aux_ind;
      intros.
    - rewrite <- H; apply MapCheckTestAux_nil.
    - apply MapCheckTestAux_cons with (b := b); [apply check_test_correct; assumption |
                                                apply IHo; assumption].
    - rewrite <- H; apply MapCheckTestAux_err; apply check_test_correct; assumption.
  Qed.

  (** Completeness proof map_check_test_aux and MapCheckTestAux. *)

  Theorem map_check_test_aux_complete :
    forall (spn : SPN)
      (marking : marking_type)
      (test_places : list place_type)
      (t : trans_type)
      (check_result : bool)
      (opt_b : option bool),
      MapCheckTestAux spn marking test_places t check_result opt_b ->
      map_check_test_aux spn marking test_places t check_result = opt_b.
  Proof.
    intros; elim H; intros.
    - simpl; reflexivity.
    - simpl; apply check_test_complete in H0; rewrite H0; assumption.
    - simpl; apply check_test_complete in H0; rewrite H0; reflexivity.
  Qed.
  
  (** Wrapper around [map_check_test_aux]. *)
  
  Definition map_check_test
             (spn : SPN)
             (marking : marking_type)
             (test_places : list place_type)
             (t : trans_type) : option bool :=
    map_check_test_aux spn marking test_places t true.

  (** Formal specification for map_check_test *)
  Inductive MapCheckTest
            (spn : SPN)
            (marking : marking_type)
            (test_places : list place_type)
            (t : trans_type) :
    option bool -> Prop := 
  | MapCheckTest_cons :
      forall opt_b : option bool,
        MapCheckTestAux spn marking test_places t  true opt_b ->
        MapCheckTest spn marking test_places t opt_b.
  
  (** Soundness proof for map_check_test and MapCheckTest. *)
  
  Theorem map_check_test_correct :
    forall (spn : SPN)
      (marking : marking_type)
      (test_places : list place_type)
      (t : trans_type)
      (opt_b : option bool),
      map_check_test spn marking test_places t = opt_b ->
      MapCheckTest spn marking test_places t opt_b.
  Proof.
    intros spn marking test_places t; unfold map_check_test; intros.
    apply MapCheckTest_cons; apply map_check_test_aux_correct; assumption.
  Qed.

  (** Completeness proof for map_check_test and MapCheckTest. *)

  Theorem map_check_test_complete :
    forall (spn : SPN)
      (marking : marking_type)
      (test_places : list place_type)
      (t : trans_type)
      (opt_b : option bool),
      MapCheckTest spn marking test_places t opt_b ->
      map_check_test spn marking test_places t = opt_b.
  Proof.
    intros; elim H; intros.
    unfold map_check_test; apply map_check_test_aux_complete; assumption.
  Qed.

  (** Formal specification for check_inhib *)
  
  Inductive CheckInhib
            (spn : SPN)
            (marking : marking_type)
            (p : place_type)
            (t : trans_type) :
    option bool -> Prop := 
  | CheckInhib_cons :
      forall (tokens : nat),
        GetM marking p (Some tokens) ->
        CheckInhib spn marking p t (Some (tokens <? (inhib spn t p)))
  | CheckInhib_err :
      GetM marking p None ->
      CheckInhib spn marking p t None.
  
  (** Returns [Some true] if M(p) >= inhib(p, t), [Some false] otherwise. 
                 
      Raises an error (i.e. None) if [get_m] fail. *)
  
  Definition check_inhib
             (spn : SPN)
             (marking : marking_type)
             (p : place_type)
             (t : trans_type) : option bool :=
    match get_m marking p with
    | Some nboftokens => Some (nboftokens <? (inhib spn t p))
    | None => None
    end.

  Functional Scheme check_inhib_ind := Induction for check_inhib Sort Prop.
  
  (** Soundness proof for check_inhib and CheckInhib. *)
  
  Theorem check_inhib_correct :
    forall (spn : SPN)
      (marking : marking_type)
      (p : place_type)
      (t : trans_type)
      (opt_b : option bool),
      check_inhib spn marking p t = opt_b -> CheckInhib spn marking p t opt_b.
  Proof.
    intros spn marking p t;
      functional induction (check_inhib spn marking p t) using check_inhib_ind;
      intros.
    - rewrite <- H;
        apply CheckInhib_cons;
        apply get_m_correct; assumption.
    - rewrite <- H;
        apply CheckInhib_err;
        apply get_m_correct; assumption.
  Qed.

  (** Completeness proof for check_inhib and CheckInhib. *)
  
  Theorem check_inhib_complete :
    forall (spn : SPN)
      (marking : marking_type)
      (p : place_type)
      (t : trans_type)
      (opt_b : option bool),
      CheckInhib spn marking p t opt_b -> check_inhib spn marking p t = opt_b.
  Proof.
    intros; elim H; intros.
    - apply get_m_complete in H0.
      unfold check_inhib; rewrite H0; reflexivity.
    - apply get_m_complete in H0.
      unfold check_inhib; rewrite H0; reflexivity.
  Qed.

  (** Formal specification for map_check_inhib. *)

  Inductive MapCheckInhibAux
            (spn : SPN)
            (marking : marking_type) :
    list place_type -> trans_type -> bool -> option bool -> Prop :=
  | MapCheckInhibAux_nil :
      forall (t : trans_type)
        (check_result : bool),
        MapCheckInhibAux spn marking [] t check_result (Some check_result)
  | MapCheckInhibAux_cons :
      forall (inhib_places : list place_type)
        (t : trans_type)
        (p : place_type)
        (b check_result : bool)
        (opt_b : option bool),
        CheckInhib spn marking p t (Some b) ->
        MapCheckInhibAux spn marking inhib_places t (b && check_result) opt_b ->
        MapCheckInhibAux spn marking (p :: inhib_places) t check_result opt_b
  | MapCheckInhibAux_err :
      forall (inhib_places : list place_type)
        (t : trans_type)
        (p : place_type)
        (check_result : bool),
        CheckInhib spn marking p t None ->
        MapCheckInhibAux spn marking (p :: inhib_places) t check_result None.
  
  (** Function : Returns [Some true] if ∀ p ∈ [inhib_places], M(p) >= inhib(p, t).
                 
                 Raises an error if [get_m] fails. *)
  
  Fixpoint map_check_inhib_aux
           (spn : SPN)
           (marking : marking_type)
           (inhib_places : list place_type)
           (t : trans_type)
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

  (** Soundness proof map_check_inhib_aux and MapCheckInhibAux. *)
  
  Theorem map_check_inhib_aux_correct :
    forall (spn : SPN)
      (marking : marking_type)
      (inhib_places : list place_type)
      (t : trans_type)
      (check_result : bool)
      (opt_b : option bool),
      map_check_inhib_aux spn marking inhib_places t check_result = opt_b ->
      MapCheckInhibAux spn marking inhib_places t check_result opt_b.
  Proof.
    intros spn marking inhib_places t check_result;
      functional induction (map_check_inhib_aux spn marking inhib_places t check_result)
                 using map_check_inhib_aux_ind;
      intros.
    - rewrite <- H; apply MapCheckInhibAux_nil.
    - apply MapCheckInhibAux_cons with (b := b); [apply check_inhib_correct; assumption |
                                                apply IHo; assumption].
    - rewrite <- H; apply MapCheckInhibAux_err; apply check_inhib_correct; assumption.
  Qed.

  (** Completeness proof map_check_inhib_aux and MapCheckInhibAux. *)

  Theorem map_check_inhib_aux_complete :
    forall (spn : SPN)
      (marking : marking_type)
      (inhib_places : list place_type)
      (t : trans_type)
      (check_result : bool)
      (opt_b : option bool),
      MapCheckInhibAux spn marking inhib_places t check_result opt_b ->
      map_check_inhib_aux spn marking inhib_places t check_result = opt_b.
  Proof.
    intros; elim H; intros.
    - simpl; reflexivity.
    - simpl; apply check_inhib_complete in H0; rewrite H0; assumption.
    - simpl; apply check_inhib_complete in H0; rewrite H0; reflexivity.
  Qed.
  
  (** Wrapper around [map_check_inhib_aux]. *)
  
  Definition map_check_inhib
             (spn : SPN)
             (marking : marking_type)
             (inhib_places : list place_type)
             (t : trans_type) : option bool :=
    map_check_inhib_aux spn marking inhib_places t true.

  (** Formal specification for map_check_inhib *)
  Inductive MapCheckInhib
            (spn : SPN)
            (marking : marking_type)
            (inhib_places : list place_type)
            (t : trans_type) :
    option bool -> Prop := 
  | MapCheckInhib_cons :
      forall opt_b : option bool,
        MapCheckInhibAux spn marking inhib_places t  true opt_b ->
        MapCheckInhib spn marking inhib_places t opt_b.
  
  (** Soundness proof for map_check_inhib and MapCheckInhib. *)
  
  Theorem map_check_inhib_correct :
    forall (spn : SPN)
      (marking : marking_type)
      (inhib_places : list place_type)
      (t : trans_type)
      (opt_b : option bool),
      map_check_inhib spn marking inhib_places t = opt_b ->
      MapCheckInhib spn marking inhib_places t opt_b.
  Proof.
    intros spn marking inhib_places t; unfold map_check_inhib; intros.
    apply MapCheckInhib_cons; apply map_check_inhib_aux_correct; assumption.
  Qed.

  (** Completeness proof for map_check_inhib and MapCheckInhib. *)

  Theorem map_check_inhib_complete :
    forall (spn : SPN)
      (marking : marking_type)
      (inhib_places : list place_type)
      (t : trans_type)
      (opt_b : option bool),
      MapCheckInhib spn marking inhib_places t opt_b ->
      map_check_inhib spn marking inhib_places t = opt_b.
  Proof.
    intros; elim H; intros.
    unfold map_check_inhib; apply map_check_inhib_aux_complete; assumption.
  Qed.
  
End Edges.


