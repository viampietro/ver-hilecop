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

  Functional Scheme get_m_ind := Induction for get_m Sort Prop.

  (** Formal specification for get_m *)
  Inductive GetM : marking_type -> nat -> option nat -> Prop :=
  | GetM_err :
      forall (p : place_type), GetM [] p None
  | GetM_if :
      forall (m m' : marking_type)
             (nboftokens : nat)
             (p place : place_type),
        m = (place, nboftokens) :: m' ->
        p = place ->
        GetM m p (Some nboftokens)
  | GetM_else :
      forall (m m' : marking_type)
             (p place : place_type)
             (nboftokens : nat)
             (opt_nboftokens : option nat),
        m = (place, nboftokens) :: m' ->
        p <> place ->
        GetM m' p opt_nboftokens ->
        GetM m p opt_nboftokens.

  (** Correctness proof : get_m ***)
  Theorem get_m_correct :
    forall (m : marking_type)
           (p : place_type)
           (opt_nboftokens : option nat),
      get_m m p = opt_nboftokens -> GetM m p opt_nboftokens.
  Proof.
    do 2 intro; functional induction (get_m m p) using get_m_ind; intros.
    (* Case m = []. *)
    - rewrite <- H; apply GetM_err.
    (* Case if is true. *)
    - rewrite <- H.
      apply GetM_if with (m' := tail) (p := p) (place := place);
        [auto | rewrite Nat.eqb_sym in e1; apply beq_nat_true in e1; auto].
    (* Case else *)
    - apply GetM_else with (p := p) (place := place) (nboftokens := nboftokens) (m' := tail).
      + auto.
      + rewrite Nat.eqb_sym in e1. apply beq_nat_false in e1. auto.
      + rewrite <- H. apply IHo with (opt_nboftokens := (get_m tail p)). auto.
  Qed.

  (** Completeness proof : get_m ***)
  Theorem get_m_compl :
    forall (m : marking_type) (p : place_type) (opt_nboftokens : option nat),
      GetM m p opt_nboftokens -> get_m m p = opt_nboftokens.
  Proof.
    intros. induction H.
    (* Case GetM_0 *)
    - simpl; auto.
    (* Case GetM_if *)
    - rewrite H. simpl.
      rewrite Nat.eqb_sym.
      rewrite H0.
      rewrite Nat.eqb_refl.
      auto.
    (* Case GetM_else *)
    - rewrite H. simpl.
      apply Nat.eqb_neq in H0.
      rewrite Nat.eqb_sym.
      apply beq_nat_false in H0.
      apply not_eq_sym in H0.
      apply Nat.eqb_neq in H0.
      rewrite H0.
      assumption.
  Qed.
  
  (* Lemma : For all marking "some_marking" and place p, 
   *         (get_m some_marking p) returns no error
   *         if p is referenced in some_marking.
   **)
  Lemma get_m_no_error :
    forall (some_marking : marking_type)
           (p : place_type),
      In p (fst (split some_marking)) ->
      exists v : nat, get_m some_marking p = Some v.
  Proof.
    intros;
      functional induction (get_m some_marking p) using get_m_ind;
      decide_accessor_no_err.
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

  (** Formal specification : replace_occ *)
  
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

  (** Correctness proof : replace_occ *)
  
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

  (** Completeness proof : replace_occ *)
  
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

  (** Lemma : Auxiliary lemma to prove replace_occ_nodup 
              and replace_occ_nodup_marking. *)
  
  Lemma replace_occ_no_change {A: Type} :
    forall (eq_dec : forall x y : A, {x = y} + {x <> y}) (occ repl : A) (l : list A),
      ~In occ l -> replace_occ eq_dec occ repl l = l.
  Proof.
    intros; functional induction (replace_occ eq_dec occ repl l)
                       using replace_occ_ind.
    (* Base case, l = [] *)
    - auto.
    (* Case occ = hd l *)
    - apply not_in_cons in H; elim H; intros. elim H0; auto.
    (* Case occ <> hd l *)
    - cut (~In occ tl).
      + intro. rewrite (IHl0 H0). auto.
      + apply not_in_cons in H. elim H; auto.
  Qed.

  (** Lemma : Auxiliary lemma to prove replace_occ_nodup
              and replace_occ_nodup_marking. *)
  
  Lemma replace_occ_not_in {A :Type} :
    forall (eq_dec : forall x y : A, {x = y} + {x <> y}) (occ repl a : A) (l : list A),
      a <> repl /\ ~In a l -> ~In a (replace_occ eq_dec occ repl l).
  Proof.
    intros;
      functional induction (replace_occ eq_dec occ repl l)
                 using replace_occ_ind;
      intros.
    (* Base case, l = [] *)
    - auto.
    (* Case occ = hd l *)
    - apply not_in_cons; split.
      + elim H; auto.
      + apply IHl0; split; elim H; intros;
          [auto | apply not_in_cons in H1; elim H1; auto ].
    (* Case occ <> hd l *)
    - apply not_in_cons; split.
      + elim H; intros. apply not_in_cons in H1; elim H1; auto.
      + apply IHl0; split; elim H; intros;
          [ auto | apply not_in_cons in H1; elim H1; auto ].
  Qed.

  (** Lemma : For all list l, if NoDup l and repl not in l
              then NoDup (replace_occ occ repl l). *)
  
  Lemma replace_occ_nodup {A : Type} :
    forall (eq_dec : forall x y : A, {x = y} + {x <> y}) (occ repl : A) (l : list A),
      NoDup l -> ~In repl l -> NoDup (replace_occ eq_dec occ repl l).
  Proof.
    intros; functional induction (replace_occ eq_dec occ repl l)
                       using replace_occ_ind.
    (* Base case, l = []*)
    - apply NoDup_nil.
    (* Case occ = hd l *)
    - apply NoDup_cons.
      -- apply NoDup_cons_iff in H. elim H; intros.
         apply replace_occ_no_change with (eq_dec0 := eq_dec) (repl0 := repl) in H1; rewrite H1.
         apply not_in_cons in H0. elim H0. intros. auto.
      -- apply IHl0.
         ++ apply NoDup_cons_iff in H; elim H; intros; auto.
         ++ apply not_in_cons in H0; elim H0; intros; auto.
    (* Case occ <> hd l *)
    - apply NoDup_cons.
      -- apply NoDup_cons_iff in H. elim H; intros.
         apply replace_occ_no_change with (eq_dec0 := eq_dec) (repl0 := repl) in H1.
         apply replace_occ_not_in.
         split.
         { apply not_in_cons in H0. elim H0; intros; auto. }
         { elim H; intros; auto. }
      -- apply IHl0.
         ++ apply NoDup_cons_iff in H; elim H; intros; auto.
         ++ apply not_in_cons in H0; elim H0; intros; auto.
  Qed.

  (** Lemma : Auxiliary lemma to prove replace_occ_nodup_marking. *)
  
  Lemma not_in_fst_split_replace_occ :
    forall (l : list (nat * nat)) (x : nat) (y y' : nat) (a : nat),
      ~In a (fst (split l)) -> a <> x -> ~In a (fst (split (replace_occ prodnat_eq_dec (x, y) (x, y') l))).
  Proof.
    do 4 intro.
    functional induction (replace_occ prodnat_eq_dec (x, y) (x, y') l)
               using replace_occ_ind; intros.
    - auto.
    - rewrite fst_split_cons_app; simpl; apply not_in_cons.
      split; auto.
      apply IHl0.
      + rewrite fst_split_cons_app in H; simpl in H.
        apply Decidable.not_or in H.
        elim H; intros; auto.
      + auto.
    - generalize dependent x0; intro; elim x0; intros.
      rewrite fst_split_cons_app; simpl; apply not_in_cons.
      split.
      + rewrite fst_split_cons_app in H; simpl in H.
        apply Decidable.not_or in H.
        elim H; intros; auto.
      + apply IHl0.
        -- rewrite fst_split_cons_app in H; simpl in H.
           apply Decidable.not_or in H.
           elim H; intros; auto.
        -- auto.
  Qed.

  (** Lemma : If no duplicates in (fst (split m))
              then no duplicates in (replace_occ (p, n) (p, n') m).
              
              This holds because (fst (p, n)) = (fst (p, n')). *)
  
  Lemma replace_occ_nodup_marking :
    forall (m : marking_type) (p : place_type) (n n' : nat),
      NoDup (fst (split m)) ->
      NoDup (fst (split (replace_occ prodnat_eq_dec (p, n) (p, n') m))).
  Proof.
    do 4 intro.
    functional induction (replace_occ prodnat_eq_dec (p, n) (p, n') m)
               using replace_occ_ind.
    (* Base case, l = [] *)
    - intro; apply NoDup_nil.
    (* Case occ = hd l *)
    - intros.
      generalize (nodup_fst_split ((p, n) :: tl) H); intro.
      apply NoDup_cons_iff in H0.
      elim H0; intros.
      apply replace_occ_no_change with (eq_dec := prodnat_eq_dec)
                                       (repl := (p, n')) in H1.
      rewrite H1.
      rewrite fst_split_cons_app in H.
      rewrite fst_split_cons_app.
      simpl in H.
      simpl.
      auto.
    (* Case occ <> hd l *)
    - generalize dependent x; intro.
      elim x; intros.
      assert (H' := H).
      assert (Hor := (classic (In (p, n) tl))).
      elim Hor; clear Hor; intros.
      (* Case In (p, n) tl *)
      + rewrite fst_split_cons_app in H; simpl in H.
        apply NoDup_cons_iff in H.
        elim H; intros.
        generalize (in_fst_split p n tl H0); intros.
        generalize (not_in_in_diff a p (fst (split tl)) (conj H1 H3)); intro.
        generalize (not_in_fst_split_replace_occ tl p n n' a H1 H4); intro.
        rewrite fst_split_cons_app; simpl; apply NoDup_cons.
        -- auto.
        -- apply IHl; auto.
      (* Case ~In (p, n) tl *)
      + apply replace_occ_no_change with (eq_dec := prodnat_eq_dec) (repl := (p, n')) in H0.
        rewrite H0.
        apply nodup_fst_split in H.
        auto.
  Qed.
  
  (** Lemma : Proves that replace_occ preserves structure
              of a marking m passed as argument when 
              (fst occ) = (fst repl). *)
  
  Lemma replace_occ_same_struct :
    forall (m : marking_type)
           (p : place_type)
           (n n' : nat),
      MarkingHaveSameStruct (replace_occ prodnat_eq_dec (p, n) (p, n') m) m.
  Proof.
    do 4 intro.
    unfold MarkingHaveSameStruct.
    functional induction (replace_occ prodnat_eq_dec (p, n) (p, n') m)
               using replace_occ_ind;
      intros.
    (* Base case. *)
    - auto.
    (* Case (p,n) is hd of list. *)
    - intros.
      rewrite fst_split_cons_app.
      symmetry.
      rewrite fst_split_cons_app.
      rewrite IHl.
      simpl.
      auto.
    (* Case (p, n) not hd of list. *)
    - rewrite fst_split_cons_app.
      symmetry.
      rewrite fst_split_cons_app.
      rewrite IHl.
      auto.
  Qed.
  
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

  Functional Scheme modify_m_ind := Induction for modify_m Sort Prop.

  (** Formal specification : modify_m *)
  
  Inductive ModifyM
            (marking : marking_type)
            (p : place_type)
            (op : nat -> nat -> nat) :
    option nat_star -> option marking_type -> Prop :=
  | ModifyM_tokens_none :
      ModifyM marking p op None (Some marking)
  (* Case place of index i is not in the marking,
   * which is a exception case. *)
  | ModifyM_err :
      forall (n : nat_star),
        GetM marking p None ->
        ModifyM marking p op (Some n) None
  (* Case place of index i exists in the marking *)
  | ModifyM_some_repl :
      forall (nboftokens : option nat_star)
        (n n' : nat)
        (is_positive : n' > 0)
        (m' : marking_type),
        nboftokens = Some (mk_nat_star n' is_positive) ->
        GetM marking p (Some n) ->
        ReplaceOcc prodnat_eq_dec (p, n) (p, (op n n')) marking m' ->
        ModifyM marking p op nboftokens (Some m').

  (** Correctness proof : modify_m *)
  
  (* Theorem modify_m_correct : *)
  (*   forall (spn : SPN) *)
  (*     (optionspn : option SPN) *)
  (*     (p : place_type) *)
  (*     (op : nat -> nat -> nat) *)
  (*     (nboftokens : option nat_star), *)
  (*     modify_m spn p op nboftokens = optionspn -> ModifyM spn p op nboftokens optionspn. *)
  (* Proof. *)
  (*   do 5 intro; functional induction (modify_m m p op nboftokens) *)
  (*                          using modify_m_ind; intros. *)
  (*   (* Case (pl i) exists in marking m *) *)
  (*   - rewrite <- H. apply ModifyM_some_repl with (n := n0) *)
  (*                                                (n' := n') *)
  (*                                                (is_positive := _x). *)
  (*     + auto. *)
  (*     + apply get_m_correct in e1; auto. *)
  (*     + apply replace_occ_correct; auto. *)
  (*   (* Case (pl i) doesn't exist in marking m (error) *) *)
  (*   - rewrite <- H. apply ModifyM_err. *)
  (*     + apply get_m_correct; auto. *)
  (*   (* Case nboftokens is None *) *)
  (*   - rewrite <- H; apply ModifyM_tokens_none. *)
  (* Qed. *)

  (** Completeness proof : modify_m *)
  
  (* Theorem modify_m_compl : *)
  (*   forall (spn : SPN) *)
  (*     (optionspn : option SPN) *)
  (*     (p : place_type) *)
  (*     (op : nat -> nat -> nat) *)
  (*     (nboftokens : option nat_star), *)
  (*     ModifyM spn p op nboftokens optionspn -> modify_m spn p op nboftokens = optionspn. *)
  (* Proof. *)
  (*   intros; induction H. *)
  (*   (* Case  ModifyM_tokens_none *) *)
  (*   - simpl; auto. *)
  (*   (* Case ModifyM_err *) *)
  (*   - unfold modify_m; elim n; intros. *)
  (*     apply get_m_compl in H; rewrite H; auto. *)
  (*   (* Case ModifyM_some_repl *) *)
  (*   - unfold modify_m; rewrite H; apply get_m_compl in H0; rewrite H0. *)
  (*     apply replace_occ_compl in H1; rewrite H1; auto.       *)
  (* Qed. *)

  (** Lemma : Proves that modify_m preserves the structure of the marking m
              passed as argument. *)
  
  (* Lemma modify_m_same_struct : *)
  (*   forall (m m' : marking_type) *)
  (*     (p : place_type) *)
  (*     (op : nat -> nat -> nat) *)
  (*     (nboftokens : option nat_star), *)
  (*     modify_m m p op nboftokens = Some m' -> *)
  (*     MarkingHaveSameStruct m m'. *)
  (* Proof. *)
  (*   do 5 intro. *)
  (*   functional induction (modify_m m p op nboftokens) *)
  (*              using modify_m_ind; *)
  (*     intros. *)
  (*   - injection H; intros. *)
  (*     rewrite <- H0. *)
  (*     unfold MarkingHaveSameStruct; symmetry. *)
  (*     apply replace_occ_same_struct. *)
  (*   - inversion H. *)
  (*   - injection H; intros. *)
  (*     rewrite H0. *)
  (*     unfold MarkingHaveSameStruct; auto. *)
  (* Qed. *)

  (** Lemma : If there are no duplicates in (fst (split m)),
              then modify_m returns a marking with no duplicates. *)
  
  (* Lemma modify_m_nodup : *)
  (*   forall (m m' : marking_type) *)
  (*          (p : place_type) *)
  (*          (op : nat -> nat -> nat) *)
  (*          (nboftokens : option nat_star), *)
  (*     NoDup (fst (split m)) -> *)
  (*     modify_m m p op nboftokens = Some m' -> *)
  (*     NoDup (fst (split m')). *)
  (* Proof. *)
  (*   do 5 intro. *)
  (*   functional induction (modify_m m p op nboftokens) *)
  (*              using modify_m_ind; *)
  (*   intros. *)
  (*   (* Case get_m returns Some value. *) *)
  (*   - apply replace_occ_nodup_marking with (p := p) (n := n0) (n' := (op n0 n')) in H. *)
  (*     injection H0; intros. *)
  (*     rewrite <- H1. *)
  (*     auto. *)
  (*   (* Case get_m returns None, leads  *)
  (*    * to a contradiction. *)
  (*    *) *)
  (*   - inversion H0. *)
  (*   (* Case nboftokens = None *) *)
  (*   - injection H0; intros; rewrite <- H1; auto. *)
  (* Qed. *)
  
  (** Lemma : For all spn, [modify_m] returns no error
              if p is in referenced in [spn.(marking)]. *)
  
  (* Lemma modify_m_no_error : *)
  (*   forall (spn : SPN) *)
  (*     (nboftokens : option nat_star) *)
  (*     (op : nat -> nat -> nat) *)
  (*     (p : place_type), *)
  (*     In p (fst (split some_marking)) -> *)
  (*     exists v : marking_type, *)
  (*       modify_m some_marking p op nboftokens = Some v. *)
  (* Proof. *)
  (*   intros. *)
  (*   functional induction (modify_m some_marking p op nboftokens) *)
  (*              using modify_m_ind.     *)
  (*   (* Base case *) *)
  (*   - exists (replace_occ prodnat_eq_dec (p, n0) (p, op n0 n') some_marking). *)
  (*     auto. *)
  (*   (* Case get_m = None, not possible. *) *)
  (*   - apply get_m_no_error in H. *)
  (*     elim H; intros. *)
  (*     rewrite H0 in e1. *)
  (*     inversion e1. *)
  (*   (* Case nboftokens = None *) *)
  (*   - exists some_marking; auto.     *)
  (* Qed.              *)
  
  (*=================================================*)
  (*=============== UPDATE MARKING ==================*)
  (*=================================================*)

  (** Function : Removes some tokens from pre places, result  
                 of the firing of t. 
                 
                 Returns a new SPN with an updated marking. *)
  
  Fixpoint update_marking_pre
           (spn : SPN)
           (t : trans_type)
           (places : list place_type) : option SPN :=
    match places with
    | p :: tail => match modify_m spn.(marking) p Nat.sub (pre spn t p) with
                   | Some m' => update_marking_pre (set_m spn m') t tail
                   (* It's an exception, p is not referenced in spn.(marking). *)
                   | None => None
                   end
    | [] => Some spn
    end.

  Functional Scheme update_marking_pre_ind := Induction for update_marking_pre Sort Prop.
  
  (** Formal specification : update_marking_pre *)
  
  Inductive UpdateMarkingPre
            (spn : SPN)
            (t : trans_type) :
    list place_type -> option SPN -> Prop :=
  | UpdateMarkingPre_nil :
      UpdateMarkingPre spn t [] (Some spn)
  | UpdateMarkingPre_some :
      forall (places : list place_type)
        (m' : marking_type)
        (optionspn : option SPN)
        (p : place_type),
        ModifyM spn.(marking) p Nat.sub (pre spn t p) (Some m') ->
        UpdateMarkingPre (set_m spn m') t places optionspn ->
        UpdateMarkingPre spn t (p :: places) optionspn
  | UpdateMarkingPre_err :
      forall (p : place_type) (places : list place_type),
        ModifyM spn.(marking) p Nat.sub (pre spn t p) None ->
        UpdateMarkingPre spn t (p :: places) None.

  (** Correctness proof : update_marking_pre *)
  
  (* Theorem update_marking_pre_correct : *)
  (*   forall (t : trans_type) *)
  (*          (pre : weight_type) *)
  (*          (places : list place_type) *)
  (*          (m : marking_type) *)
  (*          (optionm : option marking_type), *)
  (*     update_marking_pre t pre m places = optionm -> *)
  (*     UpdateMarkingPre t pre m places optionm. *)
  (* Proof. *)
  (*   intros t pre places m optionm; *)
  (*     functional induction (update_marking_pre t pre m places) *)
  (*                using update_marking_pre_ind; *)
  (*     intros. *)
  (*   (* Case places is nil *) *)
  (*   - rewrite <- H; apply UpdateMarkingPre_nil. *)
  (*   (* Case p is referenced in m *) *)
  (*   - apply UpdateMarkingPre_some with (m' := m'). *)
  (*     + apply modify_m_correct; auto. *)
  (*     + apply IHo; auto. *)
  (*   (* Case p is not in m *) *)
  (*   - rewrite <- H; apply UpdateMarkingPre_err; *)
  (*       [apply modify_m_correct; auto].       *)
  (* Qed. *)

  (** Completeness proof : update_marking_pre *)
  
  (* Theorem update_marking_pre_compl : *)
  (*   forall (t : trans_type) *)
  (*     (pre : weight_type) *)
  (*     (places : list place_type) *)
  (*     (m : marking_type) *)
  (*     (optionm : option marking_type), *)
  (*     UpdateMarkingPre t pre m places optionm -> *)
  (*     update_marking_pre t pre m places = optionm. *)
  (* Proof. *)
  (*   intros t pre places m optionm Hspec; induction Hspec. *)
  (*   (* Case UpdateMarkingPre_nil *) *)
  (*   - simpl; auto. *)
  (*   (* Case UpdateMarkingPre_some *) *)
  (*   - simpl; apply modify_m_compl in H; rewrite H; rewrite IHHspec; auto. *)
  (*   (* Case UpdateMarkingPre_err *) *)
  (*   - simpl; apply modify_m_compl in H; rewrite H; auto. *)
  (* Qed. *)
  
  (** Lemma : Proves that [update_marking_pre] returns no error 
              if all places of the list passed as argument
              are referenced in the marking (also passed as argument). *)
  
  (* Lemma update_marking_pre_no_error : *)
  (*   forall (t : trans_type) *)
  (*          (pre : weight_type) *)
  (*          (places : list place_type) *)
  (*          (marking : marking_type), *)
  (*     incl places (fst (split marking)) -> *)
  (*     exists v : marking_type, update_marking_pre t pre marking places = Some v. *)
  (* Proof. *)
  (*   unfold incl. *)
  (*   intros t pre places marking p; *)
  (*   functional induction (update_marking_pre t pre marking places) *)
  (*              using update_marking_pre_ind; *)
  (*   intros. *)
  (*   (* Base case, some_places = []. *) *)
  (*   - exists m; auto. *)
  (*   (* Case modify_m returns some marking. *) *)
  (*   - apply IHo; intros. *)
  (*     apply (in_cons p0) in H. *)
  (*     apply p in H. *)
  (*     apply modify_m_same_struct in e0. *)
  (*     unfold MarkingHaveSameStruct in e0. *)
  (*     rewrite <- e0. *)
  (*     auto. *)
  (*   (* Case modify_m returns None,  *)
  (*    * impossible regarding the hypothesis  *)
  (*    *) *)
  (*   - cut (In p0 (p0 :: tail)). *)
  (*     + intro. *)
  (*       apply p in H. *)
  (*       apply modify_m_no_error with (nboftokens := (pre t p0)) *)
  (*                                    (op := Nat.sub) in H. *)
  (*       elim H; intros. *)
  (*       rewrite e0 in H0. *)
  (*       inversion H0. *)
  (*     + apply in_eq. *)
  (* Qed. *)
  
  (** Lemma : Proves that update_marking_pre preserves
              the structure of the marking m
              passed as argument. *)
  
  (* Lemma update_marking_pre_same_struct : *)
  (*   forall (t : trans_type) *)
  (*          (pre : weight_type) *)
  (*          (places : list place_type) *)
  (*          (m m' : marking_type), *)
  (*     update_marking_pre t pre m places = Some m' -> *)
  (*     MarkingHaveSameStruct m m'. *)
  (* Proof. *)
  (*   intros t pre places m m'. *)
  (*   functional induction (update_marking_pre t pre m places) *)
  (*              using update_marking_pre_ind; *)
  (*     intros. *)
  (*   - injection H; intros. *)
  (*     rewrite H0. *)
  (*     unfold MarkingHaveSameStruct; auto. *)
  (*   - apply IHo in H. *)
  (*     apply modify_m_same_struct in e0. *)
  (*     unfold MarkingHaveSameStruct. *)
  (*     unfold MarkingHaveSameStruct in e0. *)
  (*     unfold MarkingHaveSameStruct in H. *)
  (*     rewrite <- H; rewrite e0; auto. *)
  (*   - inversion H.     *)
  (* Qed. *)

  (** Lemma : If there are no duplicates in (fst (split m)),
              then update_marking_pre returns a marking with no duplicates. *)
  
  (* Lemma update_marking_pre_nodup : *)
  (*   forall (t : trans_type) *)
  (*          (pre : weight_type) *)
  (*          (places : list place_type) *)
  (*          (m m' : marking_type), *)
  (*     NoDup (fst (split m)) -> *)
  (*     update_marking_pre t pre m places = Some m' -> *)
  (*     NoDup (fst (split m')). *)
  (* Proof. *)
  (*   intros t pre places m. *)
  (*   functional induction (update_marking_pre t pre m places) *)
  (*              using update_marking_pre_ind; *)
  (*   intros. *)
  (*   (* Base case, places = []. *) *)
  (*   - injection H0; intros; rewrite <- H1; auto. *)
  (*   (* Case modify_m returns Some value. *) *)
  (*   - apply IHo. *)
  (*     + apply (modify_m_nodup m m' p Nat.sub (pre t p) H e0). *)
  (*     + auto. *)
  (*   (* Case modify_m returns None, leads to a contradiction. *) *)
  (*   - inversion H0. *)
  (* Qed. *)
  
  (** Function : Adds some tokens from post places, according 
                 to the firing of t.

                 Returns a new marking application. *)
  
  Fixpoint update_marking_post
           (spn : SPN)
           (t : trans_type)
           (places : list place_type) : option SPN :=
    match places with
    | p :: tail => match modify_m spn.(marking) p Nat.add (post spn t p) with
                   | Some m' => update_marking_post (set_m spn m') t tail
                   (* It's a exception, p is not referenced in m. *)
                   | None => None
                   end
    | [] => Some spn
    end.

  Functional Scheme update_marking_post_ind := Induction for update_marking_post Sort Prop.

  (** Formal specification : update_marking_post *)
  
  Inductive UpdateMarkingPost
            (spn : SPN)
            (t : trans_type) :
    list place_type -> option SPN -> Prop :=
  | UpdateMarkingPost_nil :
      UpdateMarkingPost spn t [] (Some spn)
  | UpdateMarkingPost_some :
      forall (p : place_type)
        (m' : marking_type)
        (optionspn : option SPN)
        (places : list place_type),
        ModifyM spn.(marking) p Nat.add (post spn t p) (Some m') ->
        UpdateMarkingPost (set_m spn m') t places optionspn ->
        UpdateMarkingPost spn t (p :: places) optionspn
  | UpdateMarkingPost_err :
      forall (p : place_type)
        (places : list place_type),
        ModifyM spn.(marking) p Nat.add (post spn t p) None ->
        UpdateMarkingPost spn t (p :: places) None.

  (** Correctness proof : update_marking_post *)
  
  (* Theorem update_marking_post_correct : *)
  (*   forall (t : trans_type) *)
  (*          (post : weight_type) *)
  (*          (places : list place_type) *)
  (*          (m : marking_type) *)
  (*          (optionm : option marking_type), *)
  (*     update_marking_post t post m places = optionm -> *)
  (*     UpdateMarkingPost t post m places optionm. *)
  (* Proof. *)
  (*   intros t post places m optionm; *)
  (*     functional induction (update_marking_post t post m places) *)
  (*                using update_marking_post_ind; *)
  (*     intros. *)
  (*   (* Case places is nil *) *)
  (*   - rewrite <- H; apply UpdateMarkingPost_nil. *)
  (*   (* Case p is referenced in m. *) *)
  (*   - apply UpdateMarkingPost_some with (m' := m'). *)
  (*     + apply modify_m_correct; auto. *)
  (*     + apply (IHo H); auto. *)
  (*   (* Case p not referenced in m, error! *) *)
  (*   - rewrite <- H; *)
  (*       apply UpdateMarkingPost_err; *)
  (*       apply modify_m_correct; auto. *)
  (* Qed. *)

  (** Completeness proof : update_marking_post *)
  
  (* Theorem update_marking_post_compl : *)
  (*   forall (t : trans_type) *)
  (*          (post : weight_type) *)
  (*          (places : list place_type) *)
  (*          (m : marking_type) *)
  (*          (optionm : option marking_type), *)
  (*     UpdateMarkingPost t post m places optionm -> *)
  (*     update_marking_post t post m places = optionm. *)
  (* Proof. *)
  (*   intros t post places m optionm H; elim H; intros. *)
  (*   (* Case UpdateMarkingPost_nil *) *)
  (*   - simpl; auto. *)
  (*   (* Case UpdateMarkingPost_some *) *)
  (*   - simpl; apply modify_m_compl in H0; rewrite H0; auto. *)
  (*   (* Case UpdateMarkingPost_err *) *)
  (*   - simpl; apply modify_m_compl in H0; rewrite H0; auto. *)
  (* Qed. *)

  (** Lemma : Proves that update_marking_pre returns no error 
              if all places of the list passed as argument
              are referenced in the marking (also passed as argument). *)
  
  (* Lemma update_marking_post_no_error : *)
  (*   forall (t : trans_type) *)
  (*          (post : weight_type) *)
  (*          (places : list place_type) *)
  (*          (marking : marking_type), *)
  (*     incl places (fst (split marking)) -> *)
  (*     exists v : marking_type, *)
  (*       update_marking_post t post marking places = Some v. *)
  (* Proof. *)
  (*   unfold incl. *)
  (*   intros t post places marking p; *)
  (*   functional induction (update_marking_post t post marking places) *)
  (*              using update_marking_post_ind; *)
  (*   intros. *)
  (*   (* Base case, some_places = []. *) *)
  (*   - exists m; auto. *)
  (*   (* Case modify_m returns some marking. *) *)
  (*   - apply IHo; intros. *)
  (*     apply (in_cons p0) in H. *)
  (*     apply p in H. *)
  (*     apply modify_m_same_struct in e0. *)
  (*     unfold MarkingHaveSameStruct in e0. *)
  (*     rewrite <- e0. *)
  (*     auto. *)
  (*   (* Case modify_m returns None,  *)
  (*    * impossible regarding the hypothesis  *)
  (*    *) *)
  (*   - cut (In p0 (p0 :: tail)). *)
  (*     + intro. *)
  (*       apply p in H. *)
  (*       apply modify_m_no_error with (nboftokens := (post t p0)) *)
  (*                                    (op := Nat.add) in H. *)
  (*       elim H; intros. *)
  (*       rewrite e0 in H0. *)
  (*       inversion H0. *)
  (*     + apply in_eq. *)
  (* Qed. *)

  (** Lemma : Proves that update_marking_post preserves
              the structure of the marking m
              passed as argument. *)
  
  (* Lemma update_marking_post_same_struct : *)
  (*   forall (t : trans_type) *)
  (*          (post : weight_type) *)
  (*          (places : list place_type) *)
  (*          (m m' : marking_type), *)
  (*     update_marking_post t post m places = Some m' -> *)
  (*     MarkingHaveSameStruct m m'. *)
  (* Proof. *)
  (*   intros t post places m m'. *)
  (*   functional induction (update_marking_post t post m places) *)
  (*              using update_marking_post_ind; *)
  (*     intros. *)
  (*   - injection H; intros. *)
  (*     rewrite H0. *)
  (*     unfold MarkingHaveSameStruct; auto. *)
  (*   - apply IHo in H. *)
  (*     apply modify_m_same_struct in e0. *)
  (*     unfold MarkingHaveSameStruct. *)
  (*     unfold MarkingHaveSameStruct in e0. *)
  (*     unfold MarkingHaveSameStruct in H. *)
  (*     rewrite <- H; rewrite e0; auto. *)
  (*   - inversion H.     *)
  (* Qed. *)

  (** Lemma : If there are no duplicates in (fst (split m)),
              then update_marking_post returns a marking with no duplicates. *)
  
  (* Lemma update_marking_post_nodup : *)
  (*   forall (t : trans_type) *)
  (*          (post : weight_type) *)
  (*          (places : list place_type) *)
  (*          (m m' : marking_type), *)
  (*     NoDup (fst (split m)) -> *)
  (*     update_marking_post t post m places = Some m' -> *)
  (*     NoDup (fst (split m')). *)
  (* Proof. *)
  (*   intros t post places m. *)
  (*   functional induction (update_marking_post t post m places) *)
  (*              using update_marking_post_ind; *)
  (*     intros. *)
  (*   (* Base case, places = []. *) *)
  (*   - injection H0; intros; rewrite <- H1; auto. *)
  (*   (* Case modify_m returns Some value. *) *)
  (*   - apply IHo. *)
  (*     + apply (modify_m_nodup m m' p Nat.add (post t p) H e0). *)
  (*     + auto. *)
  (*   (* Case modify_m returns None, leads to a contradiction. *) *)
  (*   - inversion H0. *)
  (* Qed. *)
  
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

  (** Formal specification : get_neighbours *)
  
  Inductive GetNeighbours :
    list (trans_type * neighbours_type) ->
    nat ->
    option neighbours_type -> Prop :=
  | GetNeighbours_err :
      forall (t : nat), GetNeighbours [] t None
  | GetNeighbours_if :
      forall (lneighbours : list (trans_type * neighbours_type))
             (t t' : trans_type)
             (neighbours : neighbours_type),
        t' = t ->
        GetNeighbours ((t', neighbours) :: lneighbours) t (Some neighbours)
  | GetNeighbours_else :
      forall (lneighbours : list (trans_type * neighbours_type))
             (t t' : trans_type)
             (neighbours : neighbours_type)
             (opt_neighbours : option neighbours_type),
        t' <> t ->
        GetNeighbours lneighbours t opt_neighbours ->
        GetNeighbours ((t', neighbours) :: lneighbours) t opt_neighbours.

  Functional Scheme get_neighbours_ind := Induction for get_neighbours Sort Prop.
  
  (** Correctness proof : get_neighbours *)
  
  Theorem get_neighbours_correct :
    forall (lneighbours : list (trans_type * neighbours_type))
           (t : trans_type)
           (opt_neighbours : option neighbours_type),
      get_neighbours lneighbours t = opt_neighbours ->
      GetNeighbours lneighbours t opt_neighbours.
  Proof.
    intros lneighbours t opt_neighbours;
      functional induction (get_neighbours lneighbours t) using get_neighbours_ind; intros.
    (* Case neighbours = None *)
    - rewrite <- H; apply GetNeighbours_err.
    (* Case neighbour is head *)
    - rewrite <- H; apply GetNeighbours_if.
      apply beq_nat_true in e1; auto.
    (* Case neighbour is not head *)
    - rewrite <- H; apply GetNeighbours_else.
      + apply beq_nat_false in e1; auto.
      + rewrite H; apply IHo; auto.
  Qed.

  (** Completeness proof : get_neighbours *)
  
  Theorem get_neighbours_compl :
    forall (lneighbours : list (trans_type * neighbours_type))
           (t : trans_type)
           (opt_neighbours : option neighbours_type),
      GetNeighbours lneighbours t opt_neighbours ->
      get_neighbours lneighbours t = opt_neighbours.
  Proof.
    intros. induction H.
    (* Case GetNeighbours_err *)
    - simpl; auto.
    (* Case GetNeighbours_if *)
    - simpl.
      rewrite H.
      rewrite Nat.eqb_refl.
      auto.
    (* Case GetNeighbours_else *)
    - simpl.
      apply Nat.eqb_neq in H.
      rewrite H.
      auto.
  Qed.

  (** Lemma : For all list of neighbours lneighbours 
              and transition t, (get_neighbours lneighbours t) 
              returns no error if t is referenced in lneighbours. *)
  
  Lemma get_neighbours_no_error :
    forall (lneighbours : list (trans_type * neighbours_type))
           (t : trans_type),
      In t (fst (split lneighbours)) ->
      exists v : neighbours_type,
        get_neighbours lneighbours t = Some v.
  Proof.
    intros lneighbours t.
    functional induction (get_neighbours lneighbours t)
               using get_neighbours_ind;
      intros;
      decide_accessor_no_err.
  Qed.
  
  (** Lemma : If get_neighbours returns some neighbours
              for a transition t and a list lneighbours, then
              the couple (t, neighbours) is in lneighbours. *)
  
  Lemma get_neighbours_in :
    forall (lneighbours : list (trans_type * neighbours_type))
           (t : trans_type)
           (neighbours : neighbours_type),
      get_neighbours lneighbours t = Some neighbours ->
      In (t, neighbours) lneighbours.
  Proof.
    intros lneighbours t.
    functional induction (get_neighbours lneighbours t)
               using get_neighbours_ind;
      intros.
    - inversion H.
    - injection H; intros; rewrite H0.
      symmetry in e1; apply beq_nat_eq in e1.
      rewrite e1.
      apply in_eq.
    - apply in_cons.
      apply IHo.
      auto.
  Qed.
  
End Neighbours.

(*===============================================================*)
(*== CHECKS NB OF TOKENS IN NEIGHBOUR PLACES OF A TRANSITION T ==*)
(*== WITH WEIGHT OF ITS ADJACENT EDGES.                        ==*)
(*===============================================================*)

Section Edges.

  (** Formal specification : check_pre *)
  
  Inductive CheckPre (spn : SPN) (p : place_type) (t : trans_type) :
    option bool -> Prop :=
  | CheckPre_cons_some :
      forall (weight : nat)
             (is_positive : weight > 0)
             (nboftokens : nat),
        pre spn t p = Some (mk_nat_star weight is_positive) ->
        GetM spn.(marking) p (Some nboftokens) ->
        CheckPre spn p t (Some (weight <=? nboftokens))
  | CheckPre_cons_none :
      pre spn t p = None ->
      CheckPre spn p t (Some true)
  | CheckPre_err :
      forall (weight : nat)
        (is_positive : weight > 0),
        pre spn t p = Some (mk_nat_star weight is_positive) ->
        GetM spn.(marking) p None ->
        CheckPre spn p t None.

  (** Function : Returns [Some true] if M(p) >= pre(p, t), [Some false] otherwise. 
                 
                 Raises an error (i.e. None) if [get_m] fail.
   *)
  
  Definition check_pre (spn : SPN) (p : place_type) (t : trans_type) : option bool :=
    match pre spn t p with
    | None => Some true
    | Some (mk_nat_star weight _) =>
      match get_m spn.(marking) p with
      | Some nboftokens => Some (weight <=? nboftokens)
      | None => None
      end
    end.

  Functional Scheme check_pre_ind := Induction for check_pre Sort Prop.
  
  Theorem check_pre_correct :
    forall (spn : SPN) (p : place_type) (t : trans_type) (optb : option bool),
      check_pre spn p t = optb -> CheckPre spn p t optb.
  Proof.
    intros spn p t; functional induction (check_pre spn p t) using check_pre_ind; intros.
    - rewrite <- H; apply CheckPre_cons_some with (is_positive := _x);
        [auto | apply get_m_correct; assumption].
    - rewrite <- H; apply CheckPre_err with (weight := weight) (is_positive := _x);
        [auto | apply get_m_correct; assumption].
    - rewrite <- H; apply CheckPre_cons_none; assumption.
  Qed.
  
  Inductive MapCheckPreAux
            (spn : SPN)
            (t : trans_type) :
    list place_type -> option bool -> Prop :=
  | MapCheckPreAux_true :
      forall (pre_places : list trans_type),
        (forall p : place_type, In p pre_places -> CheckPre spn p t (Some true)) ->
        MapCheckPreAux spn t pre_places (Some true)
  | MapCheckPreAux_false :
      forall (pre_places : list trans_type),
        (exists p : place_type, In p pre_places -> CheckPre spn p t (Some false)) ->
        MapCheckPreAux spn t pre_places (Some false)
  | MapCheckPreAux_err :
      forall (pre_places : list trans_type),
        (exists p : place_type, In p pre_places -> CheckPre spn p t None) ->
        MapCheckPreAux spn t pre_places None.
  
  (** Function : Returns [Some true] if ∀ p ∈ [pre_places], M(p) >= pre(p, t).
                 
                 Raises an error if [get_m] fails. *)
  
  Fixpoint map_check_pre_aux
           (spn : SPN)
           (t : trans_type)
           (pre_places : list place_type)
           (check_result : bool) {struct pre_places} : option bool :=
    match pre_places with
    | p :: tail =>
      match check_pre spn p t with
      | None => None
      | Some b =>
        map_check_pre_aux spn t tail (b && check_result)
      end 
    | [] => Some check_result
    end.  

  (** Function : Wrapper around [map_check_pre_aux]. *)
  
  Definition map_check_pre (spn : SPN) (pre_places : list place_type) (t : trans_type) : option bool :=
    map_check_pre_aux spn t pre_places true.
  

  (** Function : Returns [Some true] if M(p) >= test(p, t), [Some false] otherwise. 
                 
                 Raises an error (i.e. None) if [get_m] fail.
   *)
  
  Definition check_test (spn : SPN) (p : place_type) (t : trans_type) : option bool :=
    match test spn t p with
    | None => Some true
    | Some (mk_nat_star weight _) =>
      match get_m spn.(marking) p with
      | Some nboftokens => Some (weight <=? nboftokens)
      | None => None
      end
    end.

  (** Function : Returns [Some true] if ∀ p ∈ [test_places], M(p) >= test(p, t).
                 
                 Raises an error if [get_m] fails.
   *)
  
  Fixpoint map_check_test_aux
           (spn : SPN)
           (t : trans_type)
           (test_places : list place_type)
           (check_result : bool) {struct test_places} : option bool :=
    match test_places with
    | p :: tail =>
      match check_test spn p t with
      | None => None
      | Some b =>
        map_check_test_aux spn t tail (b && check_result)
      end 
    | [] => Some check_result
    end.  

  (** Function : Returns [Some true] if ∀ p ∈ test places of t, M(p) >= test(p, t) 
                 
                 Raises an error if [get_neighbours] or [check_test_aux] fail.
   *)
  
  Definition map_check_test (spn : SPN) (test_places : list place_type) (t : trans_type) : option bool :=
    map_check_test_aux spn t test_places true.

  (** Function : Returns [Some true] if M(p) >= inhib(p, t), [Some false] otherwise. 
                 
                 Raises an error (i.e. None) if [get_m] fail.
   *)
  
  Definition check_inhib (spn : SPN) (p : place_type) (t : trans_type) : option bool :=
    match inhib spn t p with
    | None => Some true
    | Some (mk_nat_star weight _) =>
      match get_m spn.(marking) p with
      | Some nboftokens => Some (weight <=? nboftokens)
      | None => None
      end
    end.

  (** Function : Returns [Some true] if ∀ p ∈ [inhib_places], M(p) >= inhib(p, t).
                 
                 Raises an error if [get_m] fails.
   *)
  
  Fixpoint map_check_inhib_aux
           (spn : SPN)
           (t : trans_type)
           (inhib_places : list place_type)
           (check_result : bool) {struct inhib_places} : option bool :=
    match inhib_places with
    | p :: tail =>
      match check_inhib spn p t with
      | None => None
      | Some b =>
        map_check_inhib_aux spn t tail (b && check_result)
      end 
    | [] => Some check_result
    end.  

  (** Function : Returns [Some true] if ∀ p ∈ inhib places of t, M(p) >= inhib(p, t) 
                 
                 Raises an error if [get_neighbours] or [check_inhib_aux] fail.
   *)
  
  Definition map_check_inhib (spn : SPN) (inhib_places : list place_type) (t : trans_type) : option bool :=
    map_check_inhib_aux spn t inhib_places true.
  
End Edges.

