Require Export HilecopTactics. 

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

(*===================================================================*)
(*=== TYPES FOR GENERALIZED, EXTENDED AND SYNCHRONOUS PETRI NETS. ===*)
(*===================================================================*)

(* A place is identified by an index which is unique. *)
Definition place_type := nat.

(* A transition is identified by an index which is unique. *)
Definition trans_type := nat.

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
Definition marking_type := list (place_type * nat).

(* Defines a structure containing multiple list of places
 * correspond to pre, test, inhib and post neighbour places
 * which will be associated with a transition t (see the lneighbours
 * attribute in the SPN Structure).
 *)
Structure neighbours_type : Set := mk_neighbours {
                                       pre_pl : list place_type;
                                       test_pl : list place_type;
                                       inhib_pl : list place_type;
                                       post_pl : list place_type
                                     }.

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
       * Defines priority relations between transitions,
       * necessary to obtain a deterministic Petri net.*)
      priority_groups : list (list trans_type);

      (* Contains the list of pre, test, inhib and post places 
       * associated with each transition of the SPN. *)
      lneighbours : list (trans_type * neighbours_type);
      
    }.

(*********** HELPERS DEFINITIONS *********)

Definition MarkingHaveSameStruct
           (m1 : marking_type)
           (m2 : marking_type) := fst (split m1) = fst (split m2).

Definition PlaceIsRefInNeighbours
           (p : place_type)
           (neighbours : neighbours_type) :=
  In p neighbours.(pre_pl) \/
  In p neighbours.(test_pl) \/
  In p neighbours.(inhib_pl) \/
  In p neighbours.(post_pl).

(*==============================================*)
(*============ PROPERTIES ON SPN ===============*)
(*==============================================*)

(*** Properties on places and transitions ***)

Definition NoDupPlaces (spn : SPN) := NoDup spn.(places).  
Definition NoDupTranss (spn : SPN) := NoDup spn.(transs).

(*** Properties on priority_groups ***)

(* For all transition t, t is in spn.(transs) iff 
 * there exists a group in spn.(priority_groups) containing t. *)
Definition NoUnknownInPriorityGroups (spn : SPN) :=
  spn.(transs) = concat spn.(priority_groups).

(* For all transition t in one of the group of
 * priority_groups, t is contained in only one
 * group of priority_groups. *)
Definition NoIntersectInPriorityGroups (spn : SPN) :=
  forall (group group' : list trans_type),
    (In group spn.(priority_groups) /\
     In group' spn.(priority_groups) /\
     group <> group') ->
    (forall t : trans_type, In t group -> ~In t group').

(*** Properties on lneighbours ***)
Definition NoDupLneighbours (spn : SPN) := NoDup spn.(lneighbours).

(* For all place p, p is in places iff 
 * p is in the neighbourhood of at least one transition. *)
Definition NoIsolatedPlace (spn : SPN) := 
  forall p : place_type,
    In p spn.(places) ->
    exists (neighbours_of_t : (trans_type * neighbours_type)),
      In neighbours_of_t spn.(lneighbours) /\  
      (In p (snd neighbours_of_t).(pre_pl) \/
       In p (snd neighbours_of_t).(test_pl) \/
       In p (snd neighbours_of_t).(inhib_pl) \/
       In p (snd neighbours_of_t).(post_pl)).

(* Forall neighbours_of_t in spn.lneighbours 
 * if place p is in neighbours_of_t then
 * p is in spn.places.
 *)
Definition NoUnknownPlaceInNeighbours (spn : SPN) :=
  forall (neighbours_of_t : (trans_type * neighbours_type)),
    In neighbours_of_t spn.(lneighbours) ->  
    (forall (p : place_type),
        (In p (snd neighbours_of_t).(pre_pl) \/
         In p (snd neighbours_of_t).(test_pl) \/
         In p (snd neighbours_of_t).(inhib_pl) \/
         In p (snd neighbours_of_t).(post_pl)) ->
        In p spn.(places)).

(* For all transition t, t is in spn.transs iff 
 * t is referenced in spn.lneighbours. *)
Definition NoUnknownTransInLNeighbours (spn : SPN) (t : trans_type) :=
  spn.(transs) = fst (split spn.(lneighbours)).

(* Forall neighbours_of_t in spn.lneighbours 
 * there exists one list of places that is not empty.
 * i.e. A transition has at least one neighbour place.
 *)
Definition NoIsolatedTrans (spn : SPN) :=
  forall (neighbours_of_t : (trans_type * neighbours_type)),
    In neighbours_of_t spn.(lneighbours) ->
    ((snd neighbours_of_t).(pre_pl) <> [] \/
     (snd neighbours_of_t).(test_pl) <> [] \/
     (snd neighbours_of_t).(inhib_pl) <> [] \/
     (snd neighbours_of_t).(post_pl) <> []).

(*** Properties on marking ***)
Definition NoDupMarking (spn : SPN) := NoDup spn.(marking).

(* For all place (pl i), (pl i) is in places if
 * (pl i) is referenced in marking. *)
Definition NoUnmarkedPlace (spn : SPN)  :=
  spn.(places) = (fst (split spn.(marking))).



(*===============================================*)
(*===== EQUALITY DECIDABILITY FOR SPN TYPES =====*)
(*===============================================*)

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
  Fixpoint get_m (marking : marking_type) (p : place_type) : option nat :=
    match marking with
    | (place, nboftokens) :: tail => if p =? place then
                                       Some nboftokens
                                     else get_m tail p
    (* Exception : index is not in marking. *)
    | [] => None
    end.

  Functional Scheme get_m_ind := Induction for get_m Sort Prop.

  (*** Formal specification for get_m ***)
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

  (*** Correctness proof : get_m ***)
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

  (*** Completeness proof : get_m ***)
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

  (*** Formal specification : replace_occ ***)
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

  (*** Correctness proof : replace_occ ***)
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

  (*** Completeness proof : replace_occ ***)
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

  (* Auxiliary lemma to prove replace_occ_nodup. *)
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

  (* Auxiliary lemma to prove replace_occ_nodup. *)
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

  (*** Forall list l, if NoDup l then NoDup (replace_occ l) ***)
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

  (* Lemma : Proves that replace_occ preserves structure
   *         of a marking m passed as argument when 
   *         (fst occ) = (fst repl).
   *)
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
      rewrite fst_split_app.
      symmetry.
      rewrite fst_split_app.
      rewrite IHl.
      simpl.
      auto.
    (* Case (p, n) not hd of list. *)
    - rewrite fst_split_app.
      symmetry.
      rewrite fst_split_app.
      rewrite IHl.
      auto.
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
    match nboftokens with
    | None => Some m
    | Some (mk_nat_star n' _) =>
      let opt_n := get_m m p in
      match opt_n with
      (* The couple (i, n) to remove must be unique. *)
      | Some n =>
        Some (replace_occ prodnat_eq_dec (p, n) (p, (op n n')) m)
      (* If couple with first member i doesn't exist
       * in m, then returns None (it's an exception). *)
      | None => None 
      end
    end.

  Functional Scheme modify_m_ind := Induction for modify_m Sort Prop.

  (*** Formal specification : modify_m ***)
  Inductive ModifyM
            (m : marking_type)
            (p : place_type)
            (op : nat -> nat -> nat) :
    option nat_star -> option marking_type -> Prop :=
  | ModifyM_tokens_none :
      ModifyM m p op None (Some m)
  (* Case place of index i is not in the marking,
   * which is a exception case. *)
  | ModifyM_err :
      forall (n : nat_star),
        GetM m p None ->
        ModifyM m p op (Some n) None
  (* Case place of index i exists in the marking *)
  | ModifyM_some_repl :
      forall (nboftokens : option nat_star)
             (n n' : nat)
             (is_positive : n' > 0)
             (m' : marking_type),
        nboftokens = Some (mk_nat_star n' is_positive) ->
        GetM m p (Some n) ->
        ReplaceOcc prodnat_eq_dec (p, n) (p, (op n n')) m m' ->
        ModifyM m p op nboftokens (Some m').

  (*** Correctness proof : modify_m ***)
  Theorem modify_m_correct :
    forall (m : marking_type)
           (optionm : option marking_type)
           (p : place_type)
           (op : nat -> nat -> nat)
           (nboftokens : option nat_star),
      modify_m m p op nboftokens = optionm -> ModifyM m p op nboftokens optionm.
  Proof.
    do 5 intro; functional induction (modify_m m p op nboftokens)
                           using modify_m_ind; intros.
    (* Case (pl i) exists in marking m *)
    - rewrite <- H. apply ModifyM_some_repl with (n := n0)
                                                 (n' := n')
                                                 (is_positive := _x).
      + auto.
      + apply get_m_correct in e1; auto.
      + apply replace_occ_correct; auto.
    (* Case (pl i) doesn't exist in marking m (error) *)
    - rewrite <- H. apply ModifyM_err.
      + apply get_m_correct; auto.
    (* Case nboftokens is None *)
    - rewrite <- H; apply ModifyM_tokens_none.
  Qed.

  (*** Completeness proof : modify_m ***)
  Theorem modify_m_compl :
    forall (m : marking_type)
           (optionm : option marking_type)
           (p : place_type)
           (op : nat -> nat -> nat)
           (nboftokens : option nat_star),
      ModifyM m p op nboftokens optionm -> modify_m m p op nboftokens = optionm.
  Proof.
    intros; induction H.
    (* Case  ModifyM_tokens_none *)
    - simpl; auto.
    (* Case ModifyM_err *)
    - unfold modify_m; elim n; intros.
      apply get_m_compl in H; rewrite H; auto.
    (* Case ModifyM_some_repl *)
    - unfold modify_m; rewrite H; apply get_m_compl in H0; rewrite H0.
      apply replace_occ_compl in H1; rewrite H1; auto.      
  Qed.

  (* Lemma : Proves that modify_m conserves
   *         the structure of the marking m
   *         passed as argument.  
   *)
  Lemma modify_m_same_struct :
    forall (m m' : marking_type)
           (p : place_type)
           (op : nat -> nat -> nat)
           (nboftokens : option nat_star),
      modify_m m p op nboftokens = Some m' ->
      MarkingHaveSameStruct m m'.
  Proof.
    do 5 intro.
    functional induction (modify_m m p op nboftokens)
               using modify_m_ind;
      intros.
    - injection H; intros.
      rewrite <- H0.
      unfold MarkingHaveSameStruct; symmetry.
      apply replace_occ_same_struct.
    - inversion H.
    - injection H; intros.
      rewrite H0.
      unfold MarkingHaveSameStruct; auto.
  Qed.
  
  (* Lemma : For all spn, and marking "some_marking", 
   *         (modify_m some_marking (pl i) op nboftokens) returns no error
   *         if (pl i) is in the list of places spn.(places) and if
   *         some_marking verifies properties regarding spn.(marking).
   *)
  Lemma modify_m_no_error :
    forall (nboftokens : option nat_star)
           (some_marking : marking_type)
           (op : nat -> nat -> nat)
           (p : place_type),
      In p (fst (split some_marking)) ->
      exists v : marking_type,
        modify_m some_marking p op nboftokens = Some v.
  Proof.
    intros.
    functional induction (modify_m some_marking p op nboftokens)
               using modify_m_ind.    
    (* Base case *)
    - exists (replace_occ prodnat_eq_dec (p, n0) (p, op n0 n') some_marking).
      auto.
    (* Case get_m = None, not possible. *)
    - apply get_m_no_error in H.
      elim H; intros.
      rewrite H0 in e1.
      inversion e1.
    (* Case nboftokens = None *)
    - exists some_marking; auto.    
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
  Inductive UpdateMarkingPre
            (t : trans_type)
            (pre : weight_type)
            (m : marking_type) :
    list place_type -> option marking_type -> Prop :=
  | UpdateMarkingPre_nil :
      UpdateMarkingPre t pre m [] (Some m)
  | UpdateMarkingPre_some :
      forall (places : list place_type)
             (m' : marking_type)
             (optionm : option marking_type)
             (p : place_type),
        ModifyM m p Nat.sub (pre t p) (Some m') ->
        UpdateMarkingPre t pre m' places optionm ->
        UpdateMarkingPre t pre m (p :: places) optionm
  | UpdateMarkingPre_err :
      forall (p : place_type) (places : list place_type),
        ModifyM m p Nat.sub (pre t p) None ->
        UpdateMarkingPre t pre m (p :: places) None.

  (*** Correctness proof : update_marking_pre ***)
  Theorem update_marking_pre_correct :
    forall (t : trans_type)
           (pre : weight_type)
           (places : list place_type)
           (m : marking_type)
           (optionm : option marking_type),
      update_marking_pre t pre m places = optionm ->
      UpdateMarkingPre t pre m places optionm.
  Proof.
    intros t pre places m optionm;
      functional induction (update_marking_pre t pre m places)
                 using update_marking_pre_ind;
      intros.
    (* Case places is nil *)
    - rewrite <- H; apply UpdateMarkingPre_nil.
    (* Case p is referenced in m *)
    - apply UpdateMarkingPre_some with (m' := m').
      + apply modify_m_correct; auto.
      + apply IHo; auto.
    (* Case p is not in m *)
    - rewrite <- H; apply UpdateMarkingPre_err;
        [apply modify_m_correct; auto].      
  Qed.

  (*** Completeness proof : update_marking_pre ***)
  Theorem update_marking_pre_compl :
    forall (t : trans_type)
           (pre : weight_type)
           (places : list place_type)
           (m : marking_type)
           (optionm : option marking_type),
      UpdateMarkingPre t pre m places optionm ->
      update_marking_pre t pre m places = optionm.
  Proof.
    intros t pre places m optionm Hspec; induction Hspec.
    (* Case UpdateMarkingPre_nil *)
    - simpl; auto.
    (* Case UpdateMarkingPre_some *)
    - simpl; apply modify_m_compl in H; rewrite H; rewrite IHHspec; auto.
    (* Case UpdateMarkingPre_err *)
    - simpl; apply modify_m_compl in H; rewrite H; auto.
  Qed.
  
  (* Lemma : Proves that update_marking_pre returns no error 
   *         if all places of the list passed as argument
   *         are referenced in the marking (also passed as argument).
   *)
  Lemma update_marking_pre_no_error :
    forall (t : trans_type)
           (pre : weight_type)
           (some_places : list place_type)
           (some_marking : marking_type),
      (forall p : place_type, In p some_places -> In p (fst (split some_marking))) ->
      exists v : marking_type,
        update_marking_pre t pre some_marking some_places = Some v.
  Proof.
    intros t pre some_places some_marking p;
      functional induction (update_marking_pre t pre some_marking some_places)
                 using update_marking_pre_ind;
      intros.
    (* Base case, some_places = []. *)
    - exists m; auto.
    (* Case modify_m returns some marking. *)
    - apply IHo; intros.
      apply (in_cons p0) in H.
      apply p in H.
      apply modify_m_same_struct in e0.
      unfold MarkingHaveSameStruct in e0.
      rewrite <- e0.
      auto.
    (* Case modify_m returns None, 
     * impossible regarding the hypothesis 
     *)
    - cut (In p0 (p0 :: tail)).
      + intro.
        apply p in H.
        apply modify_m_no_error with (nboftokens := (pre t p0))
                                     (op := Nat.sub) in H.
        elim H; intros.
        rewrite e0 in H0.
        inversion H0.
      + apply in_eq.
  Qed.
  
  (* Lemma : Proves that update_marking_pre preserves
   *         the structure of the marking m
   *         passed as argument. 
   *)
  Lemma update_marking_pre_same_struct :
    forall (t : trans_type)
           (pre : weight_type)
           (places : list place_type)
           (m m' : marking_type),
      update_marking_pre t pre m places = Some m' ->
      MarkingHaveSameStruct m m'.
  Proof.
    intros t pre places m m'.
    functional induction (update_marking_pre t pre m places)
               using update_marking_pre_ind;
      intros.
    - injection H; intros.
      rewrite H0.
      unfold MarkingHaveSameStruct; auto.
    - apply IHo in H.
      apply modify_m_same_struct in e0.
      unfold MarkingHaveSameStruct.
      unfold MarkingHaveSameStruct in e0.
      unfold MarkingHaveSameStruct in H.
      rewrite <- H; rewrite e0; auto.
    - inversion H.    
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
  Inductive UpdateMarkingPost
            (t : trans_type)
            (post : weight_type)
            (m : marking_type) :
    list place_type -> option marking_type -> Prop :=
  | UpdateMarkingPost_nil :
      UpdateMarkingPost t post m [] (Some m)
  | UpdateMarkingPost_some :
      forall (p : place_type)
             (m' : marking_type)
             (optionm : option marking_type)
             (places : list place_type),
        ModifyM m p Nat.add (post t p) (Some m') ->
        UpdateMarkingPost t post m' places optionm ->
        UpdateMarkingPost t post m (p :: places) optionm
  | UpdateMarkingPost_err :
      forall (p : place_type)
             (places : list place_type),
        ModifyM m p Nat.add (post t p) None ->
        UpdateMarkingPost t post m (p :: places) None.

  (*** Correctness proof : update_marking_post ***)
  Theorem update_marking_post_correct :
    forall (t : trans_type)
           (post : weight_type)
           (places : list place_type)
           (m : marking_type)
           (optionm : option marking_type),
      update_marking_post t post m places = optionm ->
      UpdateMarkingPost t post m places optionm.
  Proof.
    intros t post places m optionm;
      functional induction (update_marking_post t post m places)
                 using update_marking_post_ind;
      intros.
    (* Case places is nil *)
    - rewrite <- H; apply UpdateMarkingPost_nil.
    (* Case p is referenced in m. *)
    - apply UpdateMarkingPost_some with (m' := m').
      + apply modify_m_correct; auto.
      + apply (IHo H); auto.
    (* Case p not referenced in m, error! *)
    - rewrite <- H;
        apply UpdateMarkingPost_err;
        apply modify_m_correct; auto.
  Qed.

  (*** Completeness proof : update_marking_post ***)
  Theorem update_marking_post_compl :
    forall (t : trans_type)
           (post : weight_type)
           (places : list place_type)
           (m : marking_type)
           (optionm : option marking_type),
      UpdateMarkingPost t post m places optionm ->
      update_marking_post t post m places = optionm.
  Proof.
    intros t post places m optionm H; elim H; intros.
    (* Case UpdateMarkingPost_nil *)
    - simpl; auto.
    (* Case UpdateMarkingPost_some *)
    - simpl; apply modify_m_compl in H0; rewrite H0; auto.
    (* Case UpdateMarkingPost_err *)
    - simpl; apply modify_m_compl in H0; rewrite H0; auto.
  Qed.

  (* Lemma : Proves that update_marking_pre returns no error 
   *         if all places of the list passed as argument
   *         are referenced in the marking (also passed as argument).
   *)
  Lemma update_marking_post_no_error :
    forall (t : trans_type)
           (post : weight_type)
           (some_places : list place_type)
           (some_marking : marking_type),
      (forall p : place_type, In p some_places -> In p (fst (split some_marking))) ->
      exists v : marking_type,
        update_marking_post t post some_marking some_places = Some v.
  Proof.
    intros t post some_places some_marking p;
      functional induction (update_marking_post t post some_marking some_places)
                 using update_marking_post_ind;
      intros.
    (* Base case, some_places = []. *)
    - exists m; auto.
    (* Case modify_m returns some marking. *)
    - apply IHo; intros.
      apply (in_cons p0) in H.
      apply p in H.
      apply modify_m_same_struct in e0.
      unfold MarkingHaveSameStruct in e0.
      rewrite <- e0.
      auto.
    (* Case modify_m returns None, 
     * impossible regarding the hypothesis 
     *)
    - cut (In p0 (p0 :: tail)).
      + intro.
        apply p in H.
        apply modify_m_no_error with (nboftokens := (post t p0))
                                     (op := Nat.add) in H.
        elim H; intros.
        rewrite e0 in H0.
        inversion H0.
      + apply in_eq.
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
    | p :: tail => match pre_or_test_arcs_t p with
                   (* If there is no pre or test edge between p and t. *)
                   | None => check_pre_or_test pre_or_test_arcs_t m tail check_result
                   (* Else some pre or test edge exists. *)
                   | Some (mk_nat_star edge_weight _) =>
                     (* Retrieves the number of tokens associated 
                      * with place p. *)
                     match get_m m p with
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
  Inductive CheckPreOrTest
            (pre_or_test_arcs_t : place_type -> option nat_star)
            (m : marking_type) :
    list place_type -> bool -> option bool -> Prop :=
  | CheckPreOrTest_nil :
      forall (b : bool),
        CheckPreOrTest pre_or_test_arcs_t m [] b (Some b)
  | CheckPreOrTest_edge_none :
      forall (places : list place_type)
             (p : place_type)
             (check_result : bool)
             (optionb : option bool),
        pre_or_test_arcs_t p = None ->
        CheckPreOrTest pre_or_test_arcs_t m places check_result optionb ->
        CheckPreOrTest pre_or_test_arcs_t m (p :: places) check_result optionb
  | CheckPreOrTest_err :
      forall (places : list place_type)
             (p : place_type)
             (edge_weight : nat)
             (check_result : bool)
             (is_positive : edge_weight > 0),
        pre_or_test_arcs_t p = Some (mk_nat_star edge_weight is_positive) ->
        GetM m p None ->
        CheckPreOrTest pre_or_test_arcs_t m (p :: places) check_result None
  | CheckPreOrTest_tokens_some :
      forall (places : list place_type) 
             (n edge_weight : nat)
             (p : place_type)
             (is_positive : edge_weight > 0)
             (check_result : bool)
             (optionb : option bool),
        pre_or_test_arcs_t p = Some (mk_nat_star edge_weight is_positive) ->
        GetM m p (Some n) ->
        CheckPreOrTest pre_or_test_arcs_t m places ((edge_weight <=? n) && check_result)
                       optionb ->
        CheckPreOrTest pre_or_test_arcs_t m (p :: places) check_result optionb.

  (*** Correctness proof : check_pre_or_test ***)
  Theorem check_pre_or_test_correct :
    forall (pre_or_test_arcs_t : place_type -> option nat_star)
           (m : marking_type)
           (places : list place_type)
           (check_result : bool)
           (optionb : option bool),
      check_pre_or_test pre_or_test_arcs_t m places check_result = optionb ->
      CheckPreOrTest pre_or_test_arcs_t m places check_result optionb.
  Proof.
    intros pre_or_test_arcs_t m places check_result optionb;
      functional induction (check_pre_or_test pre_or_test_arcs_t m places check_result)
                 using check_pre_or_test_ind;
      intros.
    (* Case places = [] *)
    - rewrite <- H; apply CheckPreOrTest_nil.
    (* Case edge and tokens exist *)
    - apply CheckPreOrTest_tokens_some with (p := p)
                                            (n := n0)
                                            (edge_weight := edge_weight)
                                            (is_positive := _x).
      + rewrite e0; auto.
      + apply get_m_correct; auto.
      + apply IHo; auto. 
    (* Case of error, get_m returns None *)
    - rewrite <- H; apply CheckPreOrTest_err with (p := p)
                                                  (edge_weight := edge_weight)
                                                  (is_positive := _x).
      + rewrite e0; auto.
      + apply get_m_correct; auto.
    (* Case edge doesn't exist *)
    - apply CheckPreOrTest_edge_none.
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
      CheckPreOrTest pre_or_test_arcs_t m places check_result optionb ->
      check_pre_or_test pre_or_test_arcs_t m places check_result = optionb.
  Proof.
    intros pre_or_test_arcs_t m places check_result optionb H; induction H.
    (* Case CheckPreOrTest_nil *)
    - simpl; auto.
    (* Case CheckPreOrTest_edge_none *)
    - simpl; rewrite H; auto.
    (* Case CheckPreOrTest_err *)
    - simpl; rewrite H; apply get_m_compl in H0; rewrite H0; auto.
    (* Case CheckPreOrTest_tokens_some *)
    - simpl; rewrite H; apply get_m_compl in H0; rewrite H0; auto.
  Qed.

  (* Lemma : Proves that check_pre_or_test returns no error if
   *         the places in list places are referenced in marking m.
   *
   *)
  Lemma check_pre_or_test_no_error :
    forall (pre_or_test_arcs_t : place_type -> option nat_star)
           (m : marking_type)
           (places : list place_type)
           (check_result : bool),
      (forall p : place_type, In p places -> In p (fst (split m))) ->
      exists v : bool,
        check_pre_or_test pre_or_test_arcs_t m places check_result = Some v.
  Proof.
    intros pre_or_test_arcs_t m places check_result.
    functional induction (check_pre_or_test pre_or_test_arcs_t m places check_result)
               using check_pre_or_test_ind;
      intros.
    (* Base case, places = [] *)
    - exists check_result; auto.
    (* Case get_m = Some v *)
    - apply IHo; intros.
      apply (in_cons p) in H0.
      apply H in H0.
      auto.
    (* Case get_m = None, impossible regarding the  
     * hypothesis.
     *)
    - cut (In p (p :: tail)).
      + intro.
        apply H in H0.
        apply get_m_no_error in H0.
        elim H0; intros.
        rewrite e2 in H1; inversion H1.
      + apply in_eq.
    (* Case pre_or_test_arcs_t = None. *)
    - apply IHo; intros.
      apply (in_cons p) in H0.
      apply H in H0.
      auto.
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
    | p :: tail => match inhib_arcs_t p with
                   (* If there is inhib edge between (pl i) and t. *)
                   | None => check_inhib inhib_arcs_t m tail check_result
                   (* Else some inhib edge exists. *)
                   | Some (mk_nat_star edge_weight _) =>
                     match get_m m p with
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
  Inductive CheckInhib
            (inhib_arcs_t : place_type -> option nat_star)
            (m : marking_type) :
    list place_type -> bool -> option bool -> Prop :=
  | CheckInhib_nil :
      forall (b : bool),
        CheckInhib inhib_arcs_t m [] b (Some b)
  | CheckInhib_edge_none :
      forall (places : list place_type)
             (p : place_type)
             (check_result : bool)
             (optionb : option bool),
        inhib_arcs_t p = None ->
        CheckInhib inhib_arcs_t m places check_result optionb->
        CheckInhib inhib_arcs_t m (p :: places) check_result optionb
  | CheckInhib_err :
      forall (places : list place_type)
             (p : place_type)
             (edge_weight : nat)
             (is_positive : edge_weight > 0)
             (check_result : bool),
        inhib_arcs_t p = Some (mk_nat_star edge_weight is_positive) ->
        GetM m p None ->
        CheckInhib inhib_arcs_t m (p :: places) check_result None
  | CheckInhib_tokens_some :
      forall (places : list place_type)
             (p : place_type)
             (n edge_weight : nat)
             (is_positive : edge_weight > 0)
             (check_result : bool)
             (optionb : option bool),
        inhib_arcs_t p = Some (mk_nat_star edge_weight is_positive) ->
        GetM m p (Some n) ->
        CheckInhib inhib_arcs_t m places (check_result && (n <? edge_weight)) optionb ->
        CheckInhib inhib_arcs_t m (p :: places) check_result optionb.

  (*** Correctness proof : check_inhib ***)
  Theorem check_inhib_correct :
    forall (inhib_arcs_t : place_type -> option nat_star)
           (m : marking_type)
           (places : list place_type)
           (check_result : bool)
           (optionb : option bool),
      check_inhib inhib_arcs_t m places check_result = optionb ->
      CheckInhib inhib_arcs_t m places check_result optionb.
  Proof.
    intros inhib_arcs_t m places check_result optionb;
      functional induction (check_inhib inhib_arcs_t m places check_result)
                 using check_inhib_ind;
      intros.
    (* Case places = [] *)
    - rewrite <- H; apply CheckInhib_nil.
    (* Case edge and tokens exist *)
    - apply CheckInhib_tokens_some with (p := p)
                                        (n := n0)
                                        (edge_weight := edge_weight)
                                        (is_positive := _x).
      + rewrite e0; auto.
      + apply get_m_correct; auto.
      + apply IHo; auto.
    (* Case edge exists but no tokens, case of error! *)
    - rewrite <- H; apply CheckInhib_err with (p := p)
                                              (edge_weight := edge_weight)
                                              (is_positive := _x).
      + rewrite e0; auto.
      + apply get_m_correct; auto.
    (* Case edge doesn't exist *)
    - apply CheckInhib_edge_none.
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
      CheckInhib inhib_arcs_t m places check_result optionb ->
      check_inhib inhib_arcs_t m places check_result = optionb.
  Proof.
    intros inhib_arcs_t m places check_result optionb H; induction H.
    (* Case CheckInhib_nil *)
    - simpl; auto.
    (* Case CheckInhib_edge_none *)
    - simpl; rewrite H; auto.
    (* Case CheckInhib_err *)
    - simpl; rewrite H; apply get_m_compl in H0; rewrite H0; auto.
    (* Case CheckInhib_tokens_some *)
    - simpl; rewrite H; apply get_m_compl in H0; rewrite H0; auto.
  Qed.

  (* Lemma : Proves that check_inhib returns no error if
   *         the places in list places are referenced in marking m.
   *
   *)
  Lemma check_inhib_no_error :
    forall (inhib_arcs_t : place_type -> option nat_star)
           (m : marking_type)
           (places : list place_type)
           (check_result : bool),
      (forall p : place_type, In p places -> In p (fst (split m))) ->
      exists v : bool,
        check_inhib inhib_arcs_t m places check_result = Some v.
  Proof.
    intros inhib_arcs_t m places check_result.
    functional induction (check_inhib inhib_arcs_t m places check_result)
               using check_inhib_ind;
      intros.
    (* Base case, places = [] *)
    - exists check_result; auto.
    (* Case get_m = Some v *)
    - apply IHo; intros.
      apply (in_cons p) in H0.
      apply H in H0.
      auto.
    (* Case get_m = None, impossible regarding the  
     * hypothesis.
     *)
    - cut (In p (p :: tail)).
      + intro.
        apply H in H0.
        apply get_m_no_error in H0.
        elim H0; intros.
        rewrite e2 in H1; inversion H1.
      + apply in_eq.
    (* Case pre_or_test_arcs_t = None. *)
    - apply IHo; intros.
      apply (in_cons p) in H0.
      apply H in H0.
      auto.
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
  Inductive CheckAllEdges
            (neighbours_t : neighbours_type)
            (pre_arcs_t : place_type -> option nat_star)
            (test_arcs_t : place_type -> option nat_star)
            (inhib_arcs_t : place_type -> option nat_star)
            (steadym decreasingm : marking_type) : option bool -> Prop :=
  | CheckAllEdges_some :
      forall (check_pre_result check_test_result check_inhib_result : bool),
        CheckPreOrTest pre_arcs_t decreasingm (pre_pl neighbours_t) true (Some check_pre_result) /\
        CheckPreOrTest test_arcs_t steadym (test_pl neighbours_t) true (Some check_test_result) /\
        CheckInhib inhib_arcs_t steadym (inhib_pl neighbours_t) true (Some check_inhib_result) ->
        CheckAllEdges neighbours_t pre_arcs_t test_arcs_t inhib_arcs_t steadym decreasingm
                      (Some (check_pre_result && check_test_result && check_inhib_result))
  | CheckAllEdges_err :
      CheckPreOrTest pre_arcs_t decreasingm (pre_pl neighbours_t) true None \/
      CheckPreOrTest test_arcs_t steadym (test_pl neighbours_t) true None \/
      CheckInhib inhib_arcs_t steadym (inhib_pl neighbours_t) true None ->
      CheckAllEdges neighbours_t pre_arcs_t test_arcs_t inhib_arcs_t steadym decreasingm None.

  (*** Correctness proof : check_all_edges *)
  Theorem check_all_edges_correct :
    forall (neighbours_t : neighbours_type)
           (pre_arcs_t : place_type -> option nat_star)
           (test_arcs_t : place_type -> option nat_star)
           (inhib_arcs_t : place_type -> option nat_star)
           (steadym decreasingm : marking_type)
           (optionb : option bool),
      check_all_edges neighbours_t pre_arcs_t test_arcs_t inhib_arcs_t steadym decreasingm = optionb ->
      CheckAllEdges neighbours_t pre_arcs_t test_arcs_t inhib_arcs_t steadym decreasingm optionb.
  Proof.
    intros;
      functional induction (check_all_edges neighbours_t pre_arcs_t test_arcs_t inhib_arcs_t steadym decreasingm)
                 using check_all_edges_ind;
      intros.
    (* Case check_pre, check_test and check_inhib returned some value. *)
    - rewrite <- H; apply CheckAllEdges_some.
      split; [apply check_pre_or_test_correct; auto |
              split; [apply check_pre_or_test_correct; auto |
                      apply check_inhib_correct; auto]].            
    (* Case of error 1. check_inhib returns None. *)
    - rewrite <- H; apply CheckAllEdges_err.
      apply check_inhib_correct in e1; auto.
    (* Case of error 2. check_test returns None.  *)
    - rewrite <- H; apply CheckAllEdges_err.
      apply check_pre_or_test_correct in e0; auto.
    (* Case of error 3. check_pre returns None. *)
    - rewrite <- H; apply CheckAllEdges_err.
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
      CheckAllEdges neighbours_t pre_arcs_t test_arcs_t inhib_arcs_t steadym decreasingm optionb ->
      check_all_edges neighbours_t pre_arcs_t test_arcs_t inhib_arcs_t steadym decreasingm = optionb.
  Proof.
    intros. induction H.
    (* Case CheckAllEdges_some *)
    - unfold check_all_edges.
      elim H; clear H; intros.
      elim H0; clear H0; intros.
      repeat (((apply check_pre_or_test_compl in H; rewrite H) ||
               (apply check_pre_or_test_compl in H0; rewrite H0) ||
               (apply check_inhib_compl in H1; rewrite H1));
              auto).
    (* Case CheckAllEdges_err *)
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

  (* Lemma : Proves that check_all_edges returns no error if
   *         the places in (pre_pl neighbours_t), (inhib_pl neighbours_t) 
   *         and (test_pl neighbours_t) are referenced in markings steadym
   *         and decreasingm.  
   *
   *)
  Lemma check_all_edges_no_error :
    forall (neighbours_t : neighbours_type)
           (pre_arcs_t : place_type -> option nat_star)
           (test_arcs_t : place_type -> option nat_star)
           (inhib_arcs_t : place_type -> option nat_star)
           (steadym decreasingm : marking_type),
      (forall p : place_type,
          In p (pre_pl neighbours_t) -> In p (fst (split decreasingm))) ->
      (forall p : place_type,
          In p (test_pl neighbours_t) -> In p (fst (split steadym))) ->
      (forall p : place_type,
          In p (inhib_pl neighbours_t) -> In p (fst (split steadym))) ->
      exists v : bool,
        check_all_edges neighbours_t pre_arcs_t test_arcs_t inhib_arcs_t steadym decreasingm = Some v.
  Proof.
    do 6 intro.
    functional induction (check_all_edges neighbours_t
                                          pre_arcs_t test_arcs_t inhib_arcs_t
                                          steadym
                                          decreasingm)
               using check_all_edges_ind; intros.
    (* Case all went well. *)
    - exists (check_pre_result && check_test_result && check_inhib_result); auto.
    (* Case check_inhib = None, impossible regarding hypothesis. *)
    - apply check_inhib_no_error with (inhib_arcs_t := inhib_arcs_t)
                                      (check_result := true) in H1.
      elim H1; intros.
      rewrite e1 in H2; inversion H2.
    (* Case check_test = None, impossible regarding hypothesis. *)
    - apply check_pre_or_test_no_error with (pre_or_test_arcs_t := test_arcs_t)
                                            (check_result := true) in H0.
      elim H0; intros.
      rewrite e0 in H2; inversion H2.
    (* Case check_pre = None, impossible regarding hypothesis. *)
    - apply check_pre_or_test_no_error with (pre_or_test_arcs_t := pre_arcs_t)
                                            (check_result := true) in H.
      elim H; intros.
      rewrite e in H2; inversion H2.
  Qed.
  
End Edges.

(*==============================================================*)
(*================= FIRING ALGORITHM for SPN ===================*)
(*==============================================================*)

Section FireSpn.

  (*  
   * Function : Returns the element of type neighbours_type
   *            associated with transition t in the list lneighbours.
   *            
   *            Returns None if transition t is not referenced
   *            in lneighbours.
   *)
  Fixpoint get_neighbours
           (lneighbours : list (trans_type * neighbours_type))
           (t : trans_type) {struct lneighbours} : option neighbours_type :=
    match lneighbours with
    | (t', neighbours) :: tail => if t' =? t then
                                    Some neighbours
                                  else get_neighbours tail t
    | [] => None 
    end.

  (*** Formal specification : get_neighbours ***)
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
  
  (*** Correctness proof : get_neighbours ***)
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

  (*** Completeness proof : get_neighbours ***)
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

  (* Lemma : For all list of neighbours lneighbours 
   *         and transition t, (get_neighbours lneighbours t) 
   *         returns no error if t is referenced in lneighbours.
   **)
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
  
  (*  
   * Lemma : If get_neighbours returns some neighbours
   *         for a transition t and a list lneighbours, then
   *         the couple (t, neighbours) is in lneighbours. 
   *)
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
           (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)  
           (steadym : marking_type)
           (decreasingm : marking_type)
           (* "fired_pre_group" meant  to be empty at first *)
           (fired_pre_group pgroup : list trans_type) :
    option (list trans_type * marking_type) :=
    match pgroup with
    | t :: tail =>
      match get_neighbours lneighbours t with
      (* Checks neighbours of t. *)
      | Some neighbours_t =>
        (* If t is sensitized. *)
        match check_all_edges neighbours_t (pre t) (test t) (inhib t) steadym decreasingm with
        | Some true =>
          (* Updates the marking for the pre places neighbours of t. *)
          match update_marking_pre t pre decreasingm (pre_pl neighbours_t) with
          | Some marking' =>
            spn_fire_pre_aux lneighbours pre test inhib steadym marking' (fired_pre_group ++ [t]) tail
          (* Something went wrong, error! *)
          | None => None
          end
        (* Else no changes but inductive progress. *)
        | Some false =>
          spn_fire_pre_aux lneighbours pre test inhib steadym decreasingm fired_pre_group tail
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
  Inductive SpnFirePreAux
            (lneighbours : list (trans_type * neighbours_type))
            (pre test inhib : weight_type) 
            (steadym : marking_type) 
            (decreasingm : marking_type)
            (fired_pre_group : list trans_type) :
    list trans_type -> option (list trans_type * marking_type) -> Prop :=
  | SpnFirePreAux_nil :
      SpnFirePreAux lneighbours pre test inhib steadym decreasingm fired_pre_group []
                    (Some (fired_pre_group, decreasingm))
  (* Case get_neighbours returns an error. *)
  | SpnFirePreAux_neighbours_err :
      forall (t : trans_type) (pgroup : list trans_type),
        GetNeighbours lneighbours t None ->
        SpnFirePreAux lneighbours pre test inhib steadym decreasingm fired_pre_group (t :: pgroup) None
  (* Case check_all_edges returns an error. *)
  | SpnFirePreAux_edges_err :
      forall (t : trans_type) (pgroup : list trans_type) (neighbours_t : neighbours_type),
        GetNeighbours lneighbours t (Some neighbours_t) ->
        CheckAllEdges neighbours_t (pre t) (test t) (inhib t) steadym decreasingm None ->
        SpnFirePreAux lneighbours pre test inhib steadym decreasingm fired_pre_group (t :: pgroup) None
  (* Case check_all_edges returns false. *)
  | SpnFirePreAux_edges_false :
      forall (t : trans_type)
             (pgroup : list trans_type)
             (neighbours_t : neighbours_type)
             (option_final_couple : option (list trans_type * marking_type)),
        GetNeighbours lneighbours t (Some neighbours_t) ->
        CheckAllEdges neighbours_t (pre t) (test t) (inhib t) steadym decreasingm (Some false) ->
        SpnFirePreAux lneighbours pre test inhib steadym decreasingm fired_pre_group pgroup
                      option_final_couple ->
        SpnFirePreAux lneighbours pre test inhib steadym decreasingm fired_pre_group (t :: pgroup)
                      option_final_couple
  (* Case update_marking_pre returns an error. *)
  | SpnFirePreAux_update_err :
      forall (t : trans_type)
             (neighbours_t : neighbours_type)
             (pgroup : list trans_type),
        GetNeighbours lneighbours t (Some neighbours_t) ->
        CheckAllEdges neighbours_t (pre t) (test t) (inhib t) steadym decreasingm (Some true) ->
        UpdateMarkingPre t pre decreasingm (pre_pl neighbours_t) None ->
        SpnFirePreAux lneighbours pre test inhib steadym decreasingm fired_pre_group (t :: pgroup) None
  (* General case, all went well. *)
  | SpnFirePreAux_cons :
      forall (t : trans_type)
             (neighbours_t : neighbours_type)
             (pgroup : list trans_type)
             (modifiedm : marking_type)
             (option_final_couple : option (list trans_type * marking_type)),
        GetNeighbours lneighbours t (Some neighbours_t) ->
        CheckAllEdges neighbours_t (pre t) (test t) (inhib t) steadym decreasingm (Some true) ->
        UpdateMarkingPre t pre decreasingm (pre_pl neighbours_t) (Some modifiedm) ->
        SpnFirePreAux lneighbours pre test inhib steadym modifiedm (fired_pre_group ++ [t]) pgroup
                      option_final_couple ->
        SpnFirePreAux lneighbours pre test inhib steadym decreasingm fired_pre_group (t :: pgroup)
                      option_final_couple.
  
  (*** Correctness proof : spn_fire_pre_aux ***)
  Theorem spn_fire_pre_aux_correct :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type) 
           (steadym : marking_type) 
           (decreasingm : marking_type)
           (fired_pre_group : list trans_type)
           (pgroup : list trans_type)
           (option_final_couple : option (list trans_type * marking_type)),
      spn_fire_pre_aux lneighbours pre test inhib steadym decreasingm fired_pre_group pgroup = option_final_couple ->
      SpnFirePreAux lneighbours pre test inhib steadym decreasingm fired_pre_group pgroup option_final_couple.
  Proof.
    intros lneighbours pre test inhib steadym decreasingm fired_pre_group pgroup option_final_couple.
    functional induction (spn_fire_pre_aux lneighbours pre test inhib steadym decreasingm fired_pre_group pgroup)
               using spn_fire_pre_aux_ind; intros.
    (* Case pgroup = [] *)
    - rewrite <- H; apply SpnFirePreAux_nil.
    (* General case, all went well. *)
    - apply SpnFirePreAux_cons with (modifiedm := marking')
                                    (neighbours_t := neighbours_t).
      + apply get_neighbours_correct; auto.
      + apply check_all_edges_correct; auto.
      + apply update_marking_pre_correct; auto.
      + apply IHo; auto.
    (* Case update_marking_pre error. *)
    - rewrite <- H; apply SpnFirePreAux_update_err with (neighbours_t := neighbours_t).
      + apply get_neighbours_correct; auto.
      + apply check_all_edges_correct; auto.
      + apply update_marking_pre_correct; auto.
    (* Case check_all_edges returns false. *)
    - apply SpnFirePreAux_edges_false with (neighbours_t := neighbours_t).
      + apply get_neighbours_correct; auto.
      + apply check_all_edges_correct; auto.
      + apply IHo; auto.
    (* Case check_all_edges returns an error. *)
    - rewrite <- H; apply SpnFirePreAux_edges_err with (neighbours_t := neighbours_t).
      + apply get_neighbours_correct; auto.
      + apply check_all_edges_correct; auto.
    (* Case get_neighbours returns an error. *)
    - rewrite <- H; apply SpnFirePreAux_neighbours_err.
      apply get_neighbours_correct; auto.
  Qed.

  (*** Completeness proof : spn_fire_pre_aux ***)
  Theorem spn_fire_pre_aux_compl :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type) 
           (steadym : marking_type) 
           (decreasingm : marking_type)
           (fired_pre_group : list trans_type)
           (pgroup : list trans_type)
           (option_final_couple : option (list trans_type * marking_type)),
      SpnFirePreAux lneighbours pre test inhib steadym decreasingm fired_pre_group pgroup option_final_couple ->
      spn_fire_pre_aux lneighbours pre test inhib steadym decreasingm fired_pre_group pgroup = option_final_couple.
  Proof.
    intros lneighbours pre test inhib steadym decreasingm fired_pre_group
           pgroup option_final_couple Hspec.
    induction Hspec.
    (* Case SpnFirePreAux_nil *)
    - simpl; auto.
    (* Case SpnFirePreAux_neighbours_err *)
    - simpl; apply get_neighbours_compl in H; rewrite H; auto.
    (* Case SpnFirePreAux_edges_err *)
    - simpl.
      apply get_neighbours_compl in H; rewrite H.
      apply check_all_edges_compl in H0; rewrite H0; auto.
    (* Case SpnFirePreAux_edges_false *)
    - simpl.
      apply get_neighbours_compl in H; rewrite H.
      apply check_all_edges_compl in H0; rewrite H0; rewrite IHHspec; auto.
    (* Case SpnFirePreAux_update_err *)
    - simpl.
      apply get_neighbours_compl in H; rewrite H.
      apply check_all_edges_compl in H0; rewrite H0; auto.
      apply update_marking_pre_compl in H1; rewrite H1; auto.
    (* Case SpnFirePreAux_cons *)
    - simpl.
      apply get_neighbours_compl in H; rewrite H.
      apply check_all_edges_compl in H0; rewrite H0; auto.
      apply update_marking_pre_compl in H1; rewrite H1; auto.
  Qed.

  (* Lemma : spn_fire_pre_aux returns no error if 
   *         all transition t in pgroup are referenced in lneighbours
   *         and if all neighbour places referenced in lneighbours are
   *         referenced in the markings steadym and decreasingm. 
   *)
  Lemma spn_fire_pre_aux_no_error :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type) 
           (steadym : marking_type) 
           (decreasingm : marking_type)
           (fired_pre_group : list trans_type)
           (pgroup : list trans_type),
      (forall t : trans_type, In t pgroup -> In t (fst (split lneighbours))) ->
      (forall (t : trans_type) (neighbours : neighbours_type),
          In (t, neighbours) lneighbours ->
          ((forall p : place_type, In p neighbours.(pre_pl) -> In p (fst (split decreasingm))) /\
           (forall p : place_type, In p neighbours.(inhib_pl) -> In p (fst (split steadym))) /\
           (forall p : place_type, In p neighbours.(test_pl) -> In p (fst (split steadym))))) ->
      exists v : (list trans_type * marking_type),
        spn_fire_pre_aux lneighbours pre test inhib steadym decreasingm fired_pre_group pgroup = Some v.
  Proof.
    intros lneighbours pre test inhib steadym decreasingm
           fired_pre_group pgroup.
    functional induction (spn_fire_pre_aux lneighbours pre test inhib
                                           steadym decreasingm
                                           fired_pre_group pgroup)
               using spn_fire_pre_aux_ind;
      intros.
    (* Base case, pgroup = []. *)
    - exists (fired_pre_group, decreasingm); auto.
    (* Case check_all_edges = true. *)
    - apply IHo.
      + intros.
        apply (in_cons t) in H1.
        apply (H t0) in H1; auto.
      + intros.
        apply (H0 t0 neighbours) in H1.
        apply update_marking_pre_same_struct in e3.
        unfold MarkingHaveSameStruct in e3.
        rewrite <- e3; auto.
    (* Case update_marking_pre = None,
     * impossible regarding hypothesis.
     *)
    - cut (In t (t :: tail)); intros.
      + apply get_neighbours_in in e0.
        generalize ((H0 t neighbours_t) e0).
        intros.
        elim H2; intros.
        apply (update_marking_pre_no_error t pre (pre_pl neighbours_t) decreasingm) in H3.
        elim H3; intros.
        rewrite H5 in e3; inversion e3.
      + apply in_eq.
    (* Case check_all_edges = false. *)
    - apply IHo; intros.
      + apply (in_cons t) in H1; apply H in H1; auto.
      + apply H0 in H1; auto.
    (* Case check_all_edges = None, 
     * impossible regarding the hypotheses. 
     *)
    - cut (In t (t :: tail)); intros.
      + apply get_neighbours_in in e0.
        generalize ((H0 t neighbours_t) e0).
        intros.
        elim H2; intros; clear H2.
        elim H4; intros; clear H4.
        (* Applies check_all_edges_no_error to create a contradiction. *)
        apply (check_all_edges_no_error neighbours_t (pre t) (test t) (inhib t)
                                        steadym decreasingm H3 H5) in H2.
        elim H2; intros.
        rewrite H4 in e1.
        inversion e1.
      + apply in_eq.
    (* Case get_neighbours = None, 
     * impossible regarding the hypotheses.
     *)
    - cut (In t (t :: tail)); intros.
      + apply H in H1.
        apply get_neighbours_no_error in H1.
        elim H1; intros.
        rewrite H2 in e0; inversion e0.
      + apply in_eq.
  Qed.

  (* Lemma : Proves that spn_fire_pre_aux preserves
   *         the structure of the marking decreasingm
   *         passed as argument. 
   *)
  Lemma spn_fire_pre_aux_same_struct :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type) 
           (steadym : marking_type) 
           (decreasingm : marking_type)
           (fired_pre_group : list trans_type)
           (pgroup : list trans_type)
           (final_fire_pre_group : list trans_type)
           (finalm : marking_type),
      spn_fire_pre_aux lneighbours pre test inhib steadym decreasingm fired_pre_group pgroup =
      Some (final_fire_pre_group, finalm) ->
      MarkingHaveSameStruct decreasingm finalm.
  Proof.
    intros lneighbours pre test inhib steadym decreasingm fired_pre_group pgroup.
    functional induction (spn_fire_pre_aux lneighbours pre test inhib steadym decreasingm fired_pre_group pgroup)
               using spn_fire_pre_aux_ind;
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
  
  (*****************************************************)
  (*****************************************************)
  
  (*  
   * Function : Wrapper function around spn_fire_pre_aux.
   *)
  Definition spn_fire_pre
             (lneighbours : list (trans_type * neighbours_type))
             (pre test inhib : weight_type) 
             (steadym : marking_type) 
             (decreasingm : marking_type)
             (pgroup : list trans_type) : option (list trans_type * marking_type) :=
    spn_fire_pre_aux lneighbours pre test inhib steadym decreasingm [] pgroup.

  Functional Scheme spn_fire_pre_ind := Induction for spn_fire_pre Sort Prop.

  (*** Formal specification : spn_fire_pre ***)
  Inductive SpnFirePre
            (lneighbours : list (trans_type * neighbours_type))
            (pre test inhib : weight_type) 
            (steadym : marking_type) 
            (decreasingm : marking_type)
            (pgroup : list trans_type) : option (list trans_type * marking_type) -> Prop :=
  | SpnFirePre_cons :
      forall (option_final_couple : option (list trans_type * marking_type)),
        SpnFirePreAux lneighbours pre test inhib steadym decreasingm [] pgroup
                      option_final_couple ->
        SpnFirePre lneighbours pre test inhib steadym decreasingm pgroup
                   option_final_couple.

  (*** Correctness proof : spn_fire_pre ***)
  Theorem spn_fire_pre_correct :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type) 
           (steadym decreasingm : marking_type) 
           (pgroup : list trans_type)
           (option_final_couple : option (list trans_type * marking_type)),
      spn_fire_pre lneighbours pre test inhib steadym decreasingm pgroup = option_final_couple ->
      SpnFirePre lneighbours pre test inhib steadym decreasingm pgroup option_final_couple.
  Proof.
    intros lneighbours pre test inhib steadym decreasingm pgroup option_final_couple;
      functional induction (spn_fire_pre lneighbours pre test inhib steadym decreasingm pgroup)
                 using spn_fire_pre_ind; intros.
    apply SpnFirePre_cons; apply spn_fire_pre_aux_correct in H; auto.
  Qed.

  (*** Completeness proof : spn_fire_pre ***)
  Theorem spn_fire_pre_compl :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type) 
           (steadym decreasingm : marking_type) 
           (pgroup : list trans_type)
           (option_final_couple : option (list trans_type * marking_type)),
      SpnFirePre lneighbours pre test inhib steadym decreasingm pgroup option_final_couple ->
      spn_fire_pre lneighbours pre test inhib steadym decreasingm pgroup = option_final_couple.
  Proof.
    intros lneighbours pre test inhib steadym decreasingm pgroup option_final_couple Hspec;
      elim Hspec;
      intros.
    unfold spn_fire_pre; apply spn_fire_pre_aux_compl in H; auto. 
  Qed.

  (* Lemma : spn_fire_pre returns no error if 
   *         all transition t in pgroup are referenced in lneighbours
   *         and if all neighbour places referenced in lneighbours are
   *         referenced in the markings steadym and decreasingm. 
   *)
  Lemma spn_fire_pre_no_error :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type) 
           (steadym : marking_type) 
           (decreasingm : marking_type)
           (pgroup : list trans_type),
      (forall t : trans_type, In t pgroup -> In t (fst (split lneighbours))) ->
      (forall (t : trans_type) (neighbours : neighbours_type),
          In (t, neighbours) lneighbours ->
          ((forall p : place_type, In p neighbours.(pre_pl) -> In p (fst (split decreasingm))) /\
           (forall p : place_type, In p neighbours.(inhib_pl) -> In p (fst (split steadym))) /\
           (forall p : place_type, In p neighbours.(test_pl) -> In p (fst (split steadym))))) ->
      exists v : (list trans_type * marking_type),
        spn_fire_pre lneighbours pre test inhib steadym decreasingm pgroup = Some v.
  Proof.
    intros lneighbours pre test inhib steadym decreasingm pgroup; intros.
    unfold spn_fire_pre.
    apply spn_fire_pre_aux_no_error; [auto | auto].
  Qed.

  (* Lemma : Proves that spn_fire_pre preserves
   *         the structure of the marking decreasingm
   *         passed as argument. 
   *)
  Lemma spn_fire_pre_same_struct :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type) 
           (steadym : marking_type) 
           (decreasingm : marking_type)
           (pgroup : list trans_type)
           (final_fire_pre_group : list trans_type)
           (finalm : marking_type),
      spn_fire_pre lneighbours pre test inhib steadym decreasingm pgroup =
      Some (final_fire_pre_group, finalm) ->
      MarkingHaveSameStruct decreasingm finalm.
  Proof.
    intros lneighbours pre test inhib steadym decreasingm pgroup; intros.
    unfold spn_fire_pre in H.
    apply spn_fire_pre_aux_same_struct in H; auto.
  Qed.
  
  (***********************************************************************)
  (***********************************************************************)
  
  (*
   * Function : Returns the list of pre-fired transitions.
   *            Apply spn_fire_pre over ALL priority group of transitions. 
   *            Begin with initial marking; End with half fired marking.  
   *            "pre_fired_transitions" is empty at first. 
   *)
  Fixpoint spn_map_fire_pre_aux
           (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)
           (steadym decreasingm : marking_type)
           (pre_fired_transitions : list trans_type)
           (priority_groups : list (list trans_type)) :
    option (list trans_type * marking_type) :=
    match priority_groups with
    (* Loops over all priority group of transitions (prgroup) and
     * calls spn_fire_pre. *)
    | pgroup :: pgroups_tail =>
      match spn_fire_pre lneighbours pre test inhib steadym decreasingm pgroup with
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
  Inductive SpnMapFirePreAux
            (lneighbours : list (trans_type * neighbours_type))
            (pre test inhib : weight_type)
            (steadym decreasingm : marking_type)
            (pre_fired_transitions : list trans_type) :
    list (list trans_type) -> option (list trans_type * marking_type) -> Prop :=
  | SpnMapFirePreAux_nil :
      SpnMapFirePreAux lneighbours pre test inhib steadym decreasingm pre_fired_transitions []
                       (Some (pre_fired_transitions, decreasingm))
  | SpnMapFirePreAux_cons :
      forall (pgroup pre_fired_trs : list trans_type)
             (decreasedm : marking_type)
             (priority_groups : list (list trans_type))
             (option_final_couple : option (list trans_type * marking_type)),
        SpnFirePre lneighbours pre test inhib steadym decreasingm pgroup
                   (Some (pre_fired_trs, decreasedm)) ->
        SpnMapFirePreAux lneighbours pre test inhib steadym decreasedm (pre_fired_transitions ++ pre_fired_trs)
                         priority_groups
                         option_final_couple ->
        SpnMapFirePreAux lneighbours pre test inhib steadym decreasingm pre_fired_transitions
                         (pgroup :: priority_groups)
                         option_final_couple
  | SpnMapFirePreAux_err :
      forall (pgroup : list trans_type)
             (priority_groups : list (list trans_type)),
        SpnFirePre lneighbours pre test inhib steadym decreasingm pgroup None ->
        SpnMapFirePreAux lneighbours pre test inhib steadym decreasingm pre_fired_transitions
                         (pgroup :: priority_groups) None.

  (*** Correctness proof : spn_map_fire_pre_aux ***)
  Theorem spn_map_fire_pre_aux_correct :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)
           (steadym decreasingm : marking_type)
           (priority_groups : list (list trans_type))
           (pre_fired_transitions : list trans_type)
           (option_final_couple : option (list trans_type * marking_type)),
      spn_map_fire_pre_aux lneighbours pre test inhib steadym decreasingm
                           pre_fired_transitions priority_groups = option_final_couple ->
      SpnMapFirePreAux lneighbours pre test inhib steadym decreasingm
                       pre_fired_transitions priority_groups option_final_couple.
  Proof.
    intros lneighbours pre test inhib steadym decreasingm priority_groups
           pre_fired_transitions option_final_couple;
      functional induction (spn_map_fire_pre_aux lneighbours pre test inhib steadym decreasingm
                                                 pre_fired_transitions priority_groups)
                 using spn_map_fire_pre_aux_ind;
      intros.
    (* Case priority_groups = [] *)
    - rewrite <- H; apply SpnMapFirePreAux_nil.
    (* General case *)
    - apply SpnMapFirePreAux_cons with (pre_fired_trs := pre_fired_trs)
                                       (decreasedm := decreasedm).
      + apply spn_fire_pre_correct; auto.
      + apply IHo; rewrite H; auto.
    (* Case of error *)
    - rewrite <- H; apply SpnMapFirePreAux_err.
      apply spn_fire_pre_correct; auto.
  Qed.

  (*** Completeness proof : spn_map_fire_pre_aux ***)
  Theorem spn_map_fire_pre_aux_compl :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)
           (steadym decreasingm : marking_type)
           (priority_groups : list (list trans_type))
           (pre_fired_transitions : list trans_type)
           (option_final_couple : option (list trans_type * marking_type)),
      SpnMapFirePreAux lneighbours pre test inhib steadym decreasingm
                       pre_fired_transitions priority_groups option_final_couple ->
      spn_map_fire_pre_aux lneighbours pre test inhib steadym decreasingm
                           pre_fired_transitions priority_groups = option_final_couple.
  Proof.
    intros lneighbours pre test inhib steadym decreasingm
           priority_groups pre_fired_transitions option_final_couple Hspec;
      elim Hspec;
      intros.
    (* Case SpnMapFirePreAux_nil *)
    - simpl; auto.
    (* Case SpnMapFirePreAux_cons *)
    - simpl; apply spn_fire_pre_compl in H; rewrite H; rewrite H1; auto.
    (* Case SpnMapFirePreAux_err *)
    - simpl; apply spn_fire_pre_compl in H; rewrite H; auto.
  Qed.

  (*
   * Lemma : spn_map_fire_pre_aux returns no error if 
   *         forall pgroup of transitions in priority_groups,
   *         transitions are referenced in lneighbours and
   *         neighbours places (of these transitions) are referenced 
   *         in markings steadym and decreasingm.
   *)
  Lemma spn_map_fire_pre_aux_no_error :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)
           (steadym decreasingm : marking_type)
           (priority_groups : list (list trans_type))
           (pre_fired_transitions : list trans_type),
      (forall pgroup : list trans_type,
          In pgroup priority_groups ->
          ((forall t : trans_type, In t pgroup -> In t (fst (split lneighbours))) /\
           (forall (t : trans_type) (neighbours : neighbours_type),
               In (t, neighbours) lneighbours ->
               ((forall p : place_type, In p neighbours.(pre_pl) -> In p (fst (split decreasingm))) /\
                (forall p : place_type, In p neighbours.(inhib_pl) -> In p (fst (split steadym))) /\
                (forall p : place_type, In p neighbours.(test_pl) -> In p (fst (split steadym))))))) ->
      exists v : (list trans_type * marking_type),
        spn_map_fire_pre_aux lneighbours pre test inhib steadym decreasingm
                             pre_fired_transitions priority_groups = Some v.
  Proof.
    intros lneighbours pre test inhib steadym decreasingm
           priority_groups pre_fired_transitions.
    functional induction (spn_map_fire_pre_aux lneighbours pre test inhib steadym decreasingm
                                               pre_fired_transitions priority_groups)
               using spn_map_fire_pre_aux_ind;
      intros.
    (* Base case, priority_groups = []. *)
    - exists (pre_fired_transitions, decreasingm); auto.
    (* Case spn_fire_pre = Some v *)
    - apply IHo.
      do 2 intro.
      apply (in_cons pgroup) in H0.
      generalize (H pgroup0 H0); intro. auto.
      apply spn_fire_pre_same_struct in e0.
      unfold MarkingHaveSameStruct in e0.
      rewrite <- e0.
      auto.
    (* Case spn_fire_pre = None, impossible regarding the hypotheses. *)
    - cut (In pgroup (pgroup :: pgroups_tail)).
      + intro.
        generalize (H pgroup H0).
        intro.
        elim H1; intros; clear H1.
        generalize (spn_fire_pre_no_error lneighbours pre test inhib steadym decreasingm pgroup H2 H3).
        intro; elim H1; intros; rewrite H4 in e0; inversion e0.
      + apply in_eq. 
  Qed.
  
  (***********************************************************************)
  (***********************************************************************)
  
  (*
   * Function : Wrapper around spn_map_fire_pre_aux function. 
   *            Update the marking by consuming
   *            the tokens in pre-condition places.            
   *)
  Definition spn_map_fire_pre
             (lneighbours : list (trans_type * neighbours_type))
             (pre test inhib : weight_type)
             (m : marking_type)
             (priority_groups : list (list trans_type)) :
    option (list trans_type * marking_type) :=
    spn_map_fire_pre_aux lneighbours pre test inhib m m [] priority_groups.

  Functional Scheme spn_map_fire_pre_ind := Induction for spn_map_fire_pre Sort Prop.
  
  (*** Formal specification : spn_map_fire_pre ***)
  Inductive SpnMapFirePre
            (lneighbours : list (trans_type * neighbours_type))
            (pre test inhib : weight_type)
            (m : marking_type)
            (priority_groups : list (list trans_type)) :
    option (list trans_type * marking_type) -> Prop :=
  | SpnMapFirePre_cons :
      forall (option_final_couple : option (list trans_type * marking_type)),
        SpnMapFirePreAux lneighbours pre test inhib m m [] priority_groups
                         option_final_couple ->
        SpnMapFirePre lneighbours pre test inhib m priority_groups option_final_couple.

  (*** Correctness proof : spn_map_fire_pre ***)
  Theorem spn_map_fire_pre_correct :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)
           (m : marking_type)
           (priority_groups : list (list trans_type))
           (option_final_couple : option (list trans_type * marking_type)),
      spn_map_fire_pre lneighbours pre test inhib m priority_groups = option_final_couple ->
      SpnMapFirePre lneighbours pre test inhib m priority_groups option_final_couple.  
  Proof.
    intros lneighbours pre test inhib m priority_groups option_final_couple H.
    apply SpnMapFirePre_cons.
    apply spn_map_fire_pre_aux_correct.
    auto.
  Qed.

  (*** Completeness proof : spn_map_fire_pre ***)
  Theorem spn_map_fire_pre_compl :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)
           (m : marking_type)
           (priority_groups : list (list trans_type))
           (option_final_couple : option (list trans_type * marking_type)),
      SpnMapFirePre lneighbours pre test inhib m priority_groups
                    option_final_couple ->
      spn_map_fire_pre lneighbours pre test inhib m priority_groups = option_final_couple.
  Proof.
    intros lneighbours pre test inhib m priority_groups option_final_couple H.
    elim H; intros.
    unfold spn_map_fire_pre.
    apply spn_map_fire_pre_aux_compl; auto.
  Qed.

  Lemma spn_map_fire_pre_no_error :
    forall (lneighbours : list (trans_type * neighbours_type))
           (pre test inhib : weight_type)
           (m : marking_type)
           (priority_groups : list (list trans_type)),
      (forall pgroup : list trans_type,
          In pgroup priority_groups ->
          ((forall t : trans_type, In t pgroup -> In t (fst (split lneighbours))) /\
           (forall (t : trans_type) (neighbours : neighbours_type),
               In (t, neighbours) lneighbours ->
               ((forall p : place_type, In p neighbours.(pre_pl) -> In p (fst (split m))) /\
                (forall p : place_type, In p neighbours.(inhib_pl) -> In p (fst (split m))) /\
                (forall p : place_type, In p neighbours.(test_pl) -> In p (fst (split m))))))) ->
      exists v : (list trans_type * marking_type),
        spn_map_fire_pre lneighbours pre test inhib m priority_groups = Some v.
  Proof.
    intros lneighbours pre test inhib m priority_groups.
    unfold spn_map_fire_pre; intros.
    apply spn_map_fire_pre_aux_no_error.
    auto.
  Qed.
  
  (***********************************************************************)
  (***********************************************************************)
  
  (* 
   * Function : Returns a marking resulting of the update of the marking 
   *            for all post places related to the transitions contained in 
   *            the pre_fired_transitions list.
   *)
  Fixpoint fire_post
           (lneighbours : list (trans_type * neighbours_type))
           (post : weight_type)
           (increasingm : marking_type)
           (pre_fired_transitions : list trans_type) : option marking_type :=
    match pre_fired_transitions with
    | t :: tail  =>
      match get_neighbours lneighbours t with
      (* Updates the marking
       * for all neighbour post places of (tr i). *)
      | Some neighbours_t =>
        match update_marking_post t post increasingm (post_pl neighbours_t) with
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
  Inductive FirePost
            (lneighbours : list (trans_type * neighbours_type))
            (post : weight_type) 
            (increasingm : marking_type) :
    list trans_type -> option marking_type -> Prop :=
  (* Case pre_fired_transitions = [] *)
  | FirePost_nil :
      FirePost lneighbours post increasingm [] (Some increasingm)
  (* Case get_neighbours returns an error *)
  | FirePost_neighbours_err :
      forall (t : trans_type) (pre_fired_transitions : list trans_type),
        GetNeighbours lneighbours t None ->
        FirePost lneighbours post increasingm (t :: pre_fired_transitions) None
  (* General case *)
  | FirePost_cons :
      forall (i : nat)
             (neighbours_t : neighbours_type)
             (pre_fired_transitions : list trans_type)
             (modifiedm : marking_type)
             (optionm : option marking_type),
        GetNeighbours lneighbours i (Some neighbours_t) ->
        UpdateMarkingPost (tr i) post increasingm (post_pl neighbours_t) (Some modifiedm) ->
        FirePost lneighbours post modifiedm pre_fired_transitions optionm ->
        FirePost lneighbours post increasingm ((tr i) :: pre_fired_transitions) optionm
  (* Case update_marking_post returns an error. *)
  | FirePost_update_err :
      forall (i : nat)
             (neighbours_t : neighbours_type)
             (pre_fired_transitions : list trans_type),
        GetNeighbours lneighbours i (Some neighbours_t) ->
        UpdateMarkingPost (tr i) post increasingm (post_pl neighbours_t) None ->
        FirePost lneighbours post increasingm ((tr i) :: pre_fired_transitions) None.

  Functional Scheme fire_post_ind := Induction for fire_post Sort Prop.
  
  (*** Correctness proof : fire_post ***)
  Theorem fire_post_correct :
    forall (lneighbours : list neighbours_type)
           (post : weight_type) 
           (increasingm : marking_type) 
           (pre_fired_transitions : list trans_type)
           (optionm : option marking_type),
      fire_post lneighbours post increasingm pre_fired_transitions = optionm ->
      FirePost lneighbours post increasingm pre_fired_transitions optionm.
  Proof.
    intros lneighbours post increasingm pre_fired_transitions optionm;
      functional induction (fire_post lneighbours post increasingm pre_fired_transitions)
                 using fire_post_ind;
      intros.
    (* Case fired_pre_group = [] *)
    - rewrite <- H; apply FirePost_nil; auto.
    (* General case. *)
    - apply FirePost_cons with (neighbours_t := neighbours_t)
                               (modifiedm := new_marking).
      + apply get_neighbours_correct; auto.
      + apply update_marking_post_correct; auto.
      + apply IHo; rewrite <- H; auto.
    (* Case update_marking_post returns an error. *)
    - rewrite <- H; apply FirePost_update_err with (neighbours_t := neighbours_t).
      + apply get_neighbours_correct; auto.
      + apply update_marking_post_correct; auto.
    (* Case get_neighbours returns an error. *)
    - rewrite <- H; apply FirePost_neighbours_err.
      apply get_neighbours_correct; auto.
  Qed.

  (*** Completeness proof : fire_post ***)
  Theorem fire_post_compl :
    forall (lneighbours : list neighbours_type)
           (post : weight_type) 
           (increasingm : marking_type) 
           (pre_fired_transitions : list trans_type)
           (optionm : option marking_type),
      FirePost lneighbours post increasingm pre_fired_transitions optionm ->
      fire_post lneighbours post increasingm pre_fired_transitions = optionm.
  Proof.
    intros lneighbours post increasingm pre_fired_transitions optionm H;
      elim H;
      intros.
    (* Case FirePost_nil *)
    - simpl; auto.
    (* Case FirePost_neighbours_err *)
    - simpl; apply get_neighbours_compl in H0; rewrite H0; auto.
    (* General case *)
    - simpl.
      apply get_neighbours_compl in H0; rewrite H0.
      apply update_marking_post_compl in H1; rewrite H1; auto.
    (* Case FirePost_update_err *)
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
  Inductive SpnFire
            (lneighbours : list neighbours_type)
            (pre test inhib post : weight_type)
            (steadym : marking_type)
            (priority_groups : list (list trans_type)) :
    option (list trans_type * marking_type) -> Prop :=
  (* General case *)
  | SpnFire_cons :
      forall (pre_fired_transitions : list trans_type)
             (intermediatem finalm : marking_type),
        SpnMapFirePre lneighbours pre test inhib steadym priority_groups
                      (Some (pre_fired_transitions, intermediatem)) ->
        FirePost lneighbours post intermediatem pre_fired_transitions (Some finalm) ->
        SpnFire lneighbours pre test inhib post steadym priority_groups
                (Some (pre_fired_transitions, finalm))
  (* Case spn_map_fire_pre returns an error. *)
  | SpnFire_map_fire_pre_err :
      SpnMapFirePre lneighbours pre test inhib steadym priority_groups None ->
      SpnFire lneighbours pre test inhib post steadym priority_groups None
  (* Case fire_post returns an error. *)
  | SpnFire_fire_post_err :
      forall (pre_fired_transitions : list trans_type)
             (intermediatem : marking_type),
        SpnMapFirePre lneighbours pre test inhib steadym priority_groups
                      (Some (pre_fired_transitions, intermediatem)) ->
        FirePost lneighbours post intermediatem pre_fired_transitions None ->
        SpnFire lneighbours pre test inhib post steadym priority_groups None.

  (*** Correctness proof : spn_fire ***)
  Theorem spn_fire_correct :
    forall (lneighbours : list neighbours_type)
           (pre test inhib post : weight_type)
           (steadym : marking_type)
           (priority_groups : list (list trans_type))
           (option_final_couple : option (list trans_type * marking_type)),
      spn_fire lneighbours pre test inhib post steadym priority_groups = option_final_couple ->
      SpnFire lneighbours pre test inhib post steadym priority_groups option_final_couple.
  Proof.
    intros lneighbours pre test inhib post steadym priority_groups option_final_couple;
      functional induction (spn_fire lneighbours pre test inhib post steadym priority_groups)
                 using spn_fire_ind;
      intros.
    (* General case *)
    - rewrite <- H; apply SpnFire_cons with (intermediatem := intermediatem).
      + apply spn_map_fire_pre_correct; auto.
      + apply fire_post_correct; auto.
    (* Case fire_post returns an error. *)
    - rewrite <- H; apply SpnFire_fire_post_err
                      with (pre_fired_transitions := pre_fired_transitions)
                           (intermediatem := intermediatem).
      + apply spn_map_fire_pre_correct; auto.
      + apply fire_post_correct; auto.
    (* Case spn_map_fire_pre returns an error. *)
    - rewrite <- H; apply SpnFire_map_fire_pre_err.
      apply spn_map_fire_pre_correct; auto.                             
  Qed.

  (*** Completeness proof : spn_fire ***)
  Theorem spn_fire_compl :
    forall (lneighbours : list neighbours_type)
           (pre test inhib post : weight_type)
           (steadym : marking_type)
           (priority_groups : list (list trans_type))
           (option_final_couple : option (list trans_type * marking_type)),
      SpnFire lneighbours pre test inhib post steadym priority_groups option_final_couple ->
      spn_fire lneighbours pre test inhib post steadym priority_groups = option_final_couple.
  Proof.
    intros lneighbours pre test inhib post steadym priority_groups option_final_couple Hspec.
    elim Hspec; intros; unfold spn_fire.
    (* Case SpnFire_cons *)
    + apply spn_map_fire_pre_compl in H; rewrite H.
      apply fire_post_compl in H0; rewrite H0; auto.
    (* Case SpnFire_map_fire_pre_err *)
    + apply spn_map_fire_pre_compl in H; rewrite H; auto.
    (* Case SpnFire_fire_post_err *)
    + apply spn_map_fire_pre_compl in H; rewrite H.
      apply fire_post_compl in H0; rewrite H0; auto.
  Qed.

  (* Lemma : spn_fire always returns some value
   *         if spn (which attributes are passed as arguments)
   *         verifies certains properties. 
   *)
  Theorem spn_fire_no_error :
    forall (spn : SPN)
           (t : trans_type)
           (p : place_type)
           (i n : nat)
           (neighbours : neighbours_type)
           (group group' : list trans_type),
      NoDupPlaces spn ->
      NoDupTranss spn ->
      NoUnknownInPriorityGroups spn t ->
      NoIntersectInPriorityGroups spn group group' t ->
      NoDupLneighbours spn ->
      NoIsolatedOrUnknownPlace spn p ->
      NoIsolatedOrUnknownTrans spn i ->
      UniqIndexLneighbours spn neighbours ->
      NoDupMarking spn ->
      NoUnmarkedPlace spn i ->
      NoUnknownPlaceInMarking spn i n ->
      UniqIndexMarking spn i n ->
      exists couple : (list trans_type * marking_type),
        spn_fire (lneighbours spn)
                 (pre spn)
                 (test spn)
                 (inhib spn)
                 (post spn)
                 (marking spn)
                 (priority_groups spn) = Some couple.
  Proof.
    unfold spn_fire.
  Admitted.
  
End FireSpn.

(*==========================================================*)
(*================= SPN CYCLE EVOLUTION ====================*)
(*==========================================================*)

Section AnimateSpn.
  
  (*  
   * Function : Returns the resulting Petri net after all the sensitized
   *            transitions in spn have been fired, and returns
   *            the list of transitions fired in this cycle.
   *
   *)
  Definition spn_cycle (spn : SPN) : option (list trans_type * SPN) :=
    match spn with
    | (mk_SPN places transs pre post test inhib m priority_groups lneighbours) =>
      match (spn_fire lneighbours pre test inhib post m priority_groups) with
      | Some (fired_transitions, nextm) =>
        Some (fired_transitions,
              (mk_SPN places transs pre post test inhib nextm priority_groups lneighbours))
      | None => None
      end
    end.

  (*** Formal specification : SpnCycle ***)
  Inductive SpnCycle (spn : SPN) :
    option (list trans_type * SPN) -> Prop :=
  (* General case *)
  | SpnCycle_cons :
      forall (places : list place_type)
             (transs : list trans_type)
             (pre post test inhib : weight_type)
             (m nextm : marking_type)
             (priority_groups : list (list trans_type))
             (lneighbours : list neighbours_type)
             (fired_transitions : list trans_type),
        spn = (mk_SPN places transs pre post test inhib m priority_groups lneighbours) ->
        SpnFire lneighbours pre test inhib post m priority_groups
                (Some (fired_transitions, nextm)) ->
        SpnCycle spn (Some (fired_transitions,
                            (mk_SPN places transs pre post test inhib nextm
                                    priority_groups lneighbours)))
  (* Case spn_fire returns an error. *)
  | SpnCycle_err :
      forall (places : list place_type)
             (transs : list trans_type)
             (pre post test inhib : weight_type)
             (m : marking_type)
             (priority_groups : list (list trans_type))
             (lneighbours : list neighbours_type),
        spn = (mk_SPN places transs pre post test inhib m priority_groups lneighbours) ->
        SpnFire lneighbours pre test inhib post m priority_groups None ->
        SpnCycle spn None.

  Functional Scheme spn_cycle_ind := Induction for spn_cycle Sort Prop.
  
  (*** Correctness proof : spn_cycle ***)
  Theorem spn_cycle_correct :
    forall (spn : SPN)
           (option_final_couple : option (list trans_type * SPN)),
      spn_cycle spn = option_final_couple -> SpnCycle spn option_final_couple.
  Proof.
    intros; functional induction (spn_cycle spn) using spn_cycle_ind; intros.
    rewrite <- H; apply SpnCycle_cons with (m := m).
    (* Base case *)
    - auto.
    (* General case, all went well. *)
    - apply spn_fire_correct; auto.
    (* Error case. *)
    - rewrite <- H; apply SpnCycle_err with (places := places0)
                                            (transs := transs0)
                                            (pre := pre0)
                                            (post := post0)
                                            (test := test0)
                                            (inhib := inhib0)
                                            (m := m)
                                            (priority_groups := priority_groups0)
                                            (lneighbours := lneighbours0).
      + auto.
      + apply spn_fire_correct; auto.
  Qed.

  (*** Completeness proof : spn_cycle ***)
  Theorem spn_cycle_compl :
    forall (spn : SPN)
           (option_final_couple : option (list trans_type * SPN)),
      SpnCycle spn option_final_couple -> spn_cycle spn = option_final_couple.
  Proof.
    intros; elim H; intros.
    unfold spn_cycle; rewrite H0.
    apply spn_fire_compl in H1; rewrite H1.
    (* SpnCycle_cons *)
    + auto.
    (* SpnCycle_err *)
    + unfold spn_cycle; rewrite H0.
      apply spn_fire_compl in H1; rewrite H1; auto.
  Qed.

  Theorem spn_cycle_no_error :
    forall (spn : SPN)
           (t : trans_type)
           (p : place_type)
           (i n : nat)
           (neighbours : neighbours_type)
           (group group' : list trans_type),
      NoDupPlaces spn ->
      NoDupTranss spn ->
      NoUnknownInPriorityGroups spn t ->
      NoIntersectInPriorityGroups spn group group' t ->
      NoDupLneighbours spn ->
      NoIsolatedOrUnknownPlace spn p ->
      NoIsolatedOrUnknownTrans spn i ->
      UniqIndexLneighbours spn neighbours ->
      NoDupMarking spn ->
      NoUnmarkedPlace spn i ->
      NoUnknownPlaceInMarking spn i n ->
      UniqIndexMarking spn i n ->
      exists value : list trans_type * SPN, spn_cycle spn = Some value.
  Proof.
    intros spn t p i n neighbours group group'
           HNoDupPlaces
           HNoDupTranss
           HNoUnknownInPriorityGroups
           HNoIntersectInPriorityGroups
           HNoDupLneighbours
           HNoIsolatedOrUnknownPlace
           HNoIsolatedOrUnknownTrans
           HUniqIndexLneighbours
           HNoDupMarking
           HNoUnmarkedPlace
           Hno_unknown_place_inmarking
           HUniqIndexMarking.
    destruct spn.
    unfold spn_cycle.
    unfold spn_fire.
    unfold spn_map_fire_pre.
    unfold spn_map_fire_pre_aux.
    unfold spn_fire_pre.
    unfold spn_fire_pre_aux.
    unfold update_marking_pre.
    unfold modify_m.
    case spn_fire.
    - intro; elim p0; intros. exists ((a, {| places := places;
                                             transs := transs;
                                             pre := pre;
                                             post := post;
                                             test := test;
                                             inhib := inhib;
                                             marking := b;
                                             priority_groups := priority_groups;
                                             lneighbours := lneighbours |})). auto.
    - 
      +
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
  Inductive SpnAnimate (spn : SPN) :
    nat -> list ((list (list trans_type)) * marking_type) -> Prop :=
  | SpnAnimate_0 : SpnAnimate spn 0 [([], [])]
  | SpnAnimate_cons :
      forall (n : nat)
             (fired_groups_at_n : list (list trans_type))
             (spn_at_n : SPN)
             (marking_evolution : list ((list (list trans_type)) * marking_type)),
        SpnCycle spn (fired_groups_at_n, spn_at_n) ->
        SpnAnimate spn_at_n n marking_evolution ->
        SpnAnimate spn (S n) ((fired_groups_at_n, (marking spn_at_n)) :: marking_evolution).
  
  (*** Correctness proof : spn_animate***)
  Theorem spn_animate_correct :
    forall (spn :SPN)
           (n : nat)
           (marking_evolution : list ((list (list trans_type)) * marking_type)),
      spn_animate spn n = marking_evolution -> SpnAnimate spn n marking_evolution.
  Proof.                                                                                
    intros spn n; functional induction (spn_animate spn n) using spn_animate_ind.
    (* Case n = 0 *)
    - intros; rewrite <- H; apply SpnAnimate_0.
    (* General case *)
    - intros; rewrite <- H; apply SpnAnimate_cons.
      + apply spn_cycle_correct in e0; auto.
      + apply IHl; auto.
  Qed.

  (*** Completeness proof : spn_animate ***)
  Theorem spn_animate_compl :
    forall (spn :SPN)
           (n : nat)
           (marking_evolution : list ((list (list trans_type)) * marking_type)),
      SpnAnimate spn n marking_evolution -> spn_animate spn n = marking_evolution.
  Proof.                                                                                
    intros; elim H; intros.
    (* Case SpnAnimate_0 *)
    - simpl; auto.
    (* Case SpnAnimate_cons *)
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
