Require Import Hilecop.SPNAnimator.

(*! ============================= !*)
(*! ======= Spn Semantics ======= !*)
(*! ============================= !*)


(** * Preliminary definitions *)

(** In all the following definitions, (IsWellDefinedSpn spn) is a necessary condition. *)

Inductive IsPredInList {A : Type} (a b : A) : list A -> Prop :=
| IsPredInList_cons:
    forall l l' l'' : list A,
      NoDup (l ++ a :: l' ++ b :: l'') -> 
      IsPredInList a b (l ++ a :: l' ++ b :: l'').

(** HasHigherPriority: ∀ t ∈ T, t' ∈ T/{t}, t ≻ t' *)

Definition HasHigherPriority
           (spn : Spn)
           (t t' : Trans)
           (pgroup : list Trans) :=
  IsWellDefinedSpn spn ->
  In pgroup spn.(priority_groups) ->
  In t pgroup ->
  In t' pgroup ->
  t <> t' ->
  IsPredInList t t' pgroup.

(** Pr: Returns the list of fired transitions with a higher priority than t. *)

Inductive Pr (spn : Spn) (pgroup : list Trans) (t : Trans) : list Trans -> list Trans -> Prop :=
| Pr_nil :
    IsWellDefinedSpn spn ->
    In pgroup spn.(priority_groups) ->
    In t pgroup ->
    Pr spn pgroup t [] []
| Pr_cons :
    forall (fired : list Trans)
           (pr : list Trans)
           (t' : Trans),
    IsWellDefinedSpn spn ->
    In pgroup spn.(priority_groups) ->
    incl fired spn.(transs) ->
    In t pgroup ->
    In t' pgroup ->
    t' <> t ->
    HasHigherPriority spn t' t pgroup ->
    Pr spn pgroup t fired pr ->
    Pr spn pgroup t (t' :: fired) (t' :: pr).

(** PreSum: Sums all weight of edges coming from place p to transitions of the l list. *)

Inductive PreSum (spn : Spn) (p : Place) : list Trans -> nat -> Prop :=
| PreSum_nil :
    IsWellDefinedSpn spn ->
    In p spn.(places) ->
    PreSum spn p [] 0
| PreSum_cons :
    forall (l : list Trans)
           (t : Trans)
           (sum : nat),
      IsWellDefinedSpn spn ->
      In p spn.(places) ->
      In t spn.(transs) ->
      incl l spn.(transs) ->
      PreSum spn p l sum ->
      PreSum spn p (t :: l) ((pre spn t p) + sum).

(** PostSum: Sums all weight of edges coming from transitions of the l list to place p. *)

Inductive PostSum (spn : Spn) (p : Place) : list Trans -> nat -> Prop :=
| PostSum_nil :
    IsWellDefinedSpn spn ->
    In p spn.(places) ->
    PostSum spn p [] 0
| PostSum_cons :
    forall (l : list Trans)
      (t : Trans)
      (sum : nat),
      IsWellDefinedSpn spn ->
      In p spn.(places) ->
      In t spn.(transs) ->
      incl l spn.(transs) ->
      PostSum spn p l sum ->
      PostSum spn p (t :: l) ((post spn t p) + sum).

Section IsSensitized.

  (** IsSensitized:
    ∀ t ∈ T, marking m, t ∈ sens(m) if
    ∀ p ∈ P, m(p) ≥ Pre(p, t) ∧ 
             m(p) ≥ Pre_t(p, t) ∧ 
             (m(p) < Pre_i(p, t) ∨ Pre_i(p, t) = 0) *)

  Definition IsSensitized
             (spn : Spn)
             (marking : list (Place * nat))
             (t : Trans) : Prop :=
    IsWellDefinedSpn spn ->
    MarkingHaveSameStruct spn.(initial_marking) marking ->
    In t spn.(transs) ->
    forall (p : Place)
      (n : nat),
      In (p, n) marking ->
      (pre spn t p) <= n  /\
      (test spn t p) <= n  /\
      (n < (inhib spn t p) \/ (inhib spn t p) = 0).

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
    do 4 intro;
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
    do 5 intro;
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
    do 5 intro;
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

  (** *)

  Lemma map_check_pre_correct :
    forall (spn : Spn)
      (marking : list (Place * nat))
      (pre_places : list Place)
      (t : Trans)
      (neighbours_of_t : Neighbours),
      IsWellDefined spn ->
      MarkingHaveSameStruct spn.(initial_marking) marking ->
      In (t, neighbours_of_t) spn.(lneighbours) ->
      pre_places = (pre_pl neighbours_of_t) ->
      map_check_pre spn marking pre_places t = Some true ->
      (forall (p : Place) (n : nat), In (p, n) marking -> (pre spn t p) <= n).
  Proof.
    
  Admitted.

  (** Correctness proof for is_sensitized and IsSensitized *)

  Theorem is_sensitized_correct :
    forall (spn : Spn)
      (marking : list (Place * nat))
      (t : Trans)
      (neighbours_of_t : Neighbours),
      MarkingHaveSameStruct spn.(initial_marking) marking ->
      In (t, neighbours_of_t) spn.(lneighbours) ->
      is_sensitized spn marking neighbours_of_t t = Some true ->
      IsSensitized spn marking t.
  Proof.
    do 4 intro;
      functional induction (is_sensitized spn marking neighbours_of_t t)
                 using is_sensitized_ind;
      intros.
    unfold IsSensitized.
    
  Qed.

  
End IsSensitized.

(** SpnIsFirable: 
    ∀ t ∈ T, state s = (m), marking m, t ∈ firable(s) if 
    t ∈ sens(m) *)

Definition SpnIsFirable
           (spn : Spn)
           (state : SpnState)
           (t : Trans) :=
  IsWellDefinedSpn spn ->
  IsWellDefinedSpnState spn state ->
  In t spn.(transs) ->
  IsSensitized spn state.(marking) t.

(** * Semantics definition *)

(** Represents the two clock events regulating the Spn evolution. *)

Inductive Clock : Set :=
| falling_edge : Clock
| raising_edge : Clock.

(** Represents the Spn Semantics  *)

Inductive SpnSemantics (spn : Spn) (s s' : SpnState) : Clock -> Prop :=
  
(* ↓clock : s = (Fired, M) ⇝ s' = (Fired', M) *)
| SpnSemantics_falling_edge :
    
    IsWellDefinedSpn spn ->
    IsWellDefinedSpnState spn s ->
    IsWellDefinedSpnState spn s' ->
    (* Marking stays the same between state s and s'. *)
    s.(marking) = s'.(marking) ->
    (* ∀ t ∉ firable(s') ⇒ t ∉ Fired'  
       All un-firable transitions are not fired. *)
    (forall (pgroup : list Trans) (t : Trans),
        In pgroup spn.(priority_groups) ->
        In t pgroup ->
        ~SpnIsFirable spn s' t ->
        ~In t s'.(fired)) ->
    (* ∀ t ∈ firable(s'), (∀ t', t' ≻ t ⇒ t' ∉ firable(s')) ⇒ t ∈ Fired' 
       If all transitions with a higher firing priority than t are not firable,
       then t is fired. *)
    (forall (pgroup : list Trans) (t : Trans),
        In pgroup spn.(priority_groups) ->
        In t pgroup ->
        SpnIsFirable spn s' t ->
        (forall (t' : Trans),
            In t' pgroup ->
            t' <> t ->
            HasHigherPriority spn t' t pgroup ->
            ~SpnIsFirable spn s' t') ->
        In t s'.(fired)) ->
    (* ∀ t ∈ firable(s'), t ∈ sens(M - ∑ pre(t_i), ∀ t_i ∈ Pr(t)) ⇒ t ∈ Fired' 
       If t is sensitized by the residual marking, result of the firing of
       all higher priority transitions, then t is fired. *)
    (forall (pgroup : list Trans)
       (t : Trans)
       (residual_marking : list (Place * nat))
       (pr : list Trans),
        In pgroup spn.(priority_groups) ->
        In t pgroup ->
        MarkingHaveSameStruct spn.(initial_marking) residual_marking ->
        SpnIsFirable spn s' t ->
        Pr spn pgroup t s'.(fired) pr ->
        (forall (p : Place)
           (n n' preSum : nat),
            In (p, n) s'.(marking) ->
            PreSum spn p pr preSum ->
            In (p, n - preSum) residual_marking) ->
        IsSensitized spn residual_marking t ->
        In t s'.(fired)) ->
    (* ∀ t ∈ firable(s'), t ∉ sens(M - ∑ pre(t_i), ∀ t_i ∈ Pr(t)) ⇒ t ∉ Fired' 
       If t is not sensitized by the residual marking, result of the firing of
       all higher priority transitions, then t is not fired. *)
    (forall (pgroup : list Trans)
       (t : Trans)
       (residual_marking : list (Place * nat))
       (pr : list Trans),
        In pgroup spn.(priority_groups) ->
        In t pgroup ->
        MarkingHaveSameStruct spn.(initial_marking) residual_marking ->
        SpnIsFirable spn s' t ->
        Pr spn pgroup t s'.(fired) pr ->
        (forall (p : Place)
                (n preSum : nat),
            In (p, n) s'.(marking) ->
            PreSum spn p pr preSum ->
            In (p, n - preSum) residual_marking) ->
        ~IsSensitized spn residual_marking t ->
        ~In t s'.(fired)) ->
    
    SpnSemantics spn s s' falling_edge
    
(* ↓clock : s = (Fired, M) ⇝ s' = (Fired, M') *)    
| SpnSemantics_raising_edge :
    
    IsWellDefinedSpn spn ->
    IsWellDefinedSpnState spn s ->
    IsWellDefinedSpnState spn s' ->
    (* Fired stays the same between state s and s'. *)
    s.(fired) = s'.(fired) ->
    (* M' = M - ∑ (pre(t_i) - post(t_i)), ∀ t_i ∈ Fired *)
    (forall (p : Place)
            (n preSum postSum : nat),
        In (p, n) s.(marking) ->
        PreSum spn p s.(fired) preSum ->
        PostSum spn p s.(fired) postSum ->
        In (p, n - preSum + postSum) s'.(marking)) ->
    
    SpnSemantics spn s s' raising_edge.

(** Correctness proof between spn_cycle and SpnSemantics_falling_edge. *)

Theorem spn_semantics_falling_edge_correct :
  forall (spn : Spn)
    (s s' s'' : SpnState),
    IsWellDefinedSpn spn ->
    IsWellDefinedSpnState spn s ->
    IsWellDefinedSpnState spn s' ->
    IsWellDefinedSpnState spn s'' ->
    spn_cycle spn s = Some (s', s'') ->
    SpnSemantics spn s s' falling_edge.
Proof.
  do 2 intro;
    functional induction (spn_cycle spn s) using spn_cycle_ind;
    intros.
  - apply SpnSemantics_falling_edge.
    (* Trivial proof, IsWellDefinedSpn. *)
    + assumption.
    (* Trivial proof, IsWellDefinedSpnState. *)
    + assumption.
    (* Trivial proof, IsWellDefinedSpnState. *)
    + assumption.
    (* Proves s.(marking) = s'.(marking) *)
    + apply spn_map_fire_same_marking in e.
      injection H3; intros; rewrite <- H5; assumption.
    (*  *)
    + unfold spn_map_fire in e; unfold spn_map_fire_aux in e.
      injection H3; intros; rewrite <- H5.
  - inversion H3.
  - inversion H3.
Qed.

(** Correctness proof between spn_cycle and SpnSemantics_raising_edge. *)

Theorem spn_semantics_raising_edge_correct :
  forall (spn : Spn)
         (s s' s'' : SpnState),
    IsWellDefinedSpn spn ->
    IsWellDefinedSpnState spn s ->
    IsWellDefinedSpnState spn s' ->
    IsWellDefinedSpnState spn s'' ->
    spn_cycle spn s = Some (s', s'') ->
    SpnSemantics spn s' s'' raising_edge.
Proof.
  do 2 intro.
  functional induction (spn_cycle spn s) using spn_cycle_ind; intros.
Qed.