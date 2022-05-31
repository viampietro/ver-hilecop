(** * Facts about H-VHDL Environment *)

Require Import common.CoqLib.
Require Import common.proofs.CoqTactics.
Require Import common.NatSet.

Require Import common.NatMap.
Require Import common.proofs.NatMapTactics.
Require Import common.NatSet.

Require Import hvhdl.HVhdlTypes.
Require Import hvhdl.Environment.
Require Import hvhdl.SemanticalDomains.

(** ** Equivalence Relations between Elaborated Designs *)

(** *** Generic Constant Set Equivalence *)

Definition EqGens (Δ Δ' : ElDesign) :=
  forall id t v,
    MapsTo id (Generic t v) Δ <-> MapsTo id (Generic t v) Δ'.

Definition EqGens_refl : forall (Δ : ElDesign), EqGens Δ Δ. firstorder. Defined.
Definition EqGens_trans : forall (Δ Δ' Δ'' : ElDesign), EqGens Δ Δ' -> EqGens Δ' Δ'' -> EqGens Δ Δ''.
  unfold EqGens; intros; transitivity (MapsTo id (Generic t0 v) Δ'); auto.
Defined.
Definition EqGens_sym : forall (Δ Δ' : ElDesign), EqGens Δ Δ' -> EqGens Δ' Δ.
  unfold EqGens; symmetry; auto.
Defined.

Add Parametric Relation : (ElDesign) (EqGens)
    reflexivity proved by EqGens_refl
    symmetry proved by EqGens_sym
    transitivity proved by EqGens_trans
      as EqGens_rel.           

(** Enable rewriting [MapsTo id (Generic t v) Δ1] into  
    [MapsTo id (Generic t) Δ2] if [EqGens Δ1 Δ2]. *)

Add Parametric Morphism (id : ident) (t : type) (v : value) : (MapsTo id (Generic t v)) 
    with signature (@EqGens ==> impl) as eqgens_mapsto_mor.
Proof. intros x y H; rewrite (H id t); unfold impl; auto. Qed.

#[export] Hint Resolve EqGens_refl : hvhdl.
#[export] Hint Resolve EqGens_trans : hvhdl.
#[export] Hint Resolve EqGens_sym : hvhdl.

(** *** Input Port Set Equivalence *)

Definition EqIns (Δ Δ' : ElDesign) :=
  forall id t,
    MapsTo id (Input t) Δ <-> MapsTo id (Input t) Δ'.

Definition EqIns_refl : forall (Δ : ElDesign), EqIns Δ Δ. firstorder. Defined.
Definition EqIns_trans : forall (Δ Δ' Δ'' : ElDesign), EqIns Δ Δ' -> EqIns Δ' Δ'' -> EqIns Δ Δ''.
  unfold EqIns; intros; transitivity (MapsTo id (Input t0) Δ'); auto.
Defined.
Definition EqIns_sym : forall (Δ Δ' : ElDesign), EqIns Δ Δ' -> EqIns Δ' Δ.
  unfold EqIns; symmetry; auto.
Defined.

Add Parametric Relation : (ElDesign) (EqIns)
    reflexivity proved by EqIns_refl
    symmetry proved by EqIns_sym
    transitivity proved by EqIns_trans
      as EqIns_rel.

(** Rewrite [MapsTo id (Input t) Δ1] into  
    [MapsTo id (Input t) Δ2] if [EqIns Δ1 Δ2]. *)

Add Parametric Morphism (id : ident) (t : type) : (MapsTo id (Input t)) 
    with signature (@EqIns ==> impl) as eqins_mapsto_in_mor.
Proof. intros x y H; rewrite (H id t); unfold impl; auto. Qed.

(** *** Output Port Set Equivalence *)

Definition EqOuts (Δ Δ' : ElDesign) :=
  forall id t,
    MapsTo id (Output t) Δ <-> MapsTo id (Output t) Δ'.

Definition EqOuts_refl : forall (Δ : ElDesign), EqOuts Δ Δ. firstorder. Defined.
Definition EqOuts_trans : forall (Δ Δ' Δ'' : ElDesign), EqOuts Δ Δ' -> EqOuts Δ' Δ'' -> EqOuts Δ Δ''.
  unfold EqOuts; intros; transitivity (MapsTo id (Output t0) Δ'); auto.
Defined.
Definition EqOuts_sym : forall (Δ Δ' : ElDesign), EqOuts Δ Δ' -> EqOuts Δ' Δ.
  unfold EqOuts; symmetry; auto.
Defined.

Add Parametric Relation : (ElDesign) (EqOuts)
    reflexivity proved by EqOuts_refl
    symmetry proved by EqOuts_sym
    transitivity proved by EqOuts_trans
      as EqOuts_rel.

(** Rewrite [MapsTo id (Output t) Δ1] into  
    [MapsTo id (Output t) Δ2] if [EqOuts Δ1 Δ2]. *)

Add Parametric Morphism (id : ident) (t : type) : (MapsTo id (Output t)) 
    with signature (@EqOuts ==> impl) as eqouts_mapsto_out_mor.
Proof. intros x y H; rewrite (H id t); unfold impl; auto. Qed.

(** *** Internal Signal Set Equivalence *)

Definition EqDecls (Δ Δ' : ElDesign) :=
  forall id t,
    MapsTo id (Internal t) Δ <-> MapsTo id (Internal t) Δ'.

Definition EqDecls_refl : forall (Δ : ElDesign), EqDecls Δ Δ. firstorder. Defined.
Definition EqDecls_trans : forall (Δ Δ' Δ'' : ElDesign), EqDecls Δ Δ' -> EqDecls Δ' Δ'' -> EqDecls Δ Δ''.
  unfold EqDecls; intros; transitivity (MapsTo id (Internal t0) Δ'); auto.
Defined.
Definition EqDecls_sym : forall (Δ Δ' : ElDesign), EqDecls Δ Δ' -> EqDecls Δ' Δ.
  unfold EqDecls; symmetry; auto.
Defined.

Add Parametric Relation : (ElDesign) (EqDecls)
    reflexivity proved by EqDecls_refl
    symmetry proved by EqDecls_sym
    transitivity proved by EqDecls_trans
      as EqDecls_rel.

(** Enable rewriting [MapsTo id (Internal t) Δ1] into  
    [MapsTo id (Internal t) Δ2] if [EqDecls Δ1 Δ2]. *)

Add Parametric Morphism (id : ident) (t : type) : (MapsTo id (Internal t)) 
    with signature (@EqDecls ==> impl) as eqdecls_mapsto_decl_mor.
Proof. intros x y H; rewrite (H id t); unfold impl; auto. Qed.

(** *** Signal (Input, Output and Internal) Set Equivalence *)

Definition EqSigs (Δ Δ' : ElDesign) :=
  EqIns Δ Δ' /\ EqOuts Δ Δ' /\ EqDecls Δ Δ'.

Definition EqSigs_refl : forall (Δ : ElDesign), EqSigs Δ Δ. firstorder. Defined.
Definition EqSigs_trans : forall (Δ Δ' Δ'' : ElDesign), EqSigs Δ Δ' -> EqSigs Δ' Δ'' -> EqSigs Δ Δ''.
  unfold EqSigs; intros; decompose [and] H; decompose [and] H0.
  split_and; transitivity Δ'; auto.
Defined.
Definition EqSigs_sym : forall (Δ Δ' : ElDesign), EqSigs Δ Δ' -> EqSigs Δ' Δ.
  unfold EqSigs; intros; decompose [and] H.
  split_and; symmetry; auto.
Defined.

Add Parametric Relation : (ElDesign) (EqSigs)
    reflexivity proved by EqSigs_refl
    symmetry proved by EqSigs_sym
    transitivity proved by EqSigs_trans
      as EqSigs_rel.

(** Enable rewriting [MapsTo id (Internal t) Δ1] into  
    [MapsTo id (Internal t) Δ2] if [EqSigs Δ1 Δ2]. *)

Add Parametric Morphism (id : ident) (t : type) : (MapsTo id (Internal t)) 
    with signature (@EqSigs ==> impl) as eqsigs_mapsto_decl_mor.
Proof. intros x y H; do 2 (apply proj2 in H); rewrite H; unfold impl; auto. Qed.

(** Enable rewriting [MapsTo id (Output t) Δ1] into  
    [MapsTo id (Output t) Δ2] if [EqSigs Δ1 Δ2]. *)

Add Parametric Morphism (id : ident) (t : type) : (MapsTo id (Output t)) 
    with signature (@EqSigs ==> impl) as eqsigs_mapsto_out_mor.
Proof. intros x y H; apply proj2, proj1 in H. rewrite H; unfold impl; auto. Qed.

(** Enable rewriting [MapsTo id (Input t) Δ1] into  
    [MapsTo id (Input t) Δ2] if [EqSigs Δ1 Δ2]. *)

Add Parametric Morphism (id : ident) (t : type) : (MapsTo id (Input t)) 
    with signature (@EqSigs ==> impl) as eqsigs_mapsto_in_mor.
Proof. intros x y H; apply proj1 in H; rewrite H; unfold impl; auto. Qed.

(** *** Process and Component Instance Set Equivalence *)

Definition EqPs (Δ Δ' : ElDesign) :=
  forall id Λ,
    MapsTo id (Process Λ) Δ <-> MapsTo id (Process Λ) Δ'.

Definition EqComps (Δ Δ' : ElDesign) :=
  forall id Δ__c,
    MapsTo id (Component Δ__c) Δ <-> MapsTo id (Component Δ__c) Δ'.

(** ** Equivalence Relations between Design States *)

(** *** Signal Store Equivalence *)

Definition EqSStore (σ σ' : DState) :=
  forall id v,
    MapsTo id v (sstore σ) <-> MapsTo id v (sstore σ').

Definition EqSStore_refl : forall (σ : DState), EqSStore σ σ. firstorder. Defined.
Definition EqSStore_trans : forall (σ σ' σ'' : DState), EqSStore σ σ' -> EqSStore σ' σ'' -> EqSStore σ σ''.
  unfold EqSStore; intros; transitivity (MapsTo id v (sstore σ')); auto.
Defined.
Definition EqSStore_sym : forall (σ σ' : DState), EqSStore σ σ' -> EqSStore σ' σ.
  unfold EqSStore; symmetry; auto.
Defined.

Add Parametric Relation : (DState) (EqSStore)
    reflexivity proved by EqSStore_refl
    symmetry proved by EqSStore_sym
    transitivity proved by EqSStore_trans
      as EqSStore_rel.

(** Enable rewriting [MapsTo id v (sstore σ1)] into  
    [MapsTo id v (sstore σ2)] if [EqSStore σ1 σ2]. *)

Add Parametric Morphism (id : ident) (v : value) : (fun σ => MapsTo id v (sstore σ)) 
    with signature (@EqSStore ==> impl) as eqsstore_mapsto_mor.
Proof. intros x y H; unfold EqSStore in H; erewrite H; unfold impl; eauto. Qed.

(** *** Component Store Equivalence *)

Definition EqCStore (σ σ' : DState) :=
  forall id σ__c,
    MapsTo id σ__c (cstore σ) <-> MapsTo id σ__c (cstore σ').

Definition EqCStore_refl : forall (σ : DState), EqCStore σ σ. firstorder. Defined.
Definition EqCStore_trans : forall (σ σ' σ'' : DState), EqCStore σ σ' -> EqCStore σ' σ'' -> EqCStore σ σ''.
  unfold EqCStore; intros; transitivity (MapsTo id σ__c (cstore σ')); auto.
Defined.
Definition EqCStore_sym : forall (σ σ' : DState), EqCStore σ σ' -> EqCStore σ' σ.
  unfold EqCStore; symmetry; auto.
Defined.

Add Parametric Relation : (DState) (EqCStore)
    reflexivity proved by EqCStore_refl
    symmetry proved by EqCStore_sym
    transitivity proved by EqCStore_trans
      as EqCStore_rel.

(** Enable rewriting [MapsTo id v (cstore σ1)] into  
    [MapsTo id v (cstore σ2)] if [EqSStore σ1 σ2]. *)

Add Parametric Morphism (id : ident) (σ__c : DState) : (fun σ => MapsTo id σ__c (cstore σ)) 
    with signature (@EqCStore ==> impl) as eqcstore_mapsto_mor.
Proof. intros x y H; unfold EqCStore in H; erewrite H; unfold impl; eauto. Qed.

(** *** Events Set Equivalence *)

Definition EqEvs (σ σ' : DState) :=
  NatSet.Equal (events σ) (events σ').

Definition EqEvs_refl : forall (σ : DState), EqEvs σ σ. firstorder. Defined.
Definition EqEvs_trans : forall (σ σ' σ'' : DState), EqEvs σ σ' -> EqEvs σ' σ'' -> EqEvs σ σ''.
  unfold EqEvs; intros; transitivity (events σ'); auto.
Defined.
Definition EqEvs_sym : forall (σ σ' : DState), EqEvs σ σ' -> EqEvs σ' σ.
  unfold EqEvs; symmetry; auto.
Defined.

Add Parametric Relation : (DState) (EqEvs)
    reflexivity proved by EqEvs_refl
    symmetry proved by EqEvs_sym
    transitivity proved by EqEvs_trans
      as EqEvs_rel.

(** Enable rewriting [(events σ1)] into  
    [(events σ2)] if [EqEvs σ1 σ2]. *)

Add Parametric Morphism : (events) 
    with signature (@EqEvs ==> Equal) as eqevs_events_mor.
Proof. unfold EqEvs; auto. Qed.

(** *** Design State Equivalence *)

Definition EqDState (σ σ' : DState) :=
  EqSStore σ σ' /\ EqCStore σ σ' /\ EqEvs σ σ'.

Definition EqDState_refl : forall (σ : DState), EqDState σ σ. firstorder. Defined.
Definition EqDState_trans : forall (σ σ' σ'' : DState), EqDState σ σ' -> EqDState σ' σ'' -> EqDState σ σ''.
  unfold EqDState; intros; decompose [and] H; decompose [and] H0.
  split_and; transitivity σ'; auto.
Defined.
Definition EqDState_sym : forall (σ σ' : DState), EqDState σ σ' -> EqDState σ' σ.
  unfold EqDState; intros; decompose [and] H.
  split_and; symmetry; auto.
Defined.

Add Parametric Relation : (DState) (EqDState)
    reflexivity proved by EqDState_refl
    symmetry proved by EqDState_sym
    transitivity proved by EqDState_trans
      as EqDState_rel.

(** Enable rewriting [MapsTo id v (sstore σ1)] into  
    [MapsTo id v (sstore σ2)] if [EqDState σ1 σ2]. *)

Add Parametric Morphism (id : ident) (v : value) : (fun σ => MapsTo id v (sstore σ)) 
    with signature (@EqDState ==> impl) as eqdstate_mapsto_sstore_mor.
Proof. intros x y H; apply proj1 in H; intro; pattern y; rewrite <- H; auto. Qed.

(** Enable rewriting [MapsTo id σ__c (cstore σ1)] into  
    [MapsTo id σ__c (cstore σ2)] if [EqDState σ1 σ2]. *)

Add Parametric Morphism (id : ident) (σ__c : DState) : (fun σ => MapsTo id σ__c (cstore σ)) 
    with signature (@EqDState ==> impl) as eqdstate_mapsto_cstore_mor.
Proof. intros x y H; apply proj2, proj1 in H; intro; pattern y; rewrite <- H; auto. Qed.

(** Enable rewriting [events σ1] into [events σ2] if [EqDState σ1 σ2]. *)

Add Parametric Morphism : (events) 
    with signature (@EqDState ==> Equal) as eqdstate_events_mor.
Proof. intros x y H; apply proj2, proj2 in H; rewrite <- H; reflexivity. Qed.

(** ** Facts about [EqualDom] equivalence *)

Lemma EqualDom_add_1 :
  forall {A : Type} {k} {e : A} {m},
    NatMap.In k m ->
    EqualDom m (NatMap.add k e m).
Proof.
  split; intros.
  destruct (Nat.eq_dec k k0); try subst.
  exists e; apply NatMap.add_1; auto.
  rewrite add_in_iff; right; auto.
  destruct (Nat.eq_dec k k0); try subst; auto.
  erewrite add_in_iff in *; firstorder.
Qed.

(** ** Facts about [merge_natmap] *)

Ltac simpl_merge_map :=
  unfold merge_natmap;
  unfold fold;
  unfold Raw.fold;
  unfold flip;
  try (progress simpl).

Lemma merge_natmap_id_notin_set :
  forall {A : Type} (s : list ident) (m1 m2 : IdMap A) (k : ident) (a : A),
    let f := fun m k1 =>
               match find k1 m1 with
               | Some a1 => NatMap.add k1 a1 m
               | _ => m
               end
    in
    ~InA Logic.eq k s ->
    MapsTo k a m2 ->
    MapsTo k a (fold_left f s m2).
Proof.
  induction s.

  (* BASE CASE *)
  - simpl; auto.

  (* IND. CASE *)
  - simpl; intros.
    eapply IHs; eauto.
    destruct (find (elt:=A) a m1); auto.
    eapply NatMap.add_2; eauto.
Qed.

Lemma merge_natmap_id_notin_set_2 :
  forall {A : Type} {s m1 m2 k} {x y : A},
    let f := fun m k1 => match find k1 m1 with
                         | Some a1 => NatMap.add k1 a1 m
                         | _ => m
                         end
    in
    ~InA Logic.eq k s ->
    MapsTo k x m2 ->
    MapsTo k y (fold_left f s m2) ->
    x = y.
Proof.
  induction s.

  (* BASE CASE *)
  - simpl; intros; eapply MapsTo_fun; eauto.

  (* IND. CASE *)
  - simpl; intros.
    eapply IHs with (m2 := match find (elt:=A) a m1 with
            | Some a1 => NatMap.add a a1 m2
            | None => m2
                           end);
      eauto.
    destruct (find (elt:=A) a m1); auto.
    eapply NatMap.add_2; eauto.
Qed.

Lemma merge_natmap_notin_m1 :
  forall {A : Type} {s m1 m2 k} {a : A},
    let f := fun m k1 => match find k1 m1 with
                         | Some a1 => NatMap.add k1 a1 m
                         | _ => m
                         end
    in
    ~NatMap.In k m1 ->
    MapsTo k a (fold_left f s m2) ->
    NatMap.In k m2.
Proof.
  induction s; simpl; intros.
  (* BASE CASE *)
  - exists a; auto.
  (* IND. CASE *)
  - case_eq (find (elt:=A) a m1).
    (* find = Some x *)
    intros x e.
    erewrite <- add_neq_in_iff with (x := a) (e := x); eauto.
    rewrite e in *; eapply IHs; eauto.
    intros e1; try subst.
    match goal with
    | [ H: ~NatMap.In _ _ |- _ ] =>
      apply H; exists x; eapply find_2; eauto
    end.    
    (* find = None *)
    intros e; rewrite e in *; eapply IHs; eauto.
Qed.

Lemma merge_natmap_EqualDom_1 :
  forall {A: Type} {s m1 m2 m3},
    EqualDom m3 m1 ->
    EqualDom m3 m2 ->
    EqualDom m1 (@merge_natmap A s m2 m3).
Proof.
  destruct s; induction this0.
  (* BASE CASE *)
  - simpl_merge_map; intros; firstorder. 
  (* IND. CASE *)
  - simpl_merge_map; intros; case_eq (find (elt:=A) a m2); intros; eapply IHthis0; eauto.
    rewrite <- H; symmetry; eapply EqualDom_add_1; eauto.
    rewrite (H0 a); exists a0; eapply find_2; eauto.
    rewrite <- H0; symmetry; eapply EqualDom_add_1; eauto.
    rewrite (H0 a); exists a0; eapply find_2; eauto.
    Unshelve.
    inversion_clear is_ok0; auto.
    inversion_clear is_ok0; auto.
Qed.

Lemma merge_natmap_compl_1 :
  forall {A : Type} s m1 m2 k (a : A),
    NatSet.In k s ->
    MapsTo k a m1 ->
    MapsTo k a (merge_natmap s m1 m2).
Proof.
  destruct s; induction this0.
  (* BASE CASE *)
  - inversion 1.
  (* IND. CASE *)
  - intros; unfold merge_natmap; unfold fold; unfold Raw.fold; unfold flip.
    simpl.
    inversion_clear H; try subst.
    (* k = a *)
    + erewrite find_1; eauto.
      eapply merge_natmap_id_notin_set; eauto.
      inversion_clear is_ok0; auto.
      eapply NatMap.add_1; eauto.
    (* use ind. hyp. *)
    + eapply IHthis0; eauto.
      Unshelve.
      inversion_clear is_ok0; auto.
Qed.

Lemma merge_natmap_compl_2 :
  forall {A : Type} s m1 m2 k (a : A),
    ~NatSet.In k s ->
    MapsTo k a m2 ->
    MapsTo k a (merge_natmap s m1 m2).
Proof.
  unfold merge_natmap; unfold fold; unfold Raw.fold; unfold flip.
  intros; eapply merge_natmap_id_notin_set; eauto.
Qed.

Lemma merge_natmap_sound_1 :
  forall {A : Type} s m1 m2 k (a : A),
    NatSet.In k s ->
    EqualDom m1 m2 ->
    MapsTo k a (merge_natmap s m1 m2) ->
    MapsTo k a m1.
Proof.
  destruct s; induction this0.
  (* BASE CASE *)
  - inversion 1.
  (* IND. CASE *)
  - simpl_merge_map; inversion_clear 1; try subst.
    (* CASE k = a *)
    + case_eq (find (elt:=A) a m1). 
      (* find = Some a *)
      intros x e EqualDom_m1m2 MapsTo_foldl.
      erewrite <- @merge_natmap_id_notin_set_2 with (k := a) (x := x) (y := a0); eauto;
        [ eapply find_2; eauto | inversion is_ok0; auto | eapply NatMap.add_1; eauto].
      (* find = None *)
      intros e EqualDom_m1m2 MapsTo_foldl.
      assert (NatMap.In a m2) by (eapply merge_natmap_notin_m1; eauto;
                                  erewrite not_find_in_iff; eauto).
      assert (~NatMap.In a m1) by (erewrite not_find_in_iff; eauto).
      assert (NatMap.In a m1) by (unfold EqualDom in EqualDom_m1m2; erewrite EqualDom_m1m2; eauto).
      contradiction.

    (* CASE use ind. hyp. *)
    + intros EqualDom_m1m2 MapsTo_foldl;
        eapply IHthis0 with (m2 := match find (elt:=A) a m1 with
                                   | Some a1 => NatMap.add a a1 m2
                                   | None => m2 end);
        eauto.
      case_eq (find (elt:=A) a m1); auto.
      intros x e; split; erewrite add_in_iff.
      right; unfold EqualDom in EqualDom_m1m2; erewrite <- EqualDom_m1m2; assumption.
      inversion_clear 1; [ try subst | unfold EqualDom in EqualDom_m1m2; erewrite EqualDom_m1m2; assumption].
      exists x; eapply find_2; assumption.
      Unshelve. inversion_clear is_ok0; auto.
Qed.

Lemma merge_natmap_sound_2 :
  forall {A : Type} s m1 m2 k (a : A),
    ~NatSet.In k s ->
    EqualDom m1 m2 ->
    MapsTo k a (merge_natmap s m1 m2) ->
    MapsTo k a m2.
Proof.
  destruct s; induction this0.
  (* BASE CASE *)
  - simpl_merge_map; auto.
  (* IND. CASE *)
  - simpl_merge_map; do 5 intro; intros EqualDom_m1m2; intros.
    case_eq (find (elt:=A) a m1). 
    (* find = Some a *)
    intros x e; rewrite e in *.
    eapply NatMap.add_3 with (x := a) (e' := x).
    intro; try subst; apply H; auto with set.
    eapply IHthis0; eauto.
    intro; apply H; eapply InA_cons_tl; auto.
    erewrite EqualDom_m1m2.
    eapply EqualDom_add_1.
    unfold  EqualDom in EqualDom_m1m2.
    erewrite <- EqualDom_m1m2.
    exists x; eapply find_2; eauto.
    (* find = None *)
    intros e; rewrite e in *.
    eapply IHthis0; eauto.
    intro; apply H; eapply InA_cons_tl; auto.
    Unshelve. inversion_clear is_ok0; auto.
    inversion_clear is_ok0; auto.
Qed.

Lemma merge_sstore_compl_1 :
  forall {id v σ__o σ σ'},
    In id (events σ) ->
    MapsTo id v (sstore σ) ->
    MapsTo id v (merge_sstore σ__o σ σ').
Proof.
  unfold merge_sstore; intros.
  eapply merge_natmap_compl_1; eauto.
Qed.

Lemma merge_sstore_compl_2 :
  forall {id v σ__o σ σ'},
    ~In id (events σ) ->
    In id (events σ') ->
    MapsTo id v (sstore σ') ->
    MapsTo id v (merge_sstore σ__o σ σ').
Proof.
  unfold merge_sstore; intros.
  eapply merge_natmap_compl_2; eauto.
  eapply merge_natmap_compl_1; eauto.
Qed.

Lemma merge_sstore_compl_3 :
  forall {id v σ__o σ σ'},
    ~In id (events σ U events σ') ->
    MapsTo id v (sstore σ__o) ->
    MapsTo id v (merge_sstore σ__o σ σ').
Proof.
  intros; eapply merge_natmap_compl_2; eauto.
  eapply proj1; eapply not_in_union_2; eauto.
  eapply merge_natmap_compl_2; eauto.
  eapply proj2; eapply not_in_union_2; eauto.
Qed.

Lemma merge_sstore_sound_1 :
  forall {id v σ__o σ σ'},
    EqualDom (sstore σ__o) (sstore σ) ->
    EqualDom (sstore σ__o) (sstore σ') ->
    In id (events σ) ->
    MapsTo id v (merge_sstore σ__o σ σ') ->
    MapsTo id v (sstore σ).
Proof.
  intros; eapply merge_natmap_sound_1; eauto.
  eapply merge_natmap_EqualDom_1; eauto.
Qed.

Lemma merge_sstore_sound_2 :
  forall {id v σ__o σ σ'},
    EqualDom (sstore σ__o) (sstore σ) ->
    EqualDom (sstore σ__o) (sstore σ') ->
    In id (events σ') ->
    ~In id (events σ) ->
    MapsTo id v (merge_sstore σ__o σ σ') ->
    MapsTo id v (sstore σ').
Proof.
  intros; eapply merge_natmap_sound_1 with (m2 := (sstore σ__o)); eauto.
  symmetry; auto.
  eapply merge_natmap_sound_2; eauto.
  eapply merge_natmap_EqualDom_1; eauto.
Qed.

Lemma merge_sstore_sound_3 :
  forall {id v σ__o σ σ'},
    EqualDom (sstore σ__o) (sstore σ) ->
    EqualDom (sstore σ__o) (sstore σ') ->
    ~In id (events σ U events σ') ->
    MapsTo id v (merge_sstore σ__o σ σ') ->
    MapsTo id v (sstore σ__o).
Proof.
  unfold merge_sstore; intros.
  eapply merge_natmap_sound_2 with (s := events σ') (m1 := sstore σ'); eauto.
  eapply not_in_union_2; eauto.
  symmetry; assumption.
  eapply merge_natmap_sound_2 with (s := events σ) (m1 := sstore σ); eauto.
  eapply not_in_union_2 with (s := events σ) (s' := events σ'); eauto.
  eapply merge_natmap_EqualDom_1; eauto.
Qed.

Lemma merge_cstore_compl_1 :
  forall {id v σ__o σ σ'},
    In id (events σ) ->
    MapsTo id v (cstore σ) ->
    MapsTo id v (merge_cstore σ__o σ σ').
Proof.
  intros; eapply merge_natmap_compl_1; eauto.
Qed.

Lemma merge_cstore_compl_2 :
  forall {id v σ__o σ σ'},
    ~In id (events σ) ->
    In id (events σ') ->
    MapsTo id v (cstore σ') ->
    MapsTo id v (merge_cstore σ__o σ σ').
Proof.
  intros; eapply merge_natmap_compl_2; eauto.
  eapply merge_natmap_compl_1; eauto.
Qed.

Lemma merge_cstore_compl_3 :
  forall {id v σ__o σ σ'},
    ~In id (events σ U events σ') ->
    MapsTo id v (cstore σ__o) ->
    MapsTo id v (merge_cstore σ__o σ σ').
Proof.
  intros; eapply merge_natmap_compl_2; eauto.
  eapply proj1; eapply not_in_union_2; eauto.
  eapply merge_natmap_compl_2; eauto.
  eapply proj2; eapply not_in_union_2; eauto.
Qed.

Lemma merge_cstore_sound_1 :
  forall {id v σ__o σ σ'},
    EqualDom (cstore σ__o) (cstore σ) ->
    EqualDom (cstore σ__o) (cstore σ') ->
    In id (events σ) ->
    MapsTo id v (merge_cstore σ__o σ σ') ->
    MapsTo id v (cstore σ).
Proof.
  intros; eapply merge_natmap_sound_1; eauto.
  eapply merge_natmap_EqualDom_1; eauto.
Qed.

Lemma merge_cstore_sound_2 :
  forall {id v σ__o σ σ'},
    EqualDom (cstore σ__o) (cstore σ) ->
    EqualDom (cstore σ__o) (cstore σ') ->
    In id (events σ') ->
    ~In id (events σ) ->
    MapsTo id v (merge_cstore σ__o σ σ') ->
    MapsTo id v (cstore σ').
Proof.
  unfold merge_sstore; intros.
  eapply merge_natmap_sound_1 with (m2 := (cstore σ__o)); eauto.
  symmetry; auto.
  eapply merge_natmap_sound_2; eauto.
  eapply merge_natmap_EqualDom_1; eauto.
Qed.

Lemma merge_cstore_sound_3 :
  forall {id v σ__o σ σ'},
    EqualDom (cstore σ__o) (cstore σ) ->
    EqualDom (cstore σ__o) (cstore σ') ->
    ~In id (events σ U events σ') ->
    MapsTo id v (merge_cstore σ__o σ σ') ->
    MapsTo id v (cstore σ__o).
Proof.
  unfold merge_sstore; intros.
  eapply merge_natmap_sound_2 with (s := events σ') (m1 := cstore σ'); eauto.
  eapply not_in_union_2; eauto.
  symmetry; assumption.
  eapply merge_natmap_sound_2 with (s := events σ) (m1 := cstore σ); eauto.
  eapply not_in_union_2 with (s := events σ) (s' := events σ'); eauto.
  eapply merge_natmap_EqualDom_1; eauto.
Qed.

(** ** Facts about the [IsMergedDState] relation *)

Ltac decompose_IMDS :=
  match goal with
  | [ H: IsMergedDState _ _ _ _ |- _ ] =>
    unfold IsMergedDState in H; decompose [and] H; clear H
  end.

Lemma IsMergedDState_comm :
  forall {σ__o σ σ' σ__m},
    IsMergedDState σ__o σ σ' σ__m <->
    IsMergedDState σ__o σ' σ σ__m.
Proof.
  split; intros; decompose_IMDS;
    let rec solve_imds :=
        match goal with
        | |- IsMergedDState _ _ _ _ => split; solve_imds
        | |- _ /\ _ => split; [solve_imds | solve_imds]
        | |- _ -> _ -> ~NatSet.In _ (_ U _) -> _ <-> _ =>
          intros;
            match goal with
            | [ H: _ -> _ -> ~NatSet.In _ _ -> _ <-> MapsTo _ _ (?f _), H': ~NatSet.In _ _ |- _ <-> MapsTo _ _ (?f _) ] =>
              apply H; auto; do 1 intro; apply H';
                match goal with
                | [ H'': NatSet.In _ (_ U _) |- _ ] =>
                  rewrite union_spec in H''; inversion H''; rewrite union_spec; [right; assumption | left; assumption]
                end
            end
        | |- Equal _ (events ?σ U events ?σ') =>
          transitivity (events σ' U events σ); auto with set
        | _ => firstorder
        end in solve_imds.
Qed.

Lemma IsMergedDState_ex :
  forall {σ__o σ σ'},
    EqualDom (sstore σ__o) (sstore σ) ->
    EqualDom (sstore σ__o) (sstore σ') ->
    EqualDom (cstore σ__o) (cstore σ) ->
    EqualDom (cstore σ__o) (cstore σ') ->
    Equal (inter (events σ) (events σ')) {[]} -> 
    exists σ__m, IsMergedDState σ__o σ σ' σ__m.
Proof.
  unfold IsMergedDState; intros.
  exists (MkDState (merge_sstore σ__o σ σ') (merge_cstore σ__o σ σ') (events σ U events σ')).
  simpl; split_and; (auto || (try reflexivity)).
  - eapply merge_natmap_EqualDom_1; symmetry;
      eapply merge_natmap_EqualDom_1; (eauto || reflexivity).
  - eapply merge_natmap_EqualDom_1; symmetry;
      eapply merge_natmap_EqualDom_1; (eauto || reflexivity).
  - split; [eapply merge_sstore_compl_1; eauto | eapply merge_sstore_sound_1; eauto].
  - split; [ eapply merge_sstore_compl_2; eauto; eapply inter_empty_2; eauto
           | eapply merge_sstore_sound_2; eauto; eapply inter_empty_2; eauto].
  - split; [ eapply merge_sstore_compl_3; eauto | eapply merge_sstore_sound_3; eauto].
  - split; [ eapply merge_cstore_compl_1; eauto | eapply merge_cstore_sound_1; eauto].
  - split; [ eapply merge_cstore_compl_2; eauto; eapply inter_empty_2; eauto
           | eapply merge_cstore_sound_2; eauto; eapply inter_empty_2; eauto ].
  - split; [ eapply merge_cstore_compl_3; eauto | eapply merge_cstore_sound_3; eauto ].
Qed.

Lemma IsMergedDState_assoc_1 :
  forall {σ σ0 σ1 σ2 σ12 σ01 σ012},
    IsMergedDState σ σ1 σ2 σ12 ->
    IsMergedDState σ σ0 σ12 σ012 ->
    IsMergedDState σ σ0 σ1 σ01 ->
    IsMergedDState σ σ01 σ2 σ012.
Proof.
  intros;
    do 3 decompose_IMDS;
    let rec solve_imds :=
        match goal with
        | |- IsMergedDState _ _ _ _ => split; solve_imds
        | |- _ /\ _ => split; [solve_imds | solve_imds]
        | |- Equal _ (events ?σ U events ?σ') => 
          match goal with
          | [ H: Equal ?ev012 (_ U ?ev12), H': Equal ?ev01 _, H'': Equal ?ev12 _
              |- Equal ?ev012 (?ev01 U _) ] =>
            rewrite H; rewrite H'; rewrite H''; auto with set
          end
        | _ => auto
        end in solve_imds.

        (* [∀ id ∈ (events σ01) -> (sstore σ01) (id) = (sstore σ012) (id)] *)
        - intros;
            match goal with
            | [ H: Equal (events ?σ) (_ U _), H': NatSet.In _ (_ ?σ) |- MapsTo _ _ (_ ?σ) <-> _ ] =>
              rewrite H, union_spec in H'; inversion H'
            end.

          (* CASE [id ∈ (events σ0)] *)
          transitivity (MapsTo id v (sstore σ0)); rw_mapsto.
          
          (* CASE [id ∈ (events σ1) ] *)
          transitivity (MapsTo id v (sstore σ1)); [rw_mapsto | auto].
          transitivity (MapsTo id v (sstore σ12)); rw_mapsto;
            match goal with
            | [ H: Equal (events ?σ12) _ |- NatSet.In _ (events ?σ12) ] =>
              rewrite H; auto with set
            end.

        (* [∀ id ∈ (events σ2) -> (sstore σ2) (id) = (sstore σ012) (id)] *)
        - intros;
            transitivity (MapsTo id v (sstore σ12)); rw_mapsto;
              match goal with
              | [ H: Equal (events ?σ12) _ |- NatSet.In _ (events ?σ12) ] =>
                rewrite H; auto with set
              end.

        (* [∀ id ∉ (events σ01) U (events σ2) -> (sstore σ) (id) = (sstore σ012) (id)] *)
        - intros id v; intros; rw_mapsto.
          match goal with
          | [ H: Equal (events ?σ12) _, H': Equal (events ?σ01) _, H'': ~NatSet.In _ (events ?σ01 U _)
              |- ~NatSet.In _ (_ U events ?σ12) ] =>
            rewrite H' in H''; rewrite H; erewrite <- union_assoc; eauto
          end.

        (* [∀ id ∈ (events σ01) -> (cstore σ01) (id) = (cstore σ012) (id)] *)
        - intros id v; intros;
            match goal with
            | [ H: Equal (events ?σ) (_ U _), H': NatSet.In _ (_ ?σ) |- MapsTo _ _ (_ ?σ) <-> _ ] =>
              rewrite H, union_spec in H'; inversion H'
            end.

          (* CASE [id ∈ (events σ0)] *)
          transitivity (MapsTo id v (cstore σ0)); rw_mapsto.
          
          (* CASE [id ∈ (events σ1) ] *)
          transitivity (MapsTo id v (cstore σ1)); [rw_mapsto | auto].
          transitivity (MapsTo id v (cstore σ12)); rw_mapsto;
            match goal with
            | [ H: Equal (events ?σ12) _ |- NatSet.In _ (events ?σ12) ] =>
              rewrite H; auto with set
            end.

        (* [∀ id ∈ (events σ2) -> (cstore σ2) (id) = (cstore σ012) (id)] *)
        - intros id v; intros;
            transitivity (MapsTo id v (cstore σ12)); rw_mapsto;
              match goal with
              | [ H: Equal (events ?σ12) _ |- NatSet.In _ (events ?σ12) ] =>
                rewrite H; auto with set
              end.

        (* [∀ id ∉ (events σ01) U (events σ2) -> (cstore σ) (id) = (cstore σ012) (id)] *)
        - intros id v; intros; rw_mapsto.
          match goal with
          | [ H: Equal (events ?σ12) _, H': Equal (events ?σ01) _, H'': ~NatSet.In _ (events ?σ01 U _)
              |- ~NatSet.In _ (_ U events ?σ12) ] =>
            rewrite H' in H''; rewrite H; erewrite <- union_assoc; eauto
          end.
Qed.

Lemma IsMergedDState_assoc_2 :
  forall {σ σ0 σ1 σ2 σ12 σ01 σ012},
    IsMergedDState σ σ0 σ1 σ01 ->
    IsMergedDState σ σ01 σ2 σ012 ->
    IsMergedDState σ σ1 σ2 σ12 ->
    IsMergedDState σ σ0 σ12 σ012.
Proof.
  intros;
    do 3 decompose_IMDS;
    let rec solve_imds :=
        match goal with
        | |- IsMergedDState _ _ _ _ => split; solve_imds
        | |- _ /\ _ => split; [solve_imds | solve_imds]
        | |- Equal _ (events ?σ U events ?σ') =>
          match goal with
          | [ H: Equal ?ev012 (?ev01 U _), H': Equal ?ev01 _, H'': Equal ?ev12 _
              |- Equal ?ev012 (_ U ?ev12) ] =>
            rewrite H; rewrite H'; rewrite H''; auto with set
          end
        | _ => auto
        end in solve_imds.

        (* [∀ id ∈ (events σ0) -> (sstore σ0) (id) = (sstore σ012) (id)] *)
        - intros;
            transitivity (MapsTo id v (sstore σ01)); rw_mapsto;
              match goal with
              | [ H: Equal (events ?σ01) _ |- NatSet.In _ (events ?σ01) ] =>
                rewrite H; auto with set
              end.
        
        (* [∀ id ∈ (events σ12) -> (sstore σ12) (id) = (sstore σ012) (id)] *)
        - intros;
          match goal with
          | [ H: Equal (events ?σ) (_ U _), H': NatSet.In _ (_ ?σ) |- MapsTo _ _ (_ ?σ) <-> _ ] =>
            rewrite H, union_spec in H'; inversion H'
          end.

          (* CASE [id ∈ (events σ1)] *)
          transitivity (MapsTo id v (sstore σ1)); [ rw_mapsto | auto].
          transitivity (MapsTo id v (sstore σ01)); rw_mapsto;
            match goal with
            | [ H: Equal (events ?σ12) _ |- NatSet.In _ (events ?σ12) ] =>
              rewrite H; auto with set
            end.
          
          (* CASE [id ∈ (events σ2) ] *)
          transitivity (MapsTo id v (sstore σ2)); rw_mapsto.
          
        (* [∀ id ∉ (events σ0) U (events σ12) -> (sstore σ) (id) = (sstore σ012) (id)] *)
        - intros id v; intros; rw_mapsto.
          match goal with
          | [ H: Equal (events ?σ01) _, H': Equal (events ?σ12) _, H'': ~NatSet.In _ (_ U events ?σ12)
              |- ~NatSet.In _ (events ?σ01 U _) ] =>
            rewrite H' in H''; rewrite H; erewrite union_assoc; eauto
          end.

        (* [∀ id ∈ (events σ0) -> (cstore σ0) (id) = (cstore σ012) (id)] *)
        - intros id v; intros;
            transitivity (MapsTo id v (cstore σ01)); rw_mapsto;
              match goal with
              | [ H: Equal (events ?σ01) _ |- NatSet.In _ (events ?σ01) ] =>
                rewrite H; auto with set
              end.
          
        (* [∀ id ∈ (events σ12) -> (cstore σ12) (id) = (cstore σ012) (id)] *)
        - intros id v; intros;
            match goal with
            | [ H: Equal (events ?σ) (_ U _), H': NatSet.In _ (_ ?σ) |- MapsTo _ _ (_ ?σ) <-> _ ] =>
              rewrite H, union_spec in H'; inversion H'
            end.

          (* CASE [id ∈ (events σ1)] *)
          transitivity (MapsTo id v (cstore σ1)); [ rw_mapsto | auto].
          transitivity (MapsTo id v (cstore σ01)); rw_mapsto;
            match goal with
            | [ H: Equal (events ?σ12) _ |- NatSet.In _ (events ?σ12) ] =>
              rewrite H; auto with set
            end.
          
          (* CASE [id ∈ (events σ2) ] *)
          transitivity (MapsTo id v (cstore σ2)); rw_mapsto.
          
        (* [∀ id ∉ (events σ0) U (events σ12) -> (cstore σ) (id) = (cstore σ012) (id)] *)
        - intros id v; intros; rw_mapsto.
          match goal with
          | [ H: Equal (events ?σ01) _, H': Equal (events ?σ12) _, H'': ~NatSet.In _ (_ U events ?σ12)
              |- ~NatSet.In _ (events ?σ01 U _) ] =>
            rewrite H' in H''; rewrite H; erewrite union_assoc; eauto
          end.
Qed.

