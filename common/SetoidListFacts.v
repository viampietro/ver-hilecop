(** * More Facts about Setoid Lists *)

Require Import common.Coqlib.
Require Import common.ListPlus.
Require Import common.FstSplit.

(** ** Facts about [InA] *)

Section InAFacts.

  (** If a couple (a, b) is in the list of couples l 
      then a is in (fst (split l)). *)

  Lemma InA_fst_split {A B : Type} :
    forall {eqk : A -> A -> Prop} {eqv : B -> B -> Prop} {a l} (b : B),
      let eqkv := (fun x y => eqk (fst x) (fst y) /\ eqv (snd x) (snd y)) in
      InA eqkv (a, b) l -> InA eqk a (fst (split l)).
  Proof.
    induction l.
    - intros; inversion H.
    - elim a0; intros; rewrite fst_split_cons_app; simpl.
      inversion_clear H; apply InA_cons.
      + firstorder.
      + right; apply IHl with (b := b0); auto.
  Qed.

  Hint Resolve InA_fst_split : setoidl.
  Hint Extern 1 (InA _ _ (fs _)) => eapply InA_fst_split; eauto : setoidl.
  
  (* Version of [not_in_fst_split] for setoid lists. *)

  Lemma not_InA_fst_split {A B : Type} :
    forall {l : list (A * B)} {eqk : A -> A -> Prop} {eqv : B -> B -> Prop} {a : A},
      ~InA eqk a (fst (split l)) ->
      let eqkv := (fun x y => eqk (fst x) (fst y) /\ eqv (snd x) (snd y)) in
      (forall b : B, ~InA eqkv (a, b) l).
  Proof.
    induction l.
    - intros; intros Hin; inversion Hin.
    - elim a; intros; intros Hin.
      specialize (InA_fst_split b0 Hin) as Hnotin_a1.
      contradiction.
  Qed.

  Hint Resolve not_InA_fst_split : setoidl.
  
  Lemma InA_eqk :
    forall {A B : Type} {eqk : A -> A -> Prop} (eqv : B -> B -> Prop) {x y z l},
      eqk x y ->
      Equivalence eqk ->
      let eqkv := fun x y => eqk (fst x) (fst y) /\ eqv (snd x) (snd y) in
      InA eqkv (x, z) l ->
      InA eqkv (y, z) l.
  Proof.
    induction 3;
      [ destruct y0 as (a, b); apply InA_cons_hd; firstorder
      | apply InA_cons_tl; auto].
  Qed.

  Hint Resolve InA_eqk : setoidl.
  Hint Extern 1 (InA _ (_, _) _) => eapply InA_eqk; eauto : setoidl.
  
  Lemma InA_setv_inv_1 :
    forall {A B : Type} {x y : A} {z v : B} {eqk eqv l} {eqk_dec : forall x y, {eqk x y} + {~eqk x y}},
      let eqkv := (fun x y => eqk (fst x) (fst y) /\ eqv (snd x) (snd y)) in
      InA eqkv (x, z) l ->
      ~eqk x y ->
      Equivalence eqk ->
      InA eqkv (x, z) (setv eqk_dec y v l).
  Proof.
    induction 1.
    
    all: destruct y0; intros; simpl; destruct (eqk_dec y a); auto.
    destruct H as (Heqk, Heqv); simpl in Heqk.
    apply (Equivalence_Symmetric y a) in e.
    apply (Equivalence_Transitive x a y) in e; [contradiction | auto].
  Qed.

  Hint Resolve InA_setv_inv_1 : setoidl.
  
  Lemma InA_setv_inv_2 :
    forall {A B : Type} {eqk eqv} {eqk_dec : forall x y, {eqk x y} + {~eqk x y}} {y v l} {x : A} {z : B},
      let eqkv := (fun x y => eqk (fst x) (fst y) /\ eqv (snd x) (snd y)) in
      InA eqkv (x, z) (setv eqk_dec y v l) ->
      ~eqk x y ->
      Equivalence eqk ->
      InA eqkv (x, z) l.
  Proof.
    intros until l.
    functional induction (setv eqk_dec y v l) using setv_ind;
      intros *; intros InA_setv neqk Equiv_eqk.
    (* CASE l = [] *)
    inversion_clear InA_setv as [ y0 a and_ | a l InA_nil ];
      [ destruct and_; contradiction | inversion InA_nil ].
    (* CASE fst hd = y *)
    inversion_clear InA_setv as [ y0 l and_ | y0 l InA_tl ]; auto.
    destruct and_; contradiction.
    (* CASE ind. call *)
    inversion_clear InA_setv as [ y0 l and_ | y0 l InA_tl ]; auto.
  Qed.

  Hint Resolve InA_setv_inv_2 : setoidl.
  
  Lemma InA_setv :
    forall {A B : Type} {x : A} {z : B} {eqk eqv} {eqk_dec : forall x y, {eqk x y} + {~eqk x y}} {l},
      let eqkv := (fun x y => eqk (fst x) (fst y) /\ eqv (snd x) (snd y)) in
      Equivalence eqk ->
      Equivalence eqv ->
      InA eqkv (x, z) (setv eqk_dec x z l).
  Proof.
    intros until l.
    functional induction (setv eqk_dec x z l) using setv_ind; intros.
    1, 2: apply InA_cons_hd; firstorder.
    apply InA_cons_tl; apply IHl0; auto.
  Qed.

  Hint Resolve InA_setv : setoidl.
  
  Lemma InA_setv_fst_or_in_tl :
    forall {A B : Type} {y : A} {v2 : B} {eqk eqv} {eqk_dec : forall x y, {eqk x y} + {~eqk x y}} {l} {x v1},
      let eqkv := (fun x y => eqk (fst x) (fst y) /\ eqv (snd x) (snd y)) in
      InA eqkv (x, v1) (setv eqk_dec y v2 l) ->
      (eqk x y /\ eqv v1 v2) \/ InA eqkv (x, v1) l.
  Proof.
    intros until l; functional induction (setv eqk_dec y v2 l) using setv_ind.
    inversion_clear 1; [ left; auto | inversion H0 ].
    inversion_clear 1; [ left; auto | right; auto ].
    inversion_clear 1; [ right; auto | auto ].
    edestruct IHl0 as [and_ | InA_tl ]; eauto.
  Qed.
  
  Lemma InA_notin_fs_setv_inv {A B : Type} :
    forall {eqk : A -> A -> Prop} {eqk_dec : forall x y, {eqk x y} + {~eqk x y}}
           {y} (b : B) {l : list (A * B)} {x},
      Equivalence eqk ->
      ~InA eqk x (fs l) ->
      ~eqk y x ->
      ~InA eqk x (fs (setv eqk_dec y b l)).
  Proof.
    intros until l; functional induction (setv eqk_dec y b l) using setv_ind;
      rewrite fs_eq_cons_app ; simpl; intros; (rewrite fs_eq_cons_app; simpl; inversion_clear 1) || inversion_clear 1;
        [ apply Equivalence_Symmetric in H3; contradiction
        | apply H0; assumption
        | apply Equivalence_Symmetric in H3; contradiction
        | apply H0; auto
        | apply H0; auto
        | generalize H3; apply IHl0; auto
        ].
  Qed.

  Hint Resolve InA_notin_fs_setv_inv : setoidl.
  
  Lemma InA_neqA {A : Type} :
    forall {eqA : A -> A -> Prop} {x y} {l : list A},
      Equivalence eqA ->
      InA eqA x l ->
      ~InA eqA y l ->
      ~eqA x y.
  Proof. intros; intro; specialize (InA_eqA H H2 H0); contradiction. Qed.

  Hint Resolve InA_neqA : setoidl.
  
  Lemma nInA_eqA {A : Type} :
    forall {eqA : A -> A -> Prop} {x y} {l : list A},
      Equivalence eqA ->
      eqA x y ->
      ~InA eqA x l ->
      ~InA eqA y l.
  Proof.
    intros *; intros Equiv_eqA eqA_xy nInA InA_y.
    apply nInA; eauto; symmetry in eqA_xy; eauto.
    eapply InA_eqA; eauto.
  Qed.

  Hint Resolve nInA_eqA : setoidl.
  
  Lemma InA_fs_InA_fs_setv :
    forall {A B : Type} {eqk} {eqk_dec : forall x y : A, {eqk x y} + {~ eqk x y}} {y b}
           {l : list (A * B)} {x},
      Equivalence eqk ->
      InA eqk x (fs l) ->
      InA eqk x (fs (setv eqk_dec y b l)).
  Proof.
    intros until l; functional induction (setv eqk_dec y b l) using setv_ind.
    inversion 2.
    rewrite fs_eq_cons_app; cbn; intros x Equiv_eqk InA_.
    rewrite fs_eq_cons_app; cbn.
    inversion_clear InA_ as [z l eqk_xa | z l InA_tl]; [ | eauto].
    eapply InA_cons_hd; transitivity a; auto.
    symmetry; auto.
    rewrite fs_eq_cons_app; cbn; intros x Equiv_eqk InA_.
    rewrite fs_eq_cons_app; cbn.
    inversion InA_; auto.
  Qed.

  Hint Resolve nInA_eqA : setoidl.

  Lemma InA_setv_eqk :
    forall {A B : Type} {y : A} {z : B} {eqk : A -> A -> Prop} {eqv : B -> B -> Prop}
           {eqk_dec : forall x0 y0 : A, {eqk x0 y0} + {~ eqk x0 y0}} {l : list (A * B)} {x : A},
      let eqkv := fun x0 y : A * B => eqk (fst x0) (fst y) /\ eqv (snd x0) (snd y) in
      Equivalence eqk -> Equivalence eqv -> eqk x y -> InA eqkv (x, z) (setv eqk_dec y z l).
  Proof.
    intros until l; functional induction (setv eqk_dec y z l) using setv_ind.
    constructor 1; cbn; split; eauto with relations.
    constructor 1; cbn; split; eauto with relations.
    constructor 2; eauto.
  Qed.

  Hint Resolve InA_setv_eqk : setoidl.
  
End InAFacts.

Hint Resolve InA_fst_split : setoidl.
Hint Extern 1 (InA _ _ (fs _)) => eapply InA_fst_split; eauto : setoidl.
Hint Resolve not_InA_fst_split : setoidl.
Hint Resolve InA_eqk : setoidl.
Hint Extern 1 (InA _ (_, _) _) => eapply InA_eqk; eauto : setoidl.
Hint Resolve InA_setv_inv_1 : setoidl.
Hint Resolve InA_setv_inv_2 : setoidl.
Hint Resolve InA_setv : setoidl.
Hint Extern 1 (InA _ (?x, ?z) (setv _ ?x ?z _)) => apply InA_setv : setoidl.
Hint Resolve InA_notin_fs_setv_inv : setoidl.
Hint Resolve InA_neqA : setoidl.
Hint Resolve nInA_eqA : setoidl.
Hint Resolve InA_fs_InA_fs_setv : setoidl.
Hint Resolve InA_setv_eqk : setoidl.

(** ** Facts about [NoDupA] *)

Section NoDupAFacts.

  Lemma NoDupA_tl (A : Type) :
    forall {eqA : A -> A -> Prop} {a : A} {l : list A},
      NoDupA eqA (a :: l) ->
      NoDupA eqA l.
  Proof. inversion 1; auto. Qed.
  
  Lemma NoDupA_fs_tl (A B : Type) :
    forall {eqA : A -> A -> Prop} {a : A} {b : B} {l : list (A * B)},
      NoDupA eqA (fs ((a, b) :: l)) ->
      NoDupA eqA (fs l).
  Proof.  intros *; rewrite fs_eq_cons_app; simpl; inversion 1; auto. Qed.

  Hint Resolve NoDupA_tl : setoidl.
  Hint Resolve NoDupA_fs_tl : setoidl.
  
  Lemma NoDupA_fs_eqk_eq (A : Type) {B : Type} :
    forall {eqk : A -> A -> Prop} {l : list (A * B)} {a b b'},
      Equivalence eqk ->
      NoDupA eqk (fs l) ->
      let eqkv := (fun x y => eqk (fst x) (fst y) /\ eq (snd x) (snd y)) in
      InA eqkv (a, b) l ->
      InA eqkv (a, b') l ->
      eq b b'.
  Proof.
    induction l.
    
    (* BASE CASE *)
    - inversion 3.

    (* IND. CASE *)
    - intros.
      lazymatch goal with
      | [ H: NoDupA _ _ |- _ ] =>
        rewrite fs_eq_cons_app in H; destruct a as (a1, b1);
          simpl in H; inversion_clear H
      end.

      lazymatch goal with
      | [ H: InA _ (a0, b) _, H': InA _ (a0, b') _ |- _ ] =>
        inversion_clear H; inversion_clear H'
      end.

      (* 4 subgoals *)

      (* [(a0, b) = (a1, b1)] and [(a0, b') = (a1, b1)] *)
      + firstorder; transitivity b1; auto.

      (* [(a0, b) = (a1, b1)] and [(a0, b') ∈ l]. 
       Then, [eqk a0 a1], then [(a1, b') ∈ l], then [a1 ∈ (fs l)].
       Contradicts [a1 ∉ (fs l)].  *)
      + elimtype False; lazymatch goal with
                        | [ H: ~InA _ _ _ |- _ ] =>
                          apply H
                        end.
        apply (@InA_fst_split A B eqk eq a1 l b').
        eapply InA_eqk; eauto; firstorder.

      + elimtype False; lazymatch goal with
                        | [ H: ~InA _ _ _ |- _ ] =>
                          apply H
                        end.
        apply (@InA_fst_split A B eqk eq a1 l b).
        eapply InA_eqk; eauto; firstorder.

      + eapply IHl; eauto.
  Qed.

  Lemma NoDupA_setv_cons (A : Type) {B : Type} :
    forall {eqk : A -> A -> Prop} {eqk_dec : forall x y, {eqk x y} + {~eqk x y}} {a b} {l : list (A * B)},
      Equivalence eqk ->
      NoDupA eqk (fs l) ->
      NoDupA eqk (fs (setv eqk_dec a b l)).
  Proof.  
    intros until l; functional induction (setv eqk_dec a b l) using setv_ind.
    - intros; apply NoDupA_singleton.
    - intros Equiv_eqk NoDupA_; rewrite fs_eq_cons_app; cbn.
      apply NoDupA_cons; eauto with setoidl.
      rewrite fs_eq_cons_app in NoDupA_; cbn in NoDupA_.
      inversion_clear NoDupA_; eauto with setoidl.
      eapply nInA_eqA; eauto.
      symmetry; auto.
    - rewrite fs_eq_cons_app; cbn; intros Equiv_eqk NoDupA_.
      rewrite fs_eq_cons_app; cbn.
      eapply NoDupA_cons; inversion_clear NoDupA_; eauto with setoidl.
  Qed.
  
End NoDupAFacts.

Hint Rewrite NoDupA_fs_eqk_eq : setoidl.
Hint Resolve NoDupA_setv_cons : setoidl.
Hint Resolve NoDupA_tl : setoidl.
Hint Resolve NoDupA_fs_tl : setoidl.

(** ** Facts about both [InA] and [NoDupA] *)

Section InAAnDNoDupAFacts.

  Lemma neqk_if_InA_NoDupA (A : Type) {B : Type} :
    forall {eqk : A -> A -> Prop} {eqv : B -> B -> Prop} {l : list (A * B)} {x y : A} {b1 b2 : B},
      Equivalence eqk ->
      let eqkv := (fun x y => eqk (fst x) (fst y) /\ eqv (snd x) (snd y)) in
      InA eqkv (x, b1) l ->
      NoDupA eqk (fs ((y, b2) :: l)) ->
      ~eqk x y.
  Proof.
    intros *; rewrite fs_eq_cons_app; cbn.
    inversion_clear 3.
    eapply @InA_neqA with (x := x) (l := fs l); eauto with setoidl typeclass_instances.
  Qed.
  
  Hint Resolve neqk_if_InA_NoDupA : setoidl.
  Hint Extern 1 False => eapply neqk_if_InA_NoDupA; eauto : setoidl.
  
  Lemma eqv_if_InA_NoDupA_setv :
    forall {A B : Type} {eqk : A -> A -> Prop} {eqk_dec : forall x0 y : A, {eqk x0 y} + {~ eqk x0 y}}
           {x : A} {z : B} {l : list (A * B)} {y},
      let eqkv := fun x0 y : A * B => eqk (fst x0) (fst y) /\ eq (snd x0) (snd y) in
      Equivalence eqk -> InA eqkv (x, y) (setv eqk_dec x z l) -> NoDupA eqk (fs l) -> y = z.
  Proof.
    intros until l.
    functional induction (setv eqk_dec x z l) using setv_ind.
    (* CASE l = [(x, z)] *)
    inversion_clear 2 as [ (a, b) l eqkv_ | (a, b) l InA_ ];
      [ simpl in eqkv_; firstorder | inversion InA_ ].
    (* CASE l = [(x, z) :: tl] *)
    inversion_clear 2 as [ (a1, b1) l eqkv_ | (a1, b1) l InA_ ];
      [ simpl in eqkv_; firstorder | intros; exfalso ].
    eauto with setoidl.
    (* CASE l = [(x, z) :: tl] *)
    inversion_clear 2 as [ (a1, b1) l eqkv_ | (a1, b1) l InA_ ];
      [ simpl in eqkv_; destruct eqkv_; contradiction |
        intros; eapply IHl0; eauto with setoidl ].
  Qed.
  
End InAAnDNoDupAFacts.

Hint Resolve neqk_if_InA_NoDupA : setoidl.
Hint Extern 1 False => eapply neqk_if_InA_NoDupA; eauto : setoidl.
