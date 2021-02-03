(** * Facts about Elaboration of Place Design *)

Require Import common.Coqlib.
Require Import common.NatMap.
Require Import common.InAndNoDup.

Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.AbstractSyntaxFacts.
Require Import hvhdl.Environment.
Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.Elaboration.
Require Import hvhdl.WellDefinedDesign.
Require Import hvhdl.WellDefinedDesignFacts.
Require Import hvhdl.Place.
Require Import hvhdl.HilecopDesignStore.
Require Import hvhdl.ArchitectureElaborationFacts.
Require Import hvhdl.DesignElaborationFacts.

Lemma edecl_s_marking :
  forall {Δ σ Δ' σ'},
    edecl Δ σ (sdecl_ s_marking local_weight_t) Δ' σ' ->
    exists n, MapsTo s_marking (Declared (Tnat 0 n)) Δ'.
Proof.
  inversion 1.
  match goal with | [ H: etype _ _ _ |- _ ] => inversion H end.
  match goal with | [ H: econstr _ _ _ _ _ |- _ ] => inversion H end.
  match goal with | [ H: vexpr _ _ _ _ _ (Vnat n) |- _ ] => inversion H end.
  exists n'; apply add_1; auto.
Qed.

Lemma edecls_place_Δ_s_marking :
  forall {Δ σ Δ' σ'},
    edecls Δ σ place_sigs Δ' σ' ->
    exists n, MapsTo s_marking (Declared (Tnat 0 n)) Δ'.
Proof.
  inversion_clear 1.
  inversion_clear H1.
  edestruct @edecl_s_marking with (Δ := Δ'0); eauto.
  exists x; eapply edecls_inv_Δ; eauto.
Qed.

Lemma elab_place_Δ_s_marking :
  forall {M__g Δ σ__e},
    edesign hdstore M__g place_design Δ σ__e ->
    exists n, MapsTo Place.s_marking (Declared (Tnat 0 n)) Δ.
Proof.
  inversion 1; subst.
  edestruct @edecls_place_Δ_s_marking with (Δ := Δ') as (n, MapsTo_Δ''); eauto.
  exists n; eapply ebeh_inv_Δ; eauto.
Qed.

Lemma ebeh_pcomp_Δ_s_marking : 
  forall {Δ σ behavior Δ' σ' id__p gm ipm opm Δ__p},
    ebeh hdstore Δ σ behavior Δ' σ' ->
    InCs (cs_comp id__p Petri.place_entid gm ipm opm) behavior ->
    MapsTo id__p (Component Δ__p) Δ' ->
    exists n, MapsTo Place.s_marking (Declared (Tnat 0 n)) Δ__p.
Proof.
  induction 1; inversion 1.

  (* CASE comp *)
  - subst; subst_place_design.
    assert (e : Component Δ__p = Component Δ__c) by (eapply MapsTo_add_eqv; eauto).
    inject_left e.
    eapply @elab_place_Δ_s_marking; eauto.
    
  (* CASE left of || *)
  - intros.
    edestruct @ebeh_compid_in_comps with (D__s := hdstore) (behavior := cstmt) as (Δ__p', MapsTo_Δ__p'); eauto.
    assert (MapsTo id__p (Component Δ__p') Δ'') by (eapply ebeh_inv_Δ; eauto).
    assert (e : Component Δ__p = Component Δ__p') by (eapply MapsTo_fun; eauto).
    inject_left e; apply IHebeh1; auto.
    
  (* CASE right of || *)
  - apply IHebeh2; auto.
Qed.

Lemma elab_pcomp_Δ_s_marking :
  forall {d Δ σ__e id__p gm ipm opm Δ__p},
    edesign hdstore (NatMap.empty value) d Δ σ__e ->
    InCs (cs_comp id__p Petri.place_entid gm ipm opm) (behavior d) ->
    MapsTo id__p (Component Δ__p) Δ ->
    exists n, MapsTo Place.s_marking (Declared (Tnat 0 n)) Δ__p.
Proof.
  inversion 1.
  eapply ebeh_pcomp_Δ_s_marking; eauto.
Qed.
