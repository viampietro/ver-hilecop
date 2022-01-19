(** * Architecture Generation and State Invariants *)

Require Import String.
Require Import common.CoqLib.
Require Import common.StateAndErrorMonad.
Require Import common.ListLib.
Require Import common.proofs.ListTacticsLib.
Require Import common.proofs.StateAndErrorMonadTactics.

Require Import sitpn.Sitpn.
Require Import sitpn.SitpnFacts.

Require Import hvhdl.Place.
Require Import hvhdl.AbstractSyntax.

Require Import transformation.Sitpn2HVhdl.
Require Import transformation.proofs.SInvTactics.

(** ** Facts about Architecture Generation Function *)

Lemma gen_arch_inv_lofPs :
  forall {sitpn mm s v s'},
    @generate_architecture sitpn mm s = OK v s' ->
    lofPs s = lofPs s'.
Proof. intros *; intros H; pattern s, s'; solve_sinv_pattern. Qed.

Lemma gen_arch_inv_lofTs :
  forall {sitpn mm s v s'},
    @generate_architecture sitpn mm s = OK v s' ->
    lofTs s = lofTs s'.
Proof. intros *; intros H; pattern s, s'; solve_sinv_pattern. Qed.

Lemma gen_arch_inv_sil_lofTs :
  forall {sitpn mm s v s'},
    @generate_architecture sitpn mm s = OK v s' ->
    Sig_in_List (lofTs s) -> Sig_in_List (lofTs s').
Proof. intros *; intros H; pattern s, s'; solve_sinv_pattern. Qed.

Lemma gen_tcis_p_comp_ex :
  forall (sitpn : Sitpn) (s : Sitpn2HVhdlState sitpn) v s' p,
    generate_tcis s = OK v s' ->
    (exists id__p g__p i__p o__p,
        InA Pkeq (p, id__p) (p2pcomp (γ s))
        /\ InCs (cs_comp id__p Petri.place_entid g__p i__p o__p) (beh s)) -> 
    (exists id__p g__p i__p o__p,
        InA Pkeq (p, id__p) (p2pcomp (γ s'))
        /\ InCs (cs_comp id__p Petri.place_entid g__p i__p o__p) (beh s')).
Proof. intros *; intros H; pattern s, s'; solve_sinv_pattern.
       inversion EQ1; subst; cbn.
       destruct 1 as [id__p [g__p [i__p [o__p [InA_ InCs_] ] ] ] ].
       exists id__p, g__p, i__p, o__p; split; [ assumption | (right; assumption) ].
Qed.
