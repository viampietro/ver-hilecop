Require Import common.CoqLib.
Require Import common.StateAndErrorMonad.

Require Import sitpn.SitpnLib.

Require Import hvhdl.HVhdlCoreLib.

Require Import transformation.Sitpn2HVhdl.
Require Import transformation.proofs.SInvTactics.

Lemma gen_inter_p_comp_ex :
  forall (sitpn : Sitpn) (s : Sitpn2HVhdlState sitpn) v s' p,
    generate_interconnections s = OK v s' ->
    (exists id__p g__p i__p o__p,
        InA Pkeq (p, id__p) (p2pcomp (γ s))
        /\ InCs (cs_comp id__p Petri.place_entid g__p i__p o__p) (beh s)) -> 
    (exists id__p g__p i__p o__p,
        InA Pkeq (p, id__p) (p2pcomp (γ s'))
        /\ InCs (cs_comp id__p Petri.place_entid g__p i__p o__p) (beh s')).
Proof.
  
  intros *; intros H; pattern s, s'.
  solve_sinv_pattern.
Admitted.
