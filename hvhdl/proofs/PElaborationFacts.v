(** * Facts about Elaboration of Place Design *)

Require Import common.CoqLib.
Require Import common.NatMap.
Require Import common.InAndNoDup.

Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.proofs.AbstractSyntaxFacts.
Require Import hvhdl.Environment.
Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.HVhdlElaborationLib.
Require Import hvhdl.WellDefinedDesign.

Require Import hvhdl.proofs.WellDefinedDesignFacts.
Require Import hvhdl.Place.
Require Import hvhdl.HilecopDesignStore.
Require Import hvhdl.proofs.ArchitectureElaborationFacts.
Require Import hvhdl.proofs.DesignElaborationFacts.
Require Import hvhdl.proofs.PArchitectureElaborationFacts.

(** ** Facts about the [output_arcs_number] generic constant *)

Lemma elab_PCI_Δ_out_arcs_nb_1 :
  forall {d Δ σ__e id__p gm ipm opm Δ__p},
    EDesign hdstore (NatMap.empty value) d Δ σ__e ->
    InCs (cs_comp id__p Petri.place_id gm ipm opm) (behavior d) ->
    MapsTo id__p (Component Δ__p) Δ ->
    exists t n, MapsTo Place.output_arcs_number (Generic t (Vnat n)) Δ__p.
Admitted.

Lemma elab_PCI_Δ_out_arcs_nb_2 :
  forall {d Δ σ__e id__p gm ipm opm Δ__p e v},
    EDesign hdstore (NatMap.empty value) d Δ σ__e ->
    InCs (cs_comp id__p Petri.place_id gm ipm opm) (behavior d) ->
    MapsTo id__p (Component Δ__p) Δ ->
    List.In (assocg_ Place.output_arcs_number e) gm ->
    VExpr EmptyElDesign EmptyDState EmptyLEnv false e v ->
    exists t, MapsTo Place.output_arcs_number (Generic t v) Δ__p.
Admitted.

(** ** Facts about the [s_marking] declared signal *)

Lemma elab_place_Δ_s_marking :
  forall {M__g Δ σ__e},
    EDesign hdstore M__g place_design Δ σ__e ->
    exists n, MapsTo Place.s_marking (Internal (Tnat 0 n)) Δ.
Proof.
  inversion 1; subst.
  edestruct @EDecls_P_Δ_s_marking with (Δ := Δ') as (n, MapsTo_Δ''); eauto.
  exists n; eapply EBeh_inv_Δ; eauto.
Qed.

Lemma EBeh_pcomp_Δ_s_marking : 
  forall {Δ σ behavior Δ' σ' id__p gm ipm opm Δ__p},
    EBeh hdstore Δ σ behavior Δ' σ' ->
    InCs (cs_comp id__p Petri.place_id gm ipm opm) behavior ->
    MapsTo id__p (Component Δ__p) Δ' ->
    exists n, MapsTo Place.s_marking (Internal (Tnat 0 n)) Δ__p.
Proof.
  induction 1; inversion 1.

  (* CASE comp *)
  - subst; subst_place_design.
    assert (e : Component Δ__p = Component Δ__c) by (eapply MapsTo_add_eqv; eauto).
    inject_left e.
    eapply @elab_place_Δ_s_marking; eauto.
    
  (* CASE left of || *)
  - intros.
    edestruct @EBeh_compid_in_comps with (D__s := hdstore) (behavior := cstmt) as (Δ__p', MapsTo_Δ__p'); eauto.
    assert (MapsTo id__p (Component Δ__p') Δ'') by (eapply EBeh_inv_Δ; eauto).
    assert (e : Component Δ__p = Component Δ__p') by (eapply MapsTo_fun; eauto).
    inject_left e; apply IHEBeh1; auto.
    
  (* CASE right of || *)
  - apply IHEBeh2; auto.
Qed.

Lemma elab_PCI_Δ_s_marking :
  forall {d Δ σ__e id__p gm ipm opm Δ__p},
    EDesign hdstore (NatMap.empty value) d Δ σ__e ->
    InCs (cs_comp id__p Petri.place_id gm ipm opm) (behavior d) ->
    MapsTo id__p (Component Δ__p) Δ ->
    exists n, MapsTo Place.s_marking (Internal (Tnat 0 n)) Δ__p.
Proof.
  inversion 1.
  eapply EBeh_pcomp_Δ_s_marking; eauto.
Qed.

(** ** Facts about the [initial_marking] input port *)

Lemma elab_PCI_Δ_init_marking :
  forall {d Δ σ__e id__p gm ipm opm Δ__p},
    EDesign hdstore (NatMap.empty value) d Δ σ__e ->
    InCs (cs_comp id__p Petri.place_id gm ipm opm) (behavior d) ->
    MapsTo id__p (Component Δ__p) Δ ->
    InputOf Δ__p initial_marking.
Proof.
  inversion 1; subst; intros; eapply @elab_input_of_comp with (d__e := place_design); eauto.
  apply add_2; [discriminate | apply add_1; auto].
  firstorder.
Qed.

(** ** Facts about the [reinit_transitions_time] output port *)

Lemma elab_PCI_σ_rtt : 
  forall {d Δ σ__e id__p gm ipm opm σ__pe},
    EDesign hdstore (NatMap.empty value) d Δ σ__e ->
    InCs (cs_comp id__p Petri.place_id gm ipm opm) (behavior d) ->
    MapsTo id__p σ__pe (cstore σ__e) ->
    exists aofv, MapsTo Place.reinit_transitions_time (Varr aofv) (sstore σ__pe).
Admitted.

Lemma elab_PCI_Δ_rtt : 
  forall {d Δ σ__e},
    EDesign hdstore (NatMap.empty value) d Δ σ__e ->
    forall {id__p gm ipm opm Δ__p t n},
      InCs (cs_comp id__p Petri.place_id gm ipm opm) (behavior d) ->
      MapsTo id__p (Component Δ__p) Δ ->
      MapsTo output_arcs_number (Generic t (Vnat n)) Δ__p ->
      MapsTo Place.reinit_transitions_time (Output (Tarray Tbool 0 (n - 1))) Δ__p.
Admitted.



