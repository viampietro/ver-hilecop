(** * Facts about Elaboration of Transition Design *)

Require Import common.CoqLib.
Require Import common.NatMapTactics.

Require Import hvhdl.HVhdlCoreLib.
Require Import hvhdl.HVhdlHilecopLib.
Require Import hvhdl.HVhdlElaborationLib.
Require Import hvhdl.HVhdlElaborationFactsLib.

(** ** Transition Generic Constant Elaboration *)

Lemma elab_T_Δ_in_arcs_nb_1 :
  forall {d Δ σ__e id__t gm ipm opm Δ__t},
    edesign hdstore (NatMap.empty value) d Δ σ__e ->
    InCs (cs_comp id__t Petri.transition_entid gm ipm opm) (behavior d) ->
    MapsTo id__t (Component Δ__t) Δ ->
    exists t n, MapsTo input_arcs_number (Generic t (Vnat n)) Δ__t.
Admitted.

Lemma elab_T_Δ_in_arcs_nb_2 :
  forall {d Δ σ__e id__t gm ipm opm Δ__t e v},
    edesign hdstore (NatMap.empty value) d Δ σ__e ->
    InCs (cs_comp id__t Petri.transition_entid gm ipm opm) (behavior d) ->
    MapsTo id__t (Component Δ__t) Δ ->
    List.In (assocg_ input_arcs_number e) gm ->
    vexpr EmptyElDesign EmptyDState EmptyLEnv false e v ->
    exists t, MapsTo input_arcs_number (Generic t v) Δ__t.
Admitted.

(** ** Transition Input Port Elaboration *)

Lemma elab_T_σ_rt : 
  forall {d Δ σ__e id__t gm ipm opm σ__te},
    edesign hdstore (NatMap.empty value) d Δ σ__e ->
    InCs (cs_comp id__t Petri.transition_entid gm ipm opm) (behavior d) ->
    MapsTo id__t σ__te (compstore σ__e) ->
    exists aofv, MapsTo Transition.reinit_time (Varr aofv) (sigstore σ__te).
Proof.
Admitted.

Lemma elab_T_σ_rt_2 : 
  forall {d Δ σ__e id__t gm ipm opm σ__te Δ__t t n},
    edesign hdstore (NatMap.empty value) d Δ σ__e ->
    InCs (cs_comp id__t Petri.transition_entid gm ipm opm) (behavior d) ->
    MapsTo id__t σ__te (compstore σ__e) ->
    MapsTo id__t (Component Δ__t) Δ ->
    MapsTo Transition.input_arcs_number (Generic t (Vnat n)) Δ__t ->
    MapsTo Transition.reinit_time (Varr (create_arr (S ((n - 1) - 0)) (Vbool false) (gt_Sn_O ((n - 1) - 0)))) (sigstore σ__te).
Proof.
  
Admitted.

(** ** Transition Declared Signal Elaboration *)

Lemma elab_T_Δ_s_tc :
  forall {d Δ σ__e id__t gm ipm opm Δ__t},
    edesign hdstore (NatMap.empty value) d Δ σ__e ->
    InCs (cs_comp id__t Petri.transition_entid gm ipm opm) (behavior d) ->
    MapsTo id__t (Component Δ__t) Δ ->
    DeclaredOf Δ__t s_time_counter.
Proof.
  inversion 1; subst; intros; eapply @elab_decl_of_comp with (d__e := transition_design); eauto.
  apply NatMap.add_1; reflexivity.
  firstorder.
Qed.

Lemma elab_T_Δ_s_rtc :
  forall {d Δ σ__e id__t gm ipm opm Δ__t},
    edesign hdstore (NatMap.empty value) d Δ σ__e ->
    InCs (cs_comp id__t Petri.transition_entid gm ipm opm) (behavior d) ->
    MapsTo id__t (Component Δ__t) Δ ->
    DeclaredOf Δ__t s_reinit_time_counter.
Proof.
  inversion 1; subst; intros; eapply @elab_decl_of_comp with (d__e := transition_design); eauto.
  apply NatMap.add_1; reflexivity.
  firstorder.
Qed.
  


