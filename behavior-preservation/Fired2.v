(** * Falling Edge Lemma *)

Require Import common.NatMap.
Require Import common.CoqLib.
Require Import common.ListLib.

Require Import sitpn.SitpnLib.

Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.Stabilize.
Require Import hvhdl.SynchronousEvaluation.
Require Import hvhdl.Environment.
Require Import hvhdl.DesignElaboration.
Require Import hvhdl.HilecopDesignStore.

Require Import transformation.Sitpn2HVhdl.

Require Import soundness.SemanticPreservationDefs.

(** ** Operational Implementation of the Fired set. *)

(** Builds the list of fired transitions from the list [lofT], the
    list of already elected fired transitions [fired], and the
    residual marking [m]. *)

Inductive IsFiredListAux {sitpn} (s : SitpnState sitpn)  :
  list (T sitpn) -> list (T sitpn) -> list (T sitpn) -> Prop :=
| IsFiredListAux_nil :
      forall F, IsFiredListAux s [] F F 
| IsFiredListAux_fired :
    forall t msub T__s F F',
      Firable s t ->
      MarkingSubPreSum (fun t' => t' >~ t /\ InA Teq t' F) (M s) msub ->
      Sens msub t ->      
      IsFiredListAux s T__s (F ++ [t]) F' ->
      IsFiredListAux s (t :: T__s) F F'
| IsFiredListAux_not_fired :
    forall t msub T__s F F',
      (~Firable s t \/ (MarkingSubPreSum (fun t' => t' >~ t /\ InA Teq t' F) (M s) msub /\ ~Sens msub t)) ->      
      IsFiredListAux s T__s F F' ->
      IsFiredListAux s (t :: T__s) F F'.

(** Wrapper around the IsFiredListAux predicate.  

    Adds that [Tlist] must implement the set (T sitpn).
 *)

Inductive IsFiredList {sitpn} (s : SitpnState sitpn) (F : list (T sitpn)) : Prop :=
  IsFiredList_ :
    forall Tlist,
      Set_in_ListA Teq (fun t => True) Tlist ->
      IsFiredListAux s Tlist [] F ->
      IsFiredList s F.

(** Final definition of the set of [fired] transitions at state [s]
    and the fact that a transition [t] belongs to the set. *)

Definition Fired {sitpn} (s : SitpnState sitpn) (F : list (T sitpn)) (t : T sitpn) : Prop :=
  IsFiredList s F /\ List.In t F.

Lemma fe_equal_fired_aux :
  forall sitpn id__ent id__arch mm d ?? E__c E__p ?? ??__e s ?? ?? s' ??__i ??__f ??',

    (* sitpn translates into (d, ??). *)
    sitpn2hvhdl sitpn id__ent id__arch mm = (inl (d, ??)) ->

    (* Environments are similar. *)
    SimEnv sitpn ?? E__c E__p ->
    
    (* [??, ??__e] are the results of the elaboration of [d]. *)
    EDesign hdstore (empty value) d ?? ??__e ->

    (* States s and ?? are similar (post rising edge). *)
    SimStateAfterRE sitpn ?? s ?? ->

    (* From s to s' after ???. *)
    SitpnStateTransition E__c ?? s s' fe ->

    (* From ?? to ??' after ???. *)
    IsInjectedDState ?? (E__p ??) ??__i ->
    vfalling hdstore ?? ??__i (behavior d) ??__f ->
    Stabilize hdstore ?? ??__f (behavior d) ??' ->

    forall T__s F Flist,
      IsFiredListAux s' T__s F Flist ->
      (* Extra. Hypothesis. *)
      (forall t' id__t' ??'__t',
          InA Tkeq (t', id__t') (t2tdi ??) ->
          MapsTo id__t' ??'__t' (cstore ??') ->
          (InA Teq t' F -> MapsTo Transition.fired (Vbool true) (sstore ??'__t'))
          /\ (MapsTo Transition.fired (Vbool true) (sstore ??'__t') -> InA Teq t' F \/ InA Teq t' T__s)) ->
      forall t id__t ??'__t,
        InA Tkeq (t, id__t) (t2tdi ??) ->
        MapsTo id__t ??'__t (cstore ??') ->
        InA Teq t Flist <-> MapsTo Transition.fired (Vbool true) (sstore ??'__t).
Proof.
  intros until T__s; induction 1.

  (* BASE CASE *)
  - intros EH; intros.
    edestruct EH as (Fired_true, True_fired); eauto.
    split; try assumption.
    intros; edestruct True_fired; eauto.
    inversion H10.
    
  (* INDUCTION CASE (transition is fired) *)
  - intros EH. apply IHIsFiredListAux.
    intros t id__t ??'__t; do 2 intro; split.
    (* CASE [t ??? (F ??? {t0}) ??? ??'(id__t)("f") = true] *)
    + intros InA_app0.
      (* CASE [t ??? F] *)
      edestruct (InA_app InA_app0) as [InA_F | eq_t0].
      eapply EH; eauto.
      (* CASE [t = t0] *)
      inversion_clear eq_t0; [ admit | admit].
      
    (* CASE [??'(id__t)("f") = true ??? t ??? (F ??? {t0}) \/ t ??? T__s] *)
    + intros fired_true.
      edestruct (EH t id__t ??'__t); eauto.
      edestruct H14; eauto.
      left. erewrite InA_app_iff. eauto.
      inversion_clear H15.
      left. erewrite InA_app_iff. eauto.
      right; eauto.

  (* INDUCTION CASE (transition is not fired) *)
  - admit.
      
Admitted.

Lemma fe_equal_fired :
  forall sitpn id__ent id__arch mm d ?? E__c E__p ?? ??__e s ?? ?? s' ??__i ??__f ??',

    (* sitpn translates into (d, ??). *)
    sitpn2hvhdl sitpn id__ent id__arch mm = (inl (d, ??)) ->

    (* Environments are similar. *)
    SimEnv sitpn ?? E__c E__p ->
    
    (* [??, ??__e] are the results of the elaboration of [d]. *)
    EDesign hdstore (empty value) d ?? ??__e ->

    (* States s and ?? are similar (post rising edge). *)
    SimStateAfterRE sitpn ?? s ?? ->

    (* From s to s' after ???. *)
    SitpnStateTransition E__c ?? s s' fe ->

    (* From ?? to ??' after ???. *)
    IsInjectedDState ?? (E__p ??) ??__i ->
    vfalling hdstore ?? ??__i (behavior d) ??__f ->
    Stabilize hdstore ?? ??__f (behavior d) ??' ->

    forall t id__t ??'__t,
      InA Tkeq (t, id__t) (t2tdi ??) ->
      MapsTo id__t ??'__t (cstore ??') ->
      forall Flist,
        IsFiredList s' Flist ->
        InA Teq t Flist <-> MapsTo Transition.fired (Vbool true) (sstore ??'__t).
Proof.
  intros until Flist; inversion 1.
  eapply fe_equal_fired_aux; eauto.

  intros; split.

  - inversion 1.
  - right. destruct H10 as (InA_Tlist, NoDup_Tlist).
    rewrite <- (InA_Tlist t'); exact Logic.I.
Qed.



