(** * Facts about Port Map Evaluation *)

Require Import common.NatMap.
Require Import common.Coqlib.
Require Import common.NatSet.
Require Import common.InAndNoDup.

Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.Environment.
Require Import hvhdl.PortMapEvaluation.
Require Import hvhdl.HVhdlTypes.
Require Import hvhdl.ExpressionEvaluation.
Require Import hvhdl.ValidPortMap.

(** ** Facts about Input Port Map Evaluation *)

Section IPMap.

  Lemma vassocip_inv_sigstore :
    forall {Δ Δ__c σ σ__c asip σ__c' id v},
      vassocip Δ Δ__c σ σ__c asip σ__c' -> 
      ~InputOf Δ__c id ->
      MapsTo id v (sigstore σ__c) ->
      MapsTo id v (sigstore σ__c').
  Proof.
    inversion 1; subst; simpl; auto; intros.
    all :
      destruct (Nat.eq_dec id id0) as [e1 | ne1]; try subst;
      [ elimtype False;
        match goal with
        | [ H: ~InputOf _ _, H': MapsTo _ (Input ?t) _ |- _ ] =>
          apply H; exists t; assumption
        end
      | eapply NatMap.add_2; eauto ].
  Qed.

  Lemma vassocip_not_in_events_if_not_input :
    forall {Δ Δ__c σ σ__c asip σ__c' id},
      vassocip Δ Δ__c σ σ__c asip σ__c' ->
      ~InputOf Δ__c id ->
      ~NatSet.In id (events σ__c) ->
      ~NatSet.In id (events σ__c').
  Proof.
    inversion_clear 1; auto; simpl; subst; intros;
      rewrite add_spec; inversion 1;
        (auto ||
         match goal with
         | [ H: MapsTo _ (Input ?t) _, H': ~InputOf _ _ |- _ ] =>
           subst; apply H'; exists t; auto
         end).
  Qed.
  
  Lemma mapip_inv_sigstore :
    forall {Δ Δ__c σ σ__c ipm σ__c' id v},
      mapip Δ Δ__c σ σ__c ipm σ__c' ->
      ~InputOf Δ__c id ->
      MapsTo id v (sigstore σ__c) ->
      MapsTo id v (sigstore σ__c').
  Proof.
    induction 1; intros; auto.
    apply IHmapip; auto.
    eapply vassocip_inv_sigstore; eauto.
  Qed.
  
  Lemma mapip_not_in_events_if_not_input :
    forall {Δ Δ__c : ElDesign} {σ σ__c : DState} {ipm : list associp} {σ__c' : DState} {id : key},
      mapip Δ Δ__c σ σ__c ipm σ__c' ->
      ~InputOf Δ__c id ->
      ~NatSet.In id (events σ__c) ->
      ~NatSet.In id (events σ__c').
  Proof.
    induction 1; auto.
    intros; apply IHmapip; auto.
    eapply vassocip_not_in_events_if_not_input; eauto.
  Qed.

  Lemma vassocip_eval_simpl_associp :
    forall {Δ Δ__c σ σ__c σ__c'} {id : ident} {e},
      vassocip Δ Δ__c σ σ__c (associp_ id e) σ__c' ->
      exists v, vexpr Δ σ EmptyLEnv false e v /\
                MapsTo id v (sigstore σ__c').
  Admitted.

  Lemma listipm_unique_simpl_associp :
    forall {Δ Δ__c σ ipm} {id__i : ident} {formals formals'},
      listipm Δ Δ__c σ formals ipm formals' ->
      List.In (id__i, None) formals ->
      (~(exists e, List.In (associp_ id__i e) ipm) /\
       ~(exists e e__i, List.In (associp_ (n_xid id__i e__i) e) ipm)).
  Admitted.

  Lemma mapip_inv_if_not_assoc :
    forall {Δ Δ__c σ σ__c ipm σ__c'} {id__i : ident} {v},
      mapip Δ Δ__c σ σ__c ipm σ__c' ->
      ~(exists e, List.In (associp_ id__i e) ipm) ->
      ~(exists e e__i, List.In (associp_ (n_xid id__i e__i) e) ipm) ->
      MapsTo id__i v (sigstore σ__c) ->
      MapsTo id__i v (sigstore σ__c').
  Admitted.
  
  Lemma mapip_eval_simpl_associp :
    forall {Δ Δ__c σ σ__c ipm σ__c'} ,
      mapip Δ Δ__c σ σ__c ipm σ__c' ->
      forall {id__i : ident} {e formals formals'},
        List.In (associp_ id__i e) ipm ->
        listipm Δ Δ__c σ formals ipm formals' ->
        exists v, vexpr Δ σ EmptyLEnv false e v /\
                  MapsTo id__i v (sigstore σ__c').
  Proof.
    induction 1; try (solve [inversion 1]).
    inversion 1; subst; auto.
    edestruct @vassocip_eval_simpl_associp with (Δ := Δ)
      as (v, (vexpr_v, MapsTo_v));
      eauto.
    exists v; split; auto.
    inversion H2; subst. inversion H5; subst.
    eapply mapip_inv_if_not_assoc; eauto.
    eapply proj1; eapply listipm_unique_simpl_associp; eauto.
    apply in_last.
    eapply proj2; eapply listipm_unique_simpl_associp; eauto.
    apply in_last.
    inversion 1; subst.
    intros; eapply IHmapip; eauto.
  Qed.

  Lemma mapip_eq_state_if_no_events :
    forall {Δ Δ__c σ σ__c ipm σ__c'},
      mapip Δ Δ__c σ σ__c ipm σ__c' ->
      Equal (events σ__c') {[]} ->
      σ__c = σ__c'.
  Admitted.
  
End IPMap.

(** ** Facts about Output Port Map Evaluation *)

Section OPMap.

  Lemma mapop_inv_compstore :
    forall {Δ Δ__c σ σ__c1 ipmap σ' id__c σ__c2},
      mapop Δ Δ__c σ σ__c1 ipmap σ' ->
      MapsTo id__c σ__c2 (compstore σ) ->
      MapsTo id__c σ__c2 (compstore σ').
  Proof.
    induction 1; try subst; auto.
    induction H; try subst; auto.
  Qed.

  Lemma mapop_not_in_events_if_not_assigned :
    forall {Δ Δ__c σ σ__c opmap σ' id},
      mapop Δ Δ__c σ σ__c opmap σ' ->
      ~NatSet.In id (events σ) ->
      ~AssignedInOPM id opmap ->
      ~NatSet.In id (events σ').
  Proof.
    induction 1; subst; auto.
    inversion H; subst; simpl; auto.
    all : simpl in IHmapop; intros; apply IHmapop;
      auto; rewrite add_spec; firstorder.
  Qed.

  Lemma vassocop_not_in_events_if_not_sig :
    forall {Δ Δ__c σ σ__c asop σ' id},
      vassocop Δ Δ__c σ σ__c asop σ' ->
      ~OutputOf Δ id ->
      ~DeclaredOf Δ id ->
      ~NatSet.In id (events σ) ->
      ~NatSet.In id (events σ').
  Proof.
    inversion_clear 1; subst; simpl; auto; intros;
    rewrite add_spec; inversion 1;
      (solve [contradiction] ||
       match goal with
       | [ Hor: MapsTo _ _ _ \/ _ |- _ ] =>
         inversion Hor;
         [ match goal with
           | [ H: MapsTo _ (Declared ?t) _, Hdecl: ~DeclaredOf _ _  |- _ ] =>
             subst; apply Hdecl; exists t; auto
           end
         | match goal with
           | [ H: MapsTo _ (Output ?t) _, Hout: ~OutputOf _ _  |- _ ] =>
             subst; apply Hout; exists t; auto
           end
         ]
       end).
  Qed.
  
  Lemma mapop_not_in_events_if_not_sig :
    forall {Δ Δ__c σ σ__c opmap σ' id},
      mapop Δ Δ__c σ σ__c opmap σ' ->
      ~NatSet.In id (events σ) ->
      ~OutputOf Δ id ->
      ~DeclaredOf Δ id ->
      ~NatSet.In id (events σ').
  Proof.
    induction 1; auto.
    intros; apply IHmapop; auto.
    eapply vassocop_not_in_events_if_not_sig; eauto.
  Qed.
  
End OPMap.
