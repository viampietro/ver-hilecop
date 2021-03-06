(** * Facts about Port Map Evaluation *)

Require Import common.NatSet.
Require Import common.NatMap.
Require Import common.proofs.NatMapTactics.
Require Import common.CoqLib.
Require Import common.NatSet.
Require Import common.InAndNoDup.

Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.Environment.
Require Import hvhdl.PortMapEvaluation.
Require Import hvhdl.HVhdlTypes.
Require Import hvhdl.ExpressionEvaluation.
Require Import hvhdl.ValidPortMap.
Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.proofs.SemanticalDomainsFacts.

Require Import hvhdl.proofs.EnvironmentFacts.
Require Import hvhdl.proofs.ValidPortMapFacts.

(** ** Facts about Input Port Map Evaluation *)

Section IPMap.

  Lemma VIPAssoc_inv_sstore :
    forall {Δ Δ__c σ σ__c asip σ__c' id v},
      VIPAssoc Δ Δ__c σ σ__c asip σ__c' -> 
      ~InputOf Δ__c id ->
      MapsTo id v (sstore σ__c) ->
      MapsTo id v (sstore σ__c').
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

  Lemma VIPAssoc_not_in_events_if_not_input :
    forall {Δ Δ__c σ σ__c asip σ__c' id},
      VIPAssoc Δ Δ__c σ σ__c asip σ__c' ->
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
  
  Lemma VIPAssoc_eval_simpl_associp :
    forall {Δ Δ__c σ σ__c σ__c'} {id : ident} {e},
      VIPAssoc Δ Δ__c σ σ__c (associp_ id e) σ__c' ->
      exists v, VExpr Δ σ EmptyLEnv false e v /\
                MapsTo id v (sstore σ__c').
  Proof. inversion 1.
         subst; simpl; exists v; auto with mapsto.
  Qed.

  Lemma VIPAssoc_inv_if_not_assoc :
    forall {Δ Δ__c σ σ__c asip σ__c'},
      VIPAssoc Δ Δ__c σ σ__c asip σ__c' ->
      forall {id__i : ident} {v},
        ~(exists e, (associp_ id__i e) = asip) ->
        ~(exists e e__i, (associp_ (n_xid id__i e__i) e) = asip) ->
        MapsTo id__i v (sstore σ__c) ->
        MapsTo id__i v (sstore σ__c').
  Proof.
    inversion 1; subst; simpl; auto.
    all : intros id__i v' nex_1 nex_2; intros.
    destruct (Nat.eq_dec id__i id) as [eq1 | neq1].
    subst; elimtype False; apply nex_1; exists e; reflexivity.
    eauto with mapsto.
    destruct (Nat.eq_dec id__i id) as [eq1 | neq1].
    subst; elimtype False; apply nex_2; exists e, ei; reflexivity.
    eauto with mapsto.
  Qed.
  
  Lemma VIPAssoc_no_events :
    forall {Δ Δ__c σ σ__c asip σ__c'},
      VIPAssoc Δ Δ__c σ σ__c asip σ__c' ->
      Equal (events σ__c') {[]} ->
      Equal (events σ__c) {[]}.
  Proof.
    inversion 1; subst; simpl; auto;
    intros; exfalso; eapply add_empty_false; eauto.
  Qed.
  
  (* Lemma VIPAssoc_eq_state_if_no_events : *)
  (*   forall {Δ Δ__c σ σ__c asip σ__c'}, *)
  (*     VIPAssoc Δ Δ__c σ σ__c asip σ__c' -> *)
  (*     Equal (events σ__c') {[]} -> *)
  (*     σ__c = σ__c'. *)
  (* Proof. *)
  (*   inversion 1; auto; subst; simpl. *)
  (*     intros; exfalso; eapply add_empty_false; eauto. *)
  (* Qed. *)

  Lemma VIPAssoc_maps_sstore :
    forall {Δ Δ__c σ σ__c asip σ__c' id v},
      VIPAssoc Δ Δ__c σ σ__c asip σ__c' -> 
      MapsTo id v (sstore σ__c) ->
      exists v', MapsTo id v' (sstore σ__c').
  Proof.
    inversion_clear 1; subst; cbn;
      destruct (Nat.eq_dec id id0) as [eq_ | neq_ ].
    subst; exists v0; eauto with mapsto.
    exists v; eauto with mapsto.
    subst; exists (Varr (set_at v0 idx aofv idx_in_bounds)); eauto with mapsto.
    exists v; eauto with mapsto.
  Qed.

  Lemma VIPAssoc_inv_well_typed_values_in_sstore :
    forall {Δ Δ__c σ σ__c asip σ'__c},
      VIPAssoc Δ Δ__c σ σ__c asip σ'__c ->
      (forall {id t v},
          (MapsTo id (Internal t) Δ__c \/ MapsTo id (Input t) Δ__c \/ MapsTo id (Output t) Δ__c) ->
          MapsTo id v (sstore σ__c) ->
          IsOfType v t) ->
      forall {id t v},
        (MapsTo id (Internal t) Δ__c \/ MapsTo id (Input t) Δ__c \/ MapsTo id (Output t) Δ__c) ->
        MapsTo id v (sstore σ'__c) ->
        IsOfType v t.
  Proof.
    induction 1; try (solve [eauto]).
    (* CASE [id ⇒ e] and [id(i) ⇒ e]*)
    all:
      intros WT; intros *; intros MapsTo_Δ; cbn;
      destruct (Nat.eq_dec id0 id) as [eq_ | neq_ ];
        [ (* CASE [id0 = id] *)
          rewrite eq_ in *; intros MapsTo_sstore;
          match goal with
          | _: MapsTo ?k (_ ?t1) ?m,
               _: MapsTo ?k (_ ?t2) ?m \/ MapsTo ?k (_ ?t2) ?m \/ MapsTo ?k (_ ?t2) ?m,
                  _: MapsTo ?k ?v3 (NatMap.add _ ?v4 _)
            |- _ =>
            assert (eq_t : t1 = t2) by (solve_mapsto_fun);
            erewrite @MapsTo_add_eqv with (e := v3) (e' := v4); eauto; rewrite <- eq_t;
            (assumption || (eapply IsOfType_inv_set_at; eauto; rewrite eq_t; eapply WT; eauto))
          end

        | (* CASE [id0 ≠ id] *)
        intro; eapply WT; eauto with mapsto ].
  Qed.
  
  Lemma MIP_inv_sstore :
    forall {Δ Δ__c σ σ__c ipm σ__c' id v},
      MIP Δ Δ__c σ σ__c ipm σ__c' ->
      ~InputOf Δ__c id ->
      MapsTo id v (sstore σ__c) ->
      MapsTo id v (sstore σ__c').
  Proof.
    induction 1; intros; auto.
    apply IHMIP; auto.
    eapply VIPAssoc_inv_sstore; eauto.
  Qed.

  Lemma MIP_inv_cstore :
    forall {Δ Δ__c σ σ__c ipm σ__c' id σ__c0},
      MIP Δ Δ__c σ σ__c ipm σ__c' ->
      MapsTo id σ__c0 (cstore σ__c) ->
      MapsTo id σ__c0 (cstore σ__c').
  Proof.
    induction 1; try subst; auto.
    induction H; try subst; auto.
  Qed.

  Lemma MIP_inv_cstore_2 :
    forall {Δ Δ__c σ σ__c ipm σ__c' id σ__c0},
      MIP Δ Δ__c σ σ__c ipm σ__c' ->
      MapsTo id σ__c0 (cstore σ__c') ->
      MapsTo id σ__c0 (cstore σ__c).
  Proof.
    induction 1; try subst; auto.
    induction H; try subst; auto.
  Qed.
  
  Lemma MIP_not_in_events_if_not_input :
    forall {Δ Δ__c : ElDesign} {σ σ__c : DState} {ipm : list associp} {σ__c' : DState} {id : key},
      MIP Δ Δ__c σ σ__c ipm σ__c' ->
      ~InputOf Δ__c id ->
      ~NatSet.In id (events σ__c) ->
      ~NatSet.In id (events σ__c').
  Proof.
    induction 1; auto.
    intros; apply IHMIP; auto.
    eapply VIPAssoc_not_in_events_if_not_input; eauto.
  Qed.
  
  Lemma MIP_inv_if_not_assoc :
    forall {Δ Δ__c σ σ__c ipm σ__c'},
      MIP Δ Δ__c σ σ__c ipm σ__c' ->
      forall {id__i : ident} {v},
      ~(exists e, List.In (associp_ id__i e) ipm) ->
      ~(exists e e__i, List.In (associp_ (n_xid id__i e__i) e) ipm) ->
      MapsTo id__i v (sstore σ__c) ->
      MapsTo id__i v (sstore σ__c').
  Proof.
    induction 1; auto.
    intros id__i v nex_1 nex_2; intros.
    apply IHMIP.
    destruct 1 as (e, In_lofasips).
    apply nex_1; exists e; auto.
    destruct 1 as (e, (e__i, In_lofasips)).
    apply nex_2; exists e, e__i; auto.
    eapply VIPAssoc_inv_if_not_assoc; eauto.
    destruct 1 as (e, e1).
    apply nex_1; exists e; rewrite e1; auto with datatypes.
    destruct 1 as (e, (e__i, e1)).
    apply nex_2; exists e, e__i; rewrite e1; auto with datatypes.
  Qed.  
  
  Lemma MIP_eval_simpl_associp :
    forall {Δ Δ__c σ σ__c ipm σ__c'} ,
      MIP Δ Δ__c σ σ__c ipm σ__c' ->
      forall {id__i : ident} {e formals formals'},
        List.In (associp_ id__i e) ipm ->
        ListIPM Δ Δ__c σ formals ipm formals' ->
        exists v, VExpr Δ σ EmptyLEnv false e v /\
                  MapsTo id__i v (sstore σ__c').
  Proof.
    induction 1; try (solve [inversion 1]).
    inversion 1; subst; auto.
    edestruct @VIPAssoc_eval_simpl_associp with (Δ := Δ)
      as (v, (vexpr_v, MapsTo_v));
      eauto.
    exists v; split; auto.
    inversion H2; subst. inversion H5; subst.
    eapply MIP_inv_if_not_assoc; eauto.
    eapply proj1; eapply ListIPM_unique_simpl_associp; eauto.
    eapply proj2; eapply ListIPM_unique_simpl_associp; eauto.
    inversion 1; subst.
    intros; eapply IHMIP; eauto.
  Qed.
  
  Lemma MIP_no_events :
    forall {Δ Δ__c σ σ__c ipm σ__c'},
      MIP Δ Δ__c σ σ__c ipm σ__c' ->
      Equal (events σ__c') {[]} ->
      Equal (events σ__c) {[]}.
  Proof.
    induction 1; auto.
    intros; eapply VIPAssoc_no_events; eauto.
  Qed.
  
  (* Lemma MIP_eq_state_if_no_events : *)
  (*   forall {Δ Δ__c σ σ__c ipm σ__c'}, *)
  (*     MIP Δ Δ__c σ σ__c ipm σ__c' -> *)
  (*     Equal (events σ__c') {[]} -> *)
  (*     σ__c = σ__c'. *)
  (* Proof. *)
  (*   induction 1; auto. *)
  (*   intros Equal_emp. *)
  (*   transitivity σ__c'; auto. *)
  (*   eapply VIPAssoc_eq_state_if_no_events; eauto. *)
  (*   eapply MIP_no_events; eauto. *)
  (* Qed. *)

  Lemma MIP_maps_sstore :
    forall {Δ Δ__c σ σ__c ipm σ__c' },
      MIP Δ Δ__c σ σ__c ipm σ__c' ->
      forall {id v},
        MapsTo id v (sstore σ__c) ->
        exists v', MapsTo id v' (sstore σ__c').
  Proof.
    induction 1; intros; auto.
    exists v; assumption.
    edestruct @VIPAssoc_maps_sstore with (Δ := Δ); eauto.
  Qed.

  Lemma MIP_inv_well_typed_values_in_sstore :
    forall {Δ Δ__c σ σ__c ipm σ__c'},
      MIP Δ Δ__c σ σ__c ipm σ__c' ->
      (forall {id t v},
          (MapsTo id (Internal t) Δ__c \/ MapsTo id (Input t) Δ__c \/ MapsTo id (Output t) Δ__c) ->
          MapsTo id v (sstore σ__c) ->
          IsOfType v t) ->
      forall {id t v},
        (MapsTo id (Internal t) Δ__c \/ MapsTo id (Input t) Δ__c \/ MapsTo id (Output t) Δ__c) ->
        MapsTo id v (sstore σ__c') ->
        IsOfType v t.
  Proof.
    induction 1; try (solve [trivial]).
    intros WT; eapply IHMIP.
    eapply VIPAssoc_inv_well_typed_values_in_sstore; eauto.
  Qed.
  
End IPMap.

(** ** Facts about Output Port Map Evaluation *)

Section OPMap.

  Lemma VOPAssoc_maps_sstore :
    forall {Δ Δ__c σ σ__c asop σ'},
      VOPAssoc Δ Δ__c σ σ__c asop σ' ->
      forall {id v},
        MapsTo id v (sstore σ) ->
        exists v', MapsTo id v' (sstore σ').
  Proof.
    induction 1; try (solve [intros; exists v; auto]).
    all : subst σ'; subst sstore'; cbn;
      intros id v MapsTo_; destruct (Nat.eq_dec id id__a); 
        [ subst id; eauto with mapsto
        | exists v; eauto with mapsto ].
  Qed.
  
  Lemma VOPAssoc_eq_state_if_no_events :
    forall {Δ Δ__c σ σ__c asop σ'},
      VOPAssoc Δ Δ__c σ σ__c asop σ' ->
      Equal (events σ') {[]} ->
      σ = σ'.
  Proof.
    induction 1; try reflexivity; subst; simpl;
      intros; contrad_add_empty.
  Qed.
  
  Lemma VOPAssoc_not_in_events_if_not_sig :
    forall {Δ Δ__c σ σ__c asop σ' id},
      VOPAssoc Δ Δ__c σ σ__c asop σ' ->
      ~OutputOf Δ id ->
      ~InternalOf Δ id ->
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
             | [ H: MapsTo _ (Internal ?t) _, Hdecl: ~InternalOf _ _  |- _ ] =>
               subst; apply Hdecl; exists t; auto
             end
           | match goal with
             | [ H: MapsTo _ (Output ?t) _, Hout: ~OutputOf _ _  |- _ ] =>
               subst; apply Hout; exists t; auto
             end
           ]
         end).
  Qed.

  Lemma VOPAssoc_inv_in_events :
    forall {Δ Δ__c σ σ__c asop σ' id},
      VOPAssoc Δ Δ__c σ σ__c asop σ' ->
      NatSet.In id (events σ) ->
      NatSet.In id (events σ').
  Proof.
    induction 1; auto;
      subst σ'; subst events'; cbn; eauto with set.
  Qed.

  Lemma VOPAssoc_inv_well_typed_values_in_sstore :
    forall {Δ Δ__c σ σ__c asop σ'},
      VOPAssoc Δ Δ__c σ σ__c asop σ' ->
      (forall {id t v},
          (MapsTo id (Internal t) Δ \/ MapsTo id (Input t) Δ \/ MapsTo id (Output t) Δ) ->
          MapsTo id v (sstore σ) ->
          IsOfType v t) ->
      forall {id t v},
        (MapsTo id (Internal t) Δ \/ MapsTo id (Input t) Δ \/ MapsTo id (Output t) Δ) ->
        MapsTo id v (sstore σ') ->
        IsOfType v t.
  Proof.
    induction 1; try (solve [eauto]).
    (* CASE [id__f ⇒ id__a] and [id__f(j) ⇒ id__a] *)
    1,4 :
      intros WT; intros *; intros MapsTo_Δ;
      subst σ'; subst sstore'; cbn;
        destruct (Nat.eq_dec id__a id) as [eq_ | neq_ ];
        [(* CASE [id__a = id] *)
          rewrite eq_ in *;
          assert (eq_t : t0 = t1) by (solve_mapsto_fun); intros MapsTo_sstore;
          erewrite @MapsTo_add_eqv with (e := v) (e' := newv); eauto;
          rewrite <- eq_t; assumption
        | (* CASE [id__a ≠ id] *)
        intro; eapply WT; eauto with mapsto ].
    
    (* CASE [id__f ⇒ id__a(i)] and [id__f(j) ⇒ id__a(i)] *)
    all:
      intros WT; intros *; intros MapsTo_Δ;
      subst σ'; subst sstore'; subst aofv'; cbn;
        destruct (Nat.eq_dec id__a id) as [eq_ | neq_ ];
        [(* CASE [id__a = id] *)
          rewrite eq_ in *;
          assert (eq_t : (Tarray t0 l u) = t1) by (solve_mapsto_fun);
          intros MapsTo_sstore;
          erewrite @MapsTo_add_eqv
            with (e := v) (e' := (Varr (set_at newv idx aofv idx_in_bounds))); eauto;
          rewrite <- eq_t;
          eapply IsOfType_inv_set_at; eauto;
          rewrite eq_t; eapply WT; eauto
        | (* CASE [id__a ≠ id] *)
        intro; eapply WT; eauto with mapsto ].
  Qed.
  
  Lemma MOP_inv_in_events :
    forall {Δ Δ__c σ σ__c opmap σ' id},
      MOP Δ Δ__c σ σ__c opmap σ' ->
      NatSet.In id (events σ) ->
      NatSet.In id (events σ').
  Proof.
    induction 1; auto; intros.
    eapply IHMOP; eapply VOPAssoc_inv_in_events; eauto.
  Qed.
  
  Lemma MOP_inv_cstore :
    forall {Δ Δ__c σ σ__c1 opmap σ' id__c σ__c2},
      MOP Δ Δ__c σ σ__c1 opmap σ' ->
      MapsTo id__c σ__c2 (cstore σ) ->
      MapsTo id__c σ__c2 (cstore σ').
  Proof.
    induction 1; try subst; auto.
    induction H; try subst; auto.
  Qed.

  Lemma MOP_inv_cstore_2 :
    forall {Δ Δ__c σ σ__c1 opmap σ' id__c σ__c2},
      MOP Δ Δ__c σ σ__c1 opmap σ' ->
      MapsTo id__c σ__c2 (cstore σ') ->
      MapsTo id__c σ__c2 (cstore σ).
  Proof.
    induction 1; try subst; auto.
    induction H; try subst; auto.
  Qed.
  
  Lemma MOP_maps_sstore :
    forall {Δ Δ__c σ σ__c opmap σ'},
      MOP Δ Δ__c σ σ__c opmap σ' ->
      forall {id v},
        MapsTo id v (sstore σ) ->
        exists v', MapsTo id v' (sstore σ').
  Proof.
    induction 1.
    intros; exists v; assumption.
    intros; edestruct @VOPAssoc_maps_sstore with (Δ := Δ); eauto.
  Qed.
  
  Lemma MOP_not_in_events_if_not_assigned :
    forall {Δ Δ__c σ σ__c opmap σ' id},
      MOP Δ Δ__c σ σ__c opmap σ' ->
      ~NatSet.In id (events σ) ->
      ~AssignedInOPM id opmap ->
      ~NatSet.In id (events σ').
  Proof.
    induction 1; subst; auto.
    inversion H; subst; simpl; auto.
    all : simpl in IHMOP; intros; apply IHMOP;
      auto; rewrite add_spec; firstorder.
  Qed.
  
  Lemma MOP_not_in_events_if_not_sig :
    forall {Δ Δ__c σ σ__c opmap σ' id},
      MOP Δ Δ__c σ σ__c opmap σ' ->
      ~NatSet.In id (events σ) ->
      ~OutputOf Δ id ->
      ~InternalOf Δ id ->
      ~NatSet.In id (events σ').
  Proof.
    induction 1; auto.
    intros; apply IHMOP; auto.
    eapply VOPAssoc_not_in_events_if_not_sig; eauto.
  Qed.
    
  Lemma MOP_eq_state_if_no_events :
    forall {Δ Δ__c σ σ__c opmap σ'},
      MOP Δ Δ__c σ σ__c opmap σ' ->
      Equal (events σ') {[]} ->
      σ = σ'.
  Proof.
    induction 1; auto.
    transitivity σ'; auto.
    eapply VOPAssoc_eq_state_if_no_events; eauto.
    rewrite IHMOP; auto.
  Qed.
  
  Lemma MOP_inv_well_typed_values_in_sstore :
    forall {Δ Δ__c σ σ__c opmap σ'},
      MOP Δ Δ__c σ σ__c opmap σ' ->
      (forall {id t v},
          (MapsTo id (Internal t) Δ \/ MapsTo id (Input t) Δ \/ MapsTo id (Output t) Δ) ->
          MapsTo id v (sstore σ) ->
          IsOfType v t) ->
      forall {id t v},
        (MapsTo id (Internal t) Δ \/ MapsTo id (Input t) Δ \/ MapsTo id (Output t) Δ) ->
        MapsTo id v (sstore σ') ->
        IsOfType v t.
  Proof.
    induction 1; try (solve [trivial]).
    intros WT; eapply IHMOP.
    eapply VOPAssoc_inv_well_typed_values_in_sstore; eauto.
  Qed.
  
End OPMap.
