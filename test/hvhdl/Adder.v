(** * H-VHDL Simple Adder Design *)

Require Import common.Coqlib.
Require Import common.NatSet.
Require Import common.NatMap.
Require Import common.NatMapFacts.
Require Import common.ListPlus.
Require Import common.ListPlusTactics.
Require Import common.ListPlusFacts.

Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.AbstractSyntaxFacts.
Require Import hvhdl.AbstractSyntaxTactics.
Require Import hvhdl.HVhdlTypes.
Require Import hvhdl.Environment.
Require Import hvhdl.Elaboration.
Require Import hvhdl.ElaborationFacts.
Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.Petri.
Require Import hvhdl.WellDefinedDesign.
Require Import hvhdl.WellDefinedDesignFacts.

Local Open Scope abss_scope.
Local Open Scope natset_scope.

Import HVhdlCsNotations.

(** ** Input ports *)

(** Input port identifiers *)

Definition a : ident := 2.
Definition b : ident := S a.

(** Input port declarations *)

Definition ins : list pdecl := [pdecl_in a tind_boolean; pdecl_in b tind_boolean].

(** ** Output ports *)

(** Out port identifiers *)

Definition o : ident := S b.
Definition outs : list pdecl := [pdecl_out o tind_boolean].

(** ** Declared signals *)

(** Declared signal identifiers *)

Definition s_add : ident := S o.
Definition sigs : list sdecl := [sdecl_ s_add tind_boolean].

(** ** Adder behavior *)

(** Process "add" (combinational) *)

Definition add_ps_id : ident := S s_add.
Definition add_ps : cs := cs_ps add_ps_id {[ a, b ]} [] (s_add @<== (#a @|| #b)).

(** Process "publish" (synchronous) *)

Definition publish_ps_id : ident := S add_ps_id.
Definition publish_ps : cs := cs_ps publish_ps_id {[ clk, rst ]} [] (Falling (o @<== #s_add)).

(** ** Adder design *)
Definition adder_id__e : ident := S publish_ps_id.
Definition adder_id__a : ident := S adder_id__e.
Definition adder : design := design_ adder_id__e adder_id__a [] (ins ++ outs) sigs
                                     (add_ps // publish_ps).
Set Printing Coercions.

Lemma vexpr_determ :
  forall {e Δ σ Λ mode v v'},
    vexpr Δ σ Λ mode e v ->
    vexpr Δ σ Λ mode e v' -> v = v'.
Proof.
  induction e.
  
  (* CASE e is a nat constant *)
  - do 2 inversion 1; auto.

  (* CASE e is a bool constant *)
  - do 2 inversion 1; auto.

  (* CASE e is a name *)
  - inversion 1.    
    + inversion 1; eauto with mapsto.
      -- admit. (* CASE id ∈ σ and id ∈ Λ, violates identifier unicity. *)
      -- mapsto_discriminate. (* CASE id ∈ Gens(Δ) and id ∈ Sigs(Δ) ∪ Ins(Δ), impossible by def. *)
    + inversion 1; eauto with mapsto.
      -- admit. (* CASE id ∈ σ and id ∈ Λ, violates identifier unicity. *)
      -- mapsto_discriminate. (* CASE id ∈ Gens(Δ) and id ∈ Outs(Δ), impossible by def. *)
    + inversion 1; eauto with mapsto.
      -- admit. (* CASE id ∈ σ and id ∈ Λ, violates identifier unicity. *)
      -- admit. (* CASE id ∈ σ and id ∈ Λ, violates identifier unicity. *)
      -- admit.
      -- admit. (* CASE id ∈ σ and id ∈ Λ, violates identifier unicity. *)
    + inversion 1; (eauto with mapsto || mapsto_discriminate || idtac).
      -- admit. (* CASE id ∈ σ and id ∈ Λ, violates identifier unicity. *)
      -- admit. (* CASE id ∈ σ and id ∈ Λ, violates identifier unicity. *)
    + inversion 1.
Admitted.

Lemma econstr_determ :
  forall {Δ e e' n m n' m'},
    econstr Δ e e' n m -> econstr Δ e e' n' m' -> n = n' /\ m = m'.
Proof.
  intros Δ e e' n m n' m' Heconstr Heconstr'.
  inversion Heconstr; inversion Heconstr'.
  lazymatch goal with
  | [ Hvexprn : vexpr _ _ _ _ ?e _,
      Hvexprn' : vexpr _ _ _ _?e _,
      Hvexprm : vexpr _ _ _ _ ?e' _,
      Hvexprm' : vexpr _ _ _ _?e' _
      |- _ ] =>
    specialize (vexpr_determ Hvexprn Hvexprn');
      specialize (vexpr_determ Hvexprm Hvexprm');
      intros Heqvm Heqvn;
      injection Heqvm as Heqm;
      injection Heqvn as Heqvn;
      split; assumption
  end.
Qed.

Lemma etype_determ : forall {τ Δ t t'}, etype Δ τ t -> etype Δ τ t' -> t = t'.
Proof.
  induction τ;
    intros Δ t t' Ht Ht'; inversion Ht; inversion Ht'; auto.
  (* Constraints are equal *)
  - lazymatch goal with
    | [ Heconstr: econstr _ _ _ _ _, Heconstr': econstr _ _ _ _ _ |- _ ] =>
      specialize (econstr_determ Heconstr Heconstr'); intros [Heq Heq'];
        rewrite Heq, Heq'; reflexivity
    end.
  (* Constraints and type of elements are equal. *)
  - lazymatch goal with
    | [ Heconstr: econstr _ _ _ _ _, Heconstr': econstr _ _ _ _ _, Het: etype _ τ ?t0, Het': etype _ τ ?t1 |- _ ] =>
      specialize (econstr_determ Heconstr Heconstr');
        specialize (IHτ Δ t0 t1 Het Het');
        intros [Heq Heq'];
        rewrite Heq, Heq', IHτ;
        reflexivity
    end.
Qed.

Lemma defaultv_determ : forall {t v v'}, defaultv t v -> defaultv t v' -> v = v'.
Proof.
Admitted.

Lemma eport_elab_sigma :
  forall Δ σ id τ Δ' σ' t v,
    (eport Δ σ (pdecl_out id τ) Δ' σ' \/ eport Δ σ (pdecl_in id τ) Δ' σ') ->
    etype Δ τ t ->
    defaultv t v ->
    MapsTo id v (sigstore σ').
Proof.
  inversion 1 as [Hep|Hep];
    inversion Hep; intros;
    lazymatch goal with
    | [ Het: etype ?Δ ?τ _, Het': etype ?Δ ?τ _, Hdv: defaultv _ _, Hdv': defaultv _ _ |- _ ] =>
      specialize (etype_determ Het Het') as Heqt; rewrite Heqt in Hdv;
        specialize (defaultv_determ Hdv Hdv') as Heqdv;
        rewrite Heqdv; simpl; auto with mapsto
    end.
Qed.

Definition AreUniquePortIds (ports : list pdecl) (portids : list ident) :=
  let pdecl2id := fun pd => match pd with pdecl_in id' _ | pdecl_out id' _ => id' end in
  Map pdecl2id ports portids /\ List.NoDup portids.

Lemma eports_elab_sigma :
  forall Δ σ ports Δ' σ' ,
    eports Δ σ ports Δ' σ' ->
    forall id τ t v portids,
      (List.In (pdecl_in id τ) ports \/ List.In (pdecl_out id τ) ports) ->
      (forall Δ__ep, EqGens Δ Δ__ep -> etype Δ__ep τ t) ->
      defaultv t v ->
      AreUniquePortIds ports portids ->
      MapsTo id v (sigstore σ').
Proof.
  induction 1.
  
  - inversion 1; contradiction.
  - inversion_clear 1 as [Hpdecl | Hpdecl].
    all :
      inversion_clear Hpdecl as [ Heq_pd | Hin_lofpds];
      [
        (* CASE (id, mode, τ) = pd *)
        rewrite Heq_pd in H; intros Hetype Hdv Hare_uniq_portids;

        (* Apply eports_elab_idle_sigma *)
        eapply eports_elab_idle_sigma; eauto;
        [
          (* Deals with [∄τ, (id, mode, τ) ∈ lofpdecls] *)
          intros Hex; inversion_clear Hex as (τ', [Hpdecl | Hpdecl]);
          inversion_clear Hare_uniq_portids as (Hmap, Hnodup_portids);
          inversion Hmap; rewrite Heq_pd in *; rewrite <- H2 in *;
          specialize (Map_in H4 Hpdecl) as Hin_m; simpl in Hin_m;
          rewrite NoDup_cons_iff in Hnodup_portids; apply (proj1 Hnodup_portids); assumption
        |
        (* Apply eport_elab_sigma to get [σ'("id") = v]. *)      
        eapply eport_elab_sigma; eauto with hvhdl
        ]
      | (* CASE [(id, mode, τ) ∈ lofpdecls] *)
      intros Hetype Hdv Huniq;
      inversion_clear Huniq as (Hmap, Hnodup);
      inversion_clear Hmap in Hnodup;
      eapply IHeports with (portids := m); eauto with hvhdl;
      split; [auto | apply (proj2 ((proj1 (NoDup_cons_iff _ m)) Hnodup))]
      ].
Qed.

Lemma elab_out_port_sigma :
  forall id τ D__s M__g d Δ σ__e t v,
    edesign D__s M__g d Δ σ__e ->
    HasUniqueIds d ->
    (List.In (pdecl_in id τ) (ports d) \/ List.In (pdecl_out id τ) (ports d)) ->
    (forall Δ__ep, EqGens Δ Δ__ep -> etype Δ__ep τ t) ->
    defaultv t v ->
    MapsTo id v (sigstore σ__e).
Proof.
  inversion 1; simpl; intros.

  (* Builds a list of [cs] out of [behavior]. *)
  build_lofcs behavior.

  (* Apply [ebeh_elab_idle_sigma] lemma. *)
  eapply ebeh_elab_idle_sigma; eauto.

  (* Apply [edecls_elab_idle_sigma] lemma. *)
  lazymatch goal with
  | [ d: design, Heq: _ = d |- _ ] =>
      eapply edecls_elab_idle_sigma; rewrite <- Heq; eauto;
        replace sigs0 with (AbstractSyntax.sigs d) by (rewrite <- Heq; reflexivity);
        only 1 : (eapply is_unique_port_id_sigs with (τ := τ); rewrite <- Heq; simpl; eauto)
  end.  

  (* Apply [eports_elab_sigma] lemma. *)
  lazymatch goal with
  | [ H: HasUniqueIds _ |- _ ] =>
    inv_hasuniqids H;
      clear Hbehids Hnodupvars;
      unfold AreDeclPartIds in Hdeclids; simpl in *
  end.
  eapply eports_elab_sigma with (portids := portids); eauto.

  { (* Prove premise [forall Δ__ep : ElDesign, EqGens Δ0 Δ__ep -> etype Δ__ep τ t0]. *)
    lazymatch goal with
    | [ H: forall _, EqGens _ _ -> _ |- _ ] =>
      intros Δ__ep Heqgens; apply H; rewrite <- Heqgens; symmetry;
        transitivity Δ''; eauto with hvhdl
    end.
  }
     
  { (* Prove premise [AreUniquePortIds ports portids] *)
    unfold AreUniquePortIds.
    split; [ firstorder |
             red_nodup Hnodupids;
             lazymatch goal with
             | [ H: List.NoDup (_ ++ _) |- _ ] =>
               get_nodup_at H 1; assumption
             end ]. }
Qed.

Lemma adder_o_defaultv :
  forall Δ__adder σ__e,
    edesign (empty design) (empty value) adder Δ__adder σ__e ->
    MapsTo o (Vbool false) (sigstore σ__e).
Proof.
  intros *; intros Helab.
  eapply elab_out_port_sigma with (τ := tind_boolean) (t := Tbool); eauto.
    [right; simpl; tauto | auto with hvhdl | auto with hvhdl ].
Qed.
