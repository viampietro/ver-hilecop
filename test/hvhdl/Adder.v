(** * H-VHDL Simple Adder Design *)

Require Import common.Coqlib.
Require Import common.NatSet.
Require Import common.NatMap.
Require Import common.NatMapFacts.

Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.HVhdlTypes.
Require Import hvhdl.Environment.
Require Import hvhdl.Elaboration.
Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.Petri.

Local Open Scope abss_scope.
Local Open Scope natset_scope.

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

Lemma eport_defaultv :
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
  
Lemma adder_o_defaultv :
  forall Δ__adder σ__e,
    edesign (empty design) (empty value) adder Δ__adder σ__e ->
    MapsTo o (Vbool false) (sigstore σ__e).
Proof.
  intros *; intros Helab.
  inversion_clear Helab.
  unfold outs in H0.
  do 3 (match goal with
        | [ H: eports _ _ _ _ _ |- _ ] => inversion_clear H
        end).
  lazymatch goal with
  | [ Heport_o: eport _ _ (pdecl_out o _) _ _ |- _ ] =>
    inversion Heport_o
  end.
  inversion_clear H8 in H9.
  inversion H9 in H12.
Qed.
