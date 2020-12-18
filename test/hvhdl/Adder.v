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

Lemma vexpr_deterministic :
  forall e Δ σ Λ mode v v',
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

Lemma econstr_eq_bounds :
  forall Δ e e' n m n' m',
    econstr Δ e e' n m -> econstr Δ e e' n' m' -> n = n' /\ m = m'.
Proof.
  intros Δ e e' n m n' m' Heconstr Heconstr'.
  inversion Heconstr; inversion Heconstr'.

    
Lemma etype_eq_type : forall Δ τ t t', etype Δ τ t -> etype Δ τ t' -> t = t'.
  intros Δ τ t t' Ht Ht'.
  inversion Ht; inversion Ht';
  (reflexivity || match goal with
                 | [ Heq: _ = ?a, Heq': _ = ?a |- _ ] =>
                   rewrite <- Heq in Heq';
                   (discriminate
                    || injection Heq'; intros Heqe Heqe'; rewrite Heqe, Heqe' in *)
                 | _ => auto
                  end).

Lemma eport_defaultv :
  forall Δ σ id τ Δ' σ' t v,
    (eport Δ σ (pdecl_out id τ) Δ' σ' \/ eport Δ σ (pdecl_in id τ) Δ' σ') ->
    etype Δ τ t ->
    defaultv t v ->
    MapsTo id v (sigstore σ').
Proof.
  intros Δ σ id τ Δ' σ' t v Hv_eport Hetype Hdv.
  inversion_clear Hv_eport; inversion_clear H.
Admitted.


  
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
Admitted.

