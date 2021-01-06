(** Defines the relation that elaborates the architecture declarative
    part of a design, declared in abstract syntax.

    The result is the addition of entries refering to constant and
    declared signal declarations in the design environment [ed] (Δ)
    and the mapping from declared signal id to their default value in
    the design state [dstate] (σ).  *)

Require Import Coqlib.
Require Import GlobalTypes.
Require Import AbstractSyntax.
Require Import SemanticalDomains.
Require Import Environment.
Require Import ExpressionEvaluation.
Require Import StaticExpressions.
Require Import TypeElaboration.
Require Import DefaultValue.

Import NatMap.

(** The architecture declarative part elaboration relation. *)

Inductive edecls (Δ : ElDesign) (σ : DState)  : list sdecl -> ElDesign -> DState -> Prop :=

(** Empty list of architecture declarations. *)
| EDeclsNil : edecls Δ σ [] Δ σ
  
(** Sequence of architecture declaration. *)
| EDeclsCons :
    forall {ad lofsigs Δ' σ' Δ'' σ''},
      edecl Δ σ ad Δ' σ' ->
      edecls Δ' σ' lofsigs Δ'' σ'' ->
      edecls Δ σ (ad :: lofsigs) Δ'' σ''

(** Defines the elaboration relation for single architecture declaration. *)
with edecl (Δ : ElDesign) (σ : DState)  : sdecl -> ElDesign -> DState -> Prop :=
  
(** Signal declaration elaboration. *)
  
| EDeclSig :
    forall {τ t v id},
      
      (* Premises. *)
      etype Δ τ t ->
      defaultv t v ->
      
      (* Side conditions. *)
      ~NatMap.In id Δ -> (* id ∉ Δ *)
      ~InSStore id σ ->  (* id ∉ σ *)

      (* Conclusion *)
      edecl Δ σ (sdecl_ id τ) (add id (Declared t) Δ) (sstore_add id v σ).
