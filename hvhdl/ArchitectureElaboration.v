(** Defines the relation that elaborates the list of internal signal
    declarations defined in a H-VHDL design.

    The result is the addition of entries refering to constant and
    declared signal declarations in the elaborated design Δ and the
    mapping from internal signal id to their default value in the
    default design state σ.  *)

Require Import common.CoqLib.
Require Import common.GlobalTypes.

Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.Environment.
Require Import hvhdl.ExpressionEvaluation.
Require Import hvhdl.StaticExpressions.
Require Import hvhdl.TypeElaboration.
Require Import hvhdl.DefaultValue.

Import NatMap.

(** The elaboration relation for internal signal declarations. *)

Inductive EDecls (Δ : ElDesign) (σ : DState)  : list sdecl -> ElDesign -> DState -> Prop :=

(** Empty list of architecture declarations. *)
| EDeclsNil : EDecls Δ σ [] Δ σ
  
(** Sequence of architecture declaration. *)
| EDeclsCons :
    forall sd lofsigs Δ' σ' Δ'' σ'',
      EDecl Δ σ sd Δ' σ' ->
      EDecls Δ' σ' lofsigs Δ'' σ'' ->
      EDecls Δ σ (sd :: lofsigs) Δ'' σ''

(** Defines the elaboration relation for single architecture declaration. *)
with EDecl (Δ : ElDesign) (σ : DState)  : sdecl -> ElDesign -> DState -> Prop :=
  
(** Signal declaration elaboration. *)
  
| EDeclSig :
    forall τ t v id,
      
      (* Premises. *)
      EType Δ τ t ->
      DefaultV t v ->
      
      (* Side conditions. *)
      ~NatMap.In id Δ -> (* id ∉ Δ *)
      ~InSStore id σ ->  (* id ∉ σ *)

      (* Conclusion *)
      EDecl Δ σ (sdecl_ id τ) (MkElDesign (add id (Internal t) Δ)) (sstore_add id v σ).
