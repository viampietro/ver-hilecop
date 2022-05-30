(** * Port Elaboration *)

(** Defines the relation that elaborates the port clause, i.e. the
    input and output port declaration list, of a H-VHDL design.

    The result is the addition of entries refering to port
    declarations in the elaborated design [Δ] and the mapping from
    port id to their default value in the default design state [σ]. *)

Require Import common.CoqLib.
Require Import common.GlobalTypes.

Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.Environment.
Require Import hvhdl.ExpressionEvaluation.
Require Import hvhdl.TypeElaboration.
Require Import hvhdl.DefaultValue.

Import NatMap.

(** The port elaboration relation. *)

Inductive EPorts (Δ : ElDesign) (σ : DState) : list pdecl -> ElDesign -> DState -> Prop :=

(** Empty list of port declarations. *)
| EPortsNil : EPorts Δ σ [] Δ σ
  
(** Sequence of port declarations. *)
| EPortsCons :
    forall pd lofpdecls Δ' σ' σ'' Δ'',
      EPort Δ σ pd Δ' σ' ->
      EPorts Δ' σ' lofpdecls Δ'' σ'' ->
      EPorts Δ σ (pd :: lofpdecls) Δ'' σ''

(** Defines the elaboration relation for single port declaration. *)
with EPort (Δ : ElDesign) (σ : DState) : pdecl -> ElDesign -> DState -> Prop :=
  
(** Declaration of port in "in" mode. *)
| EPortIn :
    forall τ t v id,
    
      (* Premises. *)
      EType Δ τ t ->
      DefaultV t v ->
      
      (* Side conditions. *)
      ~NatMap.In id Δ ->           (* id ∉ Δ *)
      ~InSStore id σ -> (* id ∉ σ *)

      (* Conclusion *)
      EPort Δ σ (pdecl_in id τ) (MkElDesign (add id (Input t) Δ)) (sstore_add id v σ)

(** Declaration of port in "out" mode. *)
| EPortOut :
    forall τ t v id,
      
      (* Premises. *)
      EType Δ τ t ->
      DefaultV t v ->
      
      (* Side conditions. *)
      ~NatMap.In id Δ ->           (* id ∉ Δ *)
      ~InSStore id σ -> (* id ∉ σ *)

      (* Conclusion *)
      EPort Δ σ (pdecl_out id τ) (MkElDesign (add id (Output t) Δ)) (sstore_add id v σ).
