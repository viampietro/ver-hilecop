(** * Port Elaboration *)

(** Defines the relation that elaborates the port clause of a design,
    declared in abstract syntax.

    The result is the addition of entries refering to port
    declarations in the design environment [Δ] (Δ) and the mapping
    from port id to their default value in the design state [σ]
    (σ).  *)

Require Import CoqLib.
Require Import GlobalTypes.
Require Import AbstractSyntax.
Require Import SemanticalDomains.
Require Import Environment.
Require Import ExpressionEvaluation.
Require Import TypeElaboration.
Require Import DefaultValue.

Import NatMap.

(** The port elaboration relation. *)

Inductive eports (Δ : ElDesign) (σ : DState) : list pdecl -> ElDesign -> DState -> Prop :=

(** Empty list of port declarations. *)
| EPortsNil : eports Δ σ [] Δ σ
  
(** Sequence of port declarations. *)
| EPortsCons :
    forall {pd lofpdecls Δ' σ' σ'' Δ''},
      eport Δ σ pd Δ' σ' ->
      eports Δ' σ' lofpdecls Δ'' σ'' ->
      eports Δ σ (pd :: lofpdecls) Δ'' σ''

(** Defines the elaboration relation for single port declaration. *)
with eport (Δ : ElDesign) (σ : DState) : pdecl -> ElDesign -> DState -> Prop :=
  
(** Declaration of port in "in" mode. *)
| EPortIn :
    forall τ t v id,
    
      (* Premises. *)
      etype Δ τ t ->
      DefaultV t v ->
      
      (* Side conditions. *)
      ~NatMap.In id Δ ->           (* id ∉ Δ *)
      ~InSStore id σ -> (* id ∉ σ *)

      (* Conclusion *)
      eport Δ σ (pdecl_in id τ) (add id (Input t) Δ) (sstore_add id v σ)

(** Declaration of port in "out" mode. *)
| EPortOut :
    forall τ t v id,
      
      (* Premises. *)
      etype Δ τ t ->
      DefaultV t v ->
      
      (* Side conditions. *)
      ~NatMap.In id Δ ->           (* id ∉ Δ *)
      ~InSStore id σ -> (* id ∉ σ *)

      (* Conclusion *)
      eport Δ σ (pdecl_out id τ) (add id (Output t) Δ) (sstore_add id v σ).
