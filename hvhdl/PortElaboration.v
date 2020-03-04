(** Defines the relation that elaborates the port clause of a design,
    declared in abstract syntax.

    The result is the addition of entries refering to port
    declarations in the design environment [denv] (Δ) and the mapping
    from port id to their default value in the design state [dstate]
    (σ).  *)

Require Import GlobalTypes.
Require Import AbstractSyntax.
Require Import SemanticalDomains.
Require Import Environment.
Require Import ExpressionEvaluation.
Require Import TypeElaboration.
Require Import DefaultValue.

Import NatMap.

(** The port elaboration relation. *)

Inductive eports (denv : DEnv) (dstate : DState) : pdecl -> DEnv -> DState -> Prop :=

(** Declaration of port in "in" mode. *)
| EPortsIn :
    forall {tau t v id},
    
      (* Premises. *)
      etype denv tau t ->
      defaultv t v ->
      
      (* Side conditions. *)
      ~In id denv ->           (* id ∉ Δ *)
      ~InSigStore id dstate -> (* id ∉ σ *)

      (* Conclusion *)
      eports denv dstate (pdecl_in id tau) (add id (Input t) denv) (sigstore_add id v dstate)

(** Declaration of port in "out" mode. *)
| EPortsOut :
    forall {tau t v id},
      
      (* Premises. *)
      etype denv tau t ->
      defaultv t v ->
      
      (* Side conditions. *)
      ~In id denv ->           (* id ∉ Δ *)
      ~InSigStore id dstate -> (* id ∉ σ *)

      (* Conclusion *)
      eports denv dstate (pdecl_in id tau) (add id (Output t) denv) (sigstore_add id v dstate)

(** Sequence of port declarations. *)
| EPortsSeq :
    forall {pd pd' denv' dstate' dstate'' denv''},
      eports denv dstate pd denv' dstate' ->
      eports denv' dstate' pd' denv'' dstate'' ->
      eports denv dstate (pdecl_seq pd pd') denv'' dstate''.
