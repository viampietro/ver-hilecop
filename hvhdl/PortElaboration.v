(** Defines the relation that elaborates the port clause of a design,
    declared in abstract syntax.

    The result is the addition of entries refering to port
    declarations in the design environment [denv] (Δ) and the mapping
    from port id to their default value in the design state [dstate]
    (σ).  *)

Require Import Coqlib.
Require Import GlobalTypes.
Require Import AbstractSyntax.
Require Import SemanticalDomains.
Require Import Environment.
Require Import ExpressionEvaluation.
Require Import TypeElaboration.
Require Import DefaultValue.

Import NatMap.

(** The port elaboration relation. *)

Inductive eports (denv : DEnv) (dstate : DState) : list pdecl -> DEnv -> DState -> Prop :=

(** Empty list of port declarations. *)
| EPortsNil : eports denv dstate [] denv dstate
  
(** Sequence of port declarations. *)
| EPortsCons :
    forall {pd lofpdecls denv' dstate' dstate'' denv''},
      eport denv dstate pd denv' dstate' ->
      eports denv' dstate' lofpdecls denv'' dstate'' ->
      eports denv dstate (pd :: lofpdecls) denv'' dstate''

(** Defines the elaboration relation for single port declaration. *)
with eport (denv : DEnv) (dstate : DState) : pdecl -> DEnv -> DState -> Prop :=
  
(** Declaration of port in "in" mode. *)
| EPortIn :
    forall {tau t v id},
    
      (* Premises. *)
      etype denv tau t ->
      defaultv t v ->
      
      (* Side conditions. *)
      ~NatMap.In id denv ->           (* id ∉ Δ *)
      ~InSStore id dstate -> (* id ∉ σ *)

      (* Conclusion *)
      eport denv dstate (pdecl_in id tau) (add id (Input t) denv) (sstore_add id v dstate)

(** Declaration of port in "out" mode. *)
| EPortOut :
    forall {tau t v id},
      
      (* Premises. *)
      etype denv tau t ->
      defaultv t v ->
      
      (* Side conditions. *)
      ~NatMap.In id denv ->           (* id ∉ Δ *)
      ~InSStore id dstate -> (* id ∉ σ *)

      (* Conclusion *)
      eport denv dstate (pdecl_in id tau) (add id (Output t) denv) (sstore_add id v dstate).
