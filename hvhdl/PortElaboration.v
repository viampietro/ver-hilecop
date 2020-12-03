(** Defines the relation that elaborates the port clause of a design,
    declared in abstract syntax.

    The result is the addition of entries refering to port
    declarations in the design environment [ed] (Δ) and the mapping
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

Inductive eports (ed : ElDesign) (dstate : DState) : list pdecl -> ElDesign -> DState -> Prop :=

(** Empty list of port declarations. *)
| EPortsNil : eports ed dstate [] ed dstate
  
(** Sequence of port declarations. *)
| EPortsCons :
    forall {pd lofpdecls ed' dstate' dstate'' ed''},
      eport ed dstate pd ed' dstate' ->
      eports ed' dstate' lofpdecls ed'' dstate'' ->
      eports ed dstate (pd :: lofpdecls) ed'' dstate''

(** Defines the elaboration relation for single port declaration. *)
with eport (ed : ElDesign) (dstate : DState) : pdecl -> ElDesign -> DState -> Prop :=
  
(** Declaration of port in "in" mode. *)
| EPortIn :
    forall {tau t v id},
    
      (* Premises. *)
      etype ed tau t ->
      defaultv t v ->
      
      (* Side conditions. *)
      ~NatMap.In id ed ->           (* id ∉ Δ *)
      ~InSStore id dstate -> (* id ∉ σ *)

      (* Conclusion *)
      eport ed dstate (pdecl_in id tau) (add id (Input t) ed) (sstore_add id v dstate)

(** Declaration of port in "out" mode. *)
| EPortOut :
    forall {tau t v id},
      
      (* Premises. *)
      etype ed tau t ->
      defaultv t v ->
      
      (* Side conditions. *)
      ~NatMap.In id ed ->           (* id ∉ Δ *)
      ~InSStore id dstate -> (* id ∉ σ *)

      (* Conclusion *)
      eport ed dstate (pdecl_in id tau) (add id (Output t) ed) (sstore_add id v dstate).
