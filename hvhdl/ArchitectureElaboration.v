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

Inductive edecls (ed : ElDesign) (dstate : DState)  : list adecl -> ElDesign -> DState -> Prop :=

(** Empty list of architecture declarations. *)
| EDeclsNil : edecls ed dstate [] ed dstate
  
(** Sequence of architecture declaration. *)
| EDeclsCons :
    forall {ad lofadecls ed' dstate' ed'' dstate''},
      edecl ed dstate ad ed' dstate' ->
      edecls ed' dstate' lofadecls ed'' dstate'' ->
      edecls ed dstate (ad :: lofadecls) ed'' dstate''

(** Defines the elaboration relation for single architecture declaration. *)
with edecl (ed : ElDesign) (dstate : DState)  : adecl -> ElDesign -> DState -> Prop :=
  
(** Signal declaration elaboration. *)
  
| EDeclSig :
    forall {tau t v id},
      
      (* Premises. *)
      etype ed tau t ->
      defaultv t v ->
      
      (* Side conditions. *)
      ~NatMap.In id ed -> (* id ∉ Δ *)
      ~InSStore id dstate ->  (* id ∉ σ *)

      (* Conclusion *)
      edecl ed dstate (adecl_sig id tau) (add id (Declared t) ed) (sstore_add id v dstate).
