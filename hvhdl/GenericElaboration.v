(** Defines the relation that elaborates the generic clause of a
    design, as declared in abstract syntax.
    
    The result is the addition of entries refering to generic constant
    declarations in the design environment.  *)

Require Import CoqLib.
Require Import GlobalTypes.
Require Import AbstractSyntax.
Require Import SemanticalDomains.
Require Import Environment.
Require Import ExpressionEvaluation.
Require Import StaticExpressions.
Require Import TypeElaboration.
Require Import HVhdlTypes.

Import NatMap.

(** The generic constant elaboration relation.
    
    The [dimen] parameter is the dimensioning function (M); that is, the
    function yielding the values assigned to the generic constants
    being elaborated.  *)

Inductive egens (ed : ElDesign) (dimen : IdMap value) : list gdecl -> ElDesign -> Prop :=

(* Elaborates an empty list of generic constant declaration. *)
| EGensNil: egens ed dimen [] ed

(* Elaborates a non-empty list of generic constant declaration. *)
| EGensCons:
    forall {gd lofgdecls ed' ed''},
      egen ed dimen gd ed' ->
      egens ed' dimen lofgdecls ed'' ->
      egens ed dimen (gd :: lofgdecls) ed''
    
(** Defines the elaboration relation for one generic constant declaration. *)
with egen (ed : ElDesign) (dimen : IdMap value) : gdecl -> ElDesign -> Prop :=
  
(* Elaboration with given a dimensioning value. *)
| EGenDimen :
    forall {idg tau e t dv v},
      
      (* Premises *)
      etypeg tau t ->
      is_lstatic_expr e ->
      vexpr EmptyElDesign EmptyDState EmptyLEnv false e dv ->

      (* Side conditions *)
      ~NatMap.In idg ed ->           (* idg ∉ Δ *)
      MapsTo idg v dimen ->     (* idg ∈ M and M(idg) = v *)
      
      (* Conclusion *)
      egen ed dimen (gdecl_ idg tau e) (add idg (Generic t v) ed)

(* Elaboration with default value. *)
| EGenDefault :
    forall {idg tau e t dv},
      
      (* Premises *)
      etypeg tau t ->
      is_lstatic_expr e ->
      vexpr EmptyElDesign EmptyDState EmptyLEnv false e dv ->

      (* Side conditions *)
      ~NatMap.In idg ed ->      (* idg ∉ Δ *)
      ~NatMap.In idg dimen ->     (* idg ∉ M *)
      
      (* Conclusion *)
      egen ed dimen (gdecl_ idg tau e) (add idg (Generic t dv) ed).

      

