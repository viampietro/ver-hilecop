(** Defines the relation that elaborates the generic clause of a
    design, as declared in abstract syntax.
    
    The result is the addition of entries refering to generic constant
    declarations in the design environment.  *)

Require Import Coqlib.
Require Import GlobalTypes.
Require Import AbstractSyntax.
Require Import SemanticalDomains.
Require Import Environment.
Require Import ExpressionEvaluation.
Require Import StaticExpressions.
Require Import TypeElaboration.

Include NatMap.

(** The generic constant elaboration relation.
    
    The [dimen] parameter is the dimensioning function (M); that is, the
    function yielding the values assigned to the generic constants
    being elaborated.  *)

Inductive egens (denv : DEnv) (dimen : IdMap value) : gdecl -> DEnv -> Prop :=

(* Elaboration with given a dimensioning value. *)
| EGensDimen :
    forall {idg tau e t dv v},
      
      (* Premises *)
      etypeg tau t ->
      is_lstatic_expr e ->
      vexpr EmptyDEnv EmptyDState EmptyLEnv e (Some dv) ->

      (* Side conditions *)
      ~In idg denv ->           (* idg ∉ Δ *)
      MapsTo idg v dimen ->     (* idg ∈ M and M(idg) = v *)
      
      (* Conclusion *)
      egens denv dimen (gdecl_ idg tau e) (add idg (Generic t v) denv)

(* Elaboration with default value. *)
| EGensDefault :
    forall {idg tau e t dv},
      
      (* Premises *)
      etypeg tau t ->
      is_lstatic_expr e ->
      vexpr EmptyDEnv EmptyDState EmptyLEnv e (Some dv) ->

      (* Side conditions *)
      ~In idg denv ->      (* idg ∉ Δ *)
      ~In idg dimen ->     (* idg ∉ M *)
      
      (* Conclusion *)
      egens denv dimen (gdecl_ idg tau e) (add idg (Generic t dv) denv)

(* Elaboration of a sequence of generic constant declaration. *)
| EGensSeq:
    forall {gd gd' denv' denv''},
      egens denv dimen gd denv' ->
      egens denv' dimen gd' denv'' ->
      egens denv dimen (gdecl_seq gd gd') denv''.

      

