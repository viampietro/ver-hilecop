(** Defines the constraint elaboration relation that interprets, in a
    design environment [ed] (Δ), a constraint of the abstract
    syntax, expressed as a couple of expressions into a couple of
    natural numbers.
    
    Some validity check are performed on the constraint being
    transformed.  *)

Require Import AbstractSyntax.
Require Import Environment.
Require Import StaticExpressions.
Require Import ExpressionEvaluation.
Require Import SemanticalDomains.

(** The constraint elaboration relation (general definition). *)

Inductive econstr (Δ : ElDesign) (e e' : expr) (n n' : nat) : Prop :=
| EConstr :
    (* Premises *)

    IGStaticExpr Δ e ->   (* Expression e must be globally static. *)
    IGStaticExpr Δ e' ->  (* Expression e' must be globally static. *)
    
    (* vexpr checks that the bounds are nat values comprised in the
       interval [0, NATMAX]. *)
    vexpr Δ EmptyDState EmptyLEnv false e (Vnat n) -> (* e evaluates to (Vnat n) *)
    vexpr Δ EmptyDState EmptyLEnv false e' (Vnat n') -> (* e' evaluates to (Vnat n') *)

    n <= n' -> (* Upper bound must be greater or equal to lower bound *)

    econstr Δ e e' n n'.

(** The constraint elaboration relation (definition for generic constant declaration). *)

Inductive econstrg (e e' : expr) (n n' : nat) : Prop :=
| EConstrG :
    (* Premises *)

    IsLStaticExpr e ->   (* Expression e must be globally static. *)
    IsLStaticExpr e' ->  (* Expression e' must be globally static. *)
    
    vexpr EmptyElDesign EmptyDState EmptyLEnv false e (Vnat n) -> (* e evaluates to (Vnat n) *)
    vexpr EmptyElDesign EmptyDState EmptyLEnv false e' (Vnat n') -> (* e' evaluates to (Vnat n') *)

    n <= n' -> (* Upper bound must be greater or equal to lower bound *)

    econstrg e e' n n'.

