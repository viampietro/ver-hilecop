(** Defines the constraint elaboration relation that interprets, for a
    given elaborated design Δ, a constraint of the abstract syntax,
    expressed as a couple of expressions, into a couple of natural
    numbers.
    
    Some validity check are performed on the constraint being
    transformed.  *)

Require Import common.CoqLib.

Require Import AbstractSyntax.
Require Import Environment.
Require Import StaticExpressions.
Require Import ExpressionEvaluation.
Require Import SemanticalDomains.

Open Scope N_scope.

(** The constraint elaboration relation (general definition). *)

Inductive EConstr (Δ : ElDesign) (e e' : expr) (n n' : N) : Prop :=
| EConstr_ :
    (* Premises *)

    IGStaticExpr Δ e ->   (* Expression e must be globally static. *)
    IGStaticExpr Δ e' ->  (* Expression e' must be globally static. *)
    
    (* VExpr checks that the bounds are nat values comprised in the
       interval [0, NATMAX]. *)
    VExpr Δ EmptySStore EmptyLEnv false e (Vnat n) -> (* e evaluates to (Vnat n) *)
    VExpr Δ EmptySStore EmptyLEnv false e' (Vnat n') -> (* e' evaluates to (Vnat n') *)

    n <= n' -> (* Upper bound must be greater or equal to lower bound *)

    EConstr Δ e e' n n'.


(** The constraint elaboration relation (definition for generic constant declaration). *)

Inductive EConstrG (e e' : expr) (n n' : N) : Prop :=
| EConstrG_ :
    (* Premises *)

    IsLStaticExpr e ->   (* Expression e must be globally static. *)
    IsLStaticExpr e' ->  (* Expression e' must be globally static. *)
    
    VExpr EmptyElDesign EmptySStore EmptyLEnv false e (Vnat n) -> (* e evaluates to (Vnat n) *)
    VExpr EmptyElDesign EmptySStore EmptyLEnv false e' (Vnat n') -> (* e' evaluates to (Vnat n') *)

    n <= n' -> (* Upper bound must be greater or equal to lower bound *)

    EConstrG e e' n n'.

