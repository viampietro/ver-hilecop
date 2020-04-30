(** Predicates for static expression qualification. 
    
    A static expression is either locally or globally static.
 *)

Require Import Coqlib.
Require Import GlobalTypes.
Require Import AbstractSyntax.
Require Import Environment.
Require Import SemanticalDomains.
Require Import HVhdlTypes.

(** Defines the inductive predicate [is_lstatic_expr] stating that an
    expression is locally static, i.e it is:
    
    - composed of operators and operands of a scalar type (i.e, natural, boolean).  
    - a literal of a scalar type.
 *)

Inductive is_lstatic_expr : expr -> Prop :=
| IsLStaticNat (n : nat) : is_lstatic_expr (e_nat n)
| IsLStaticBool (b : bool) : is_lstatic_expr (e_bool b)
| IsLStaticNot (e : expr) : is_lstatic_expr e -> is_lstatic_expr (e_not e)
| IsLStaticBinOp (e e' : expr) (bop : binop) :
    is_lstatic_expr e -> is_lstatic_expr e' -> is_lstatic_expr (e_binop bop e e').

(** Defines the inductive predicate [is_gstatic_expr] stating that an
    expression is globally static, i.e it is:
    
    - a generic constant.
    - a constant.
    - an array aggregate composed of globally static expressions.
    - a locally static expression.
 *)

Inductive is_gstatic_expr (env : DEnv) : expr -> Prop :=
| IsGStaticLStatic (e : expr) : is_lstatic_expr e -> is_gstatic_expr env e
| IsGStaticGeneric (id : ident) :
    forall (t : type) (v : value),
      MapsTo id (Generic t v) env -> is_gstatic_expr env (e_name (n_id id))
| IsGStaticConstant (id : ident) :
    forall (t : type) (v : value),
      MapsTo id (Constant t v) env -> is_gstatic_expr env (e_name (n_id id))
| IsGStaticAggreg (l : list expr) :
    (forall (e : expr), List.In e l -> is_gstatic_expr env e) ->
    is_gstatic_expr env (e_aggreg l).
    
