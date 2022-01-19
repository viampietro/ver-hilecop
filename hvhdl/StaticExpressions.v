(** Predicates for static expression qualification. 
    
    A static expression is either locally or globally static.
 *)

Require Import common.CoqLib.
Require Import common.GlobalTypes.
Require Import common.NatMap.

Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.Environment.
Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.HVhdlTypes.

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

#[export] Hint Constructors is_lstatic_expr : hvhdl.

(** Defines the inductive predicate [is_gstatic_expr] stating that an
    expression is globally static, i.e it is:
    
    - a generic constant.
    - a constant.
    - an array aggregate composed of globally static expressions.
    - a locally static expression.
 *)

Inductive is_gstatic_expr (Δ : ElDesign) : expr -> Prop :=
| IsGStaticLStatic (e : expr) : is_lstatic_expr e -> is_gstatic_expr Δ e
| IsGStaticBinOp (e e' : expr) (bop : binop) :
    is_gstatic_expr Δ e -> is_gstatic_expr Δ e' -> is_gstatic_expr Δ (e_binop bop e e')
| IsGStaticGeneric (id : ident) :
    forall (t : type) (v : value),
      MapsTo id (Generic t v) Δ -> is_gstatic_expr Δ (e_name (n_id id))
| IsGStaticAggreg (ag : agofexprs) :
    (forall (e : expr), List.In e ag -> is_gstatic_expr Δ e) ->
    is_gstatic_expr Δ (e_aggreg ag).
    
#[export] Hint Constructors is_gstatic_expr : hvhdl.
