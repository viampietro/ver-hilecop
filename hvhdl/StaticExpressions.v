(** * Static expressions *)

Require Import common.CoqLib.
Require Import common.GlobalTypes.
Require Import common.NatMap.
Require Import String.

Import ErrMonadNotations.

Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.Environment.
Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.HVhdlTypes.

(** ** Locally static expressions *)

Section LStaticExpr.

  (** Defines the relation [IsLStaticExpr] stating that an
      expression is locally static, i.e it is:
    
      - composed of operators and operands of a scalar type (i.e, natural, boolean).  
      - a literal of a scalar type.
   *)

  Inductive IsLStaticExpr : expr -> Prop :=
  | IsLStaticNat (n : N) : IsLStaticExpr (e_nat n)
  | IsLStaticBool (b : bool) : IsLStaticExpr (e_bool b)
  | IsLStaticNot (e : expr) : IsLStaticExpr e -> IsLStaticExpr (e_not e)
  | IsLStaticBinOp (e e' : expr) (bop : binop) :
    IsLStaticExpr e -> IsLStaticExpr e' -> IsLStaticExpr (e_binop bop e e').

  (** Returns [true] if expression [e] is a locally static expression;
      false otherwise. *)

  Fixpoint is_lstatic_expr (e : expr) {struct e} : bool :=
    match e with
    | e_nat _ | e_bool _ => true
    | e_not e1 => is_lstatic_expr e1
    | e_binop _ e1 e2 => is_lstatic_expr e1 && is_lstatic_expr e2
    | _ => false
    end.
  
End LStaticExpr.

#[export] Hint Constructors IsLStaticExpr : hvhdl.

(** ** Globally static expressions *)

Section GStaticExpr.

  (** Defines the inductive predicate [IGStaticExpr] stating that an
    expression is globally static, i.e it is:
    
    - a generic constant.
    - a constant.
    - an array aggregate composed of globally static expressions.
    - a locally static expression.
   *)

  Inductive IGStaticExpr (Δ : ElDesign) : expr -> Prop :=
  | IsGStaticLStatic (e : expr) : IsLStaticExpr e -> IGStaticExpr Δ e
  | IsGStaticBinOp (e e' : expr) (bop : binop) :
    IGStaticExpr Δ e -> IGStaticExpr Δ e' -> IGStaticExpr Δ (e_binop bop e e')
  | IsGStaticGeneric (id : ident) :
    forall (t : type) (v : value),
      MapsTo id (Generic t v) Δ -> IGStaticExpr Δ (e_name (n_id id))
  | IsGStaticAggreg (ag : agofexprs) :
    (forall (e : expr), List.In e ag -> IGStaticExpr Δ e) ->
    IGStaticExpr Δ (e_aggreg ag).

  (** Returns [true] if [e] is a globally static expression; [false]
      otherwise. *)
  
  Fixpoint is_gstatic_expr (Δ : ElDesign) (e : expr) {struct e} : bool :=
    match e with
    | e_binop _ e1 e2 => is_gstatic_expr Δ e1 && is_gstatic_expr Δ e2
    | (e_name (n_id id)) =>
        match find id Δ with Some (Generic _ _) => true | _ => false end
    | e_aggreg ag => is_gstatic_agofexprs Δ ag
    | _ => is_lstatic_expr e
    end
  with is_gstatic_agofexprs (Δ : ElDesign) (ag : agofexprs) {struct ag} : bool :=
         match ag with
         | agofe_one e => is_gstatic_expr Δ e
         | agofe_cons e agtl => is_gstatic_expr Δ e && is_gstatic_agofexprs Δ agtl
         end.
        
End GStaticExpr.

    
#[export] Hint Constructors IGStaticExpr : hvhdl.
