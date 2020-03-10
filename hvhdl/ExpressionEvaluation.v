(** Module that implement the relation evaluating H-VHDL
    expressions. *)

Require Import Coqlib.
Require Import ListsPlus.
Require Import GlobalTypes.
Require Import AbstractSyntax.
Require Import Environment.
Require Import SemanticalDomains.
Require Import IsOfType.

Import NatMap.

(** Defines the expression evaluation relation. 
    
    The environment is composed of:
    - [denv], the design environment (Δ).
    - [dstate], the design state (σ).
    - [lenv], a local environment (process environment) (Λ).
    
 *)

Inductive vexpr (denv : DEnv) (dstate : DState) (lenv : LEnv) :
  expr -> value -> Prop :=

(** Evaluates nat constant. *) 
| VExprNat (n : nat) : n <= NATMAX -> vexpr denv dstate lenv (e_nat n) (Vnat n)

(** Evaluates bool constant. *)
| VExprBool (b : bool) : vexpr denv dstate lenv (e_bool b) (Vbool b)

(** Evaluates arc_t constant. *)
| VExprArcT (a : arc_t) : vexpr denv dstate lenv (e_arc a) (Varc a)

(** Evaluates arc_t constant. *)
| VExprTransT (t : transition_t) : vexpr denv dstate lenv (e_trans t) (Vtransition t)
                                         
(** Evaluates aggregate expression.
    
    The list of expressions [lofexprs] and the list of values
    [lofvalues] in parameter must be of the same length. *)
| VExprAggreg (lofe : list expr) (lofv : lofvalues) :
    vlofexprs denv dstate lenv lofe lofv ->
    vexpr denv dstate lenv (e_aggreg lofe) (Vlist lofv)

(** Evaluates a declared signal identifier . *)
          
| VExprSig (id : ident) (v : value) :
    forall (t : type),
      MapsTo id (Declared t) denv ->   (* id ∈ Sigs(Δ) and Δ(id) = t *)
      MapsTo id v (sigstore dstate) -> (* id ∈ σ and σ(id) = v *)
      vexpr denv dstate lenv (e_name (n_id id)) v

(** Evaluates an input signal identifier. *)

| VExprIn (id : ident) (v : value) :
    forall (t : type),
      MapsTo id (Input t) denv ->      (* id ∈ In(Δ) and Δ(id) = t *)
      MapsTo id v (sigstore dstate) -> (* id ∈ σ and σ(id) = v *)
      vexpr denv dstate lenv (e_name (n_id id)) v

(** Evaluates a variable identifier. *)
            
| VExprVar (id : ident) (t : type) (v : value) :
    MapsTo id (t, v) lenv ->      (* id ∈ Λ and Λ(id) = (t,v) *)
    vexpr denv dstate lenv (e_name (n_id id)) v
          
(** Evaluates a constant identifier. *)
          
| VExprConst (id : ident) (t : type) (v : value) :
    MapsTo id (Constant t v) denv ->      (* id ∈ Consts(Δ) and Δ(id) = (t,v) *)
    vexpr denv dstate lenv (e_name (n_id id)) v

(** Evaluates a constant identifier. *)
          
| VExprGen (id : ident) (t : type) (v : value) :
    MapsTo id (Generic t v) denv ->      (* id ∈ Gens(Δ) and Δ(id) = (t,v) *)
    vexpr denv dstate lenv (e_name (n_id id)) v

(** Evaluates an indexed declared signal identifier. *)
          
| VExprIdxSig (id : ident) (ei : expr):
    forall (t : type) (i l u : nat) (v v' : value) (lofv : lofvalues),

      (* Premises *)
      vexpr denv dstate lenv ei (Vnat i) -> (* index expression [ei] evaluates to [i] *)
      is_of_type (Vnat i) (Tnat l u) ->
      
      (* Side conditions *)
      MapsTo id (Declared (Tarray t l u)) denv ->      (* id ∈ Sigs(Δ) and Δ(id) = array(t, l, u) *)
      MapsTo id (Vlist lofv) (sigstore dstate) -> (* id ∈ σ and σ(id) = lofvalues *)
      get_at (i - l) lofv = Some v' ->
      
      (* Conclusion *)
      vexpr denv dstate lenv (e_name (n_xid id ei)) v'

(** Evaluates an indexed input signal identifier. *)
            
| VExprIdxIn (id : ident) (ei : expr):
    forall (t : type) (i l u : nat) (v v' : value) (lofv : lofvalues),

      (* Premises *)
      vexpr denv dstate lenv ei (Vnat i) -> (* index expression [ei] evaluates to [i] *)
      is_of_type (Vnat i) (Tnat l u) ->
      
      (* Side conditions *)
      MapsTo id (Input (Tarray t l u)) denv ->         (* id ∈ Ins(Δ) and Δ(id) = array(t, l, u) *)
      MapsTo id (Vlist lofv) (sigstore dstate) -> (* id ∈ σ and σ(id) = lofvalues *)
      get_at (i - l) lofv = Some v' ->
             
      (* Conclusion *)
      
      vexpr denv dstate lenv (e_name (n_xid id ei)) v'

(** Evaluates an indexed variable identifier. *)

| VExprIdxVar (id : ident) (ei : expr):
    forall (t : type) (i l u : nat) (v v' : value) (lofv : lofvalues),

      (* Premises *)
      vexpr denv dstate lenv ei (Vnat i) ->  (* index expression [ei] evaluates to [i] *)
      is_of_type (Vnat i) (Tnat l u) ->             (* index value is in array bounds. *)
      
      (* Side conditions *)
      MapsTo id ((Tarray t l u), (Vlist lofv)) lenv -> (* id ∈ Λ(Δ) and Λ(id) = (array(t, l, u), lofvalues) *)
      get_at (i - l) lofv = Some v' ->
      
      (* Conclusion *)      
      vexpr denv dstate lenv (e_name (n_xid id ei)) v'

(** Evaluates an indexed constant identifier. *)

| VExprIdxConst (id : ident) (ei : expr):
    forall (t : type) (i l u : nat) (v v' : value) (lofv : lofvalues),

      (* Premises *)
      vexpr denv dstate lenv ei (Vnat i) ->  (* index expression [ei] evaluates to [i] *)
      is_of_type (Vnat i) (Tnat l u) ->             (* index value is in array bounds. *)
      
      (* Side conditions *)
      MapsTo id (Constant (Tarray t l u) (Vlist lofv)) denv -> (* id ∈ Consts(Δ) and Δ(id) = (array(t, l, u), lofvalues) *)
      get_at (i - l) lofv = Some v' ->
      
      (* Conclusion *)      
      vexpr denv dstate lenv (e_name (n_xid id ei)) v'

(** Evaluates expression with addition operator. 
    
    The "nat overflow check" (i.e, v + v' <= NATMAX)
    is done in the [vadd] function.
 *)

| VExprAdd (e e' : expr):
    forall (n n' : nat),

      (* Premises:
         - Checks that operands evaluate to nat.
         - Checks that the addition does not cause nat overflow.
       *)
      vexpr denv dstate lenv e (Vnat n) -> 
      vexpr denv dstate lenv e' (Vnat n') ->
      n + n' <= NATMAX ->
      
      (* Conclusion *)      
      vexpr denv dstate lenv (e_binop bo_add e e') (Vnat (n + n'))

(** Evaluates expression with substraction operator. 
    
    The "out of natural scope" check (i.e, v <= v') 
    is done in the [vsub] function.
 *)

| VExprSub (e e' : expr):
    forall (n n' : nat),

      (* Premises:
         - Checks that operands evaluate to nat.     
         - Checks that the substraction does not go out of
           nat scope.
       *)
      vexpr denv dstate lenv e (Vnat n) ->
      vexpr denv dstate lenv e' (Vnat n') ->
      n > n' ->
      
      (* Conclusion *)      
      vexpr denv dstate lenv (e_binop bo_sub e e') (Vnat (n - n'))

(** Evaluates expression with the "less or equal" operator. *)

| VExprLE (e e' : expr):
    forall (n n' : nat),

      (* Premises: checks that operands evaluate to nat. *)
      vexpr denv dstate lenv e (Vnat n) -> 
      vexpr denv dstate lenv e' (Vnat n') ->
      
      (* Conclusion *)      
      vexpr denv dstate lenv (e_binop bo_le e e') (Vbool (n <=? n'))

(** Evaluates expression with the "strictly less" operator. *)

| VExprLT (e e' : expr):
    forall (n n' : nat),

      (* Premises: checks that operands evaluate to nat. *)
      vexpr denv dstate lenv e (Vnat n) -> 
      vexpr denv dstate lenv e' (Vnat n') ->
        
      (* Conclusion *)      
      vexpr denv dstate lenv (e_binop bo_lt e e') (Vbool (n <? n'))

(** Evaluates expression with the "greater or equal" operator. *)

| VExprGE (e e' : expr):
    forall (n n' : nat),

      (* Premises: checks that operands evaluate to nat. *)
      vexpr denv dstate lenv e (Vnat n) -> 
      vexpr denv dstate lenv e' (Vnat n') ->
      
      (* Conclusion *)      
      vexpr denv dstate lenv (e_binop bo_ge e e') (Vbool (n' <=? n))

(** Evaluates expression with the "strictly greater" operator. *)

| VExprGT (e e' : expr):
    forall (n n' : nat),

      (* Premises: checks that operands evaluate to nat. *)
      vexpr denv dstate lenv e (Vnat n) -> 
      vexpr denv dstate lenv e' (Vnat n') ->
      
      (* Conclusion *)      
      vexpr denv dstate lenv (e_binop bo_gt e e') (Vbool (n' <? n))

(** Evaluates expression with the "and" operator. *)

| VExprAnd (e e' : expr):
    forall (b b' : bool),

      (* Premises: checks that the operands evaluate to bool. *)
      vexpr denv dstate lenv e (Vbool b) -> 
      vexpr denv dstate lenv e' (Vbool b') ->
            
      (* Conclusion *)      
      vexpr denv dstate lenv (e_binop bo_and e e') (Vbool (b && b'))

(** Evaluates expression with the or operator. *)

| VExprOr (e e' : expr):
    forall (b b' : bool),

      (* Premises: checks that the operands evaluate to bool. *)
      vexpr denv dstate lenv e (Vbool b) ->
      vexpr denv dstate lenv e' (Vbool b') ->
      
      (* Conclusion *)      
      vexpr denv dstate lenv (e_binop bo_or e e') (Vbool (b || b'))

(** Evaluates expression with the not operator. *)

| VExprNot (e : expr):
    forall (b : bool),

      (* Premises: checks that the operand evaluates to bool. *)
      vexpr denv dstate lenv e (Vbool b) ->
            
      (* Conclusion. *)
      vexpr denv dstate lenv (e_not e) (Vbool (negb b))
            
(** Evaluates expression with the equality operator (bool). *)
            
| VExprEq (e e' : expr):
    forall (v v' : value) (b : bool),

      (* Premises *)
      vexpr denv dstate lenv e v ->
      vexpr denv dstate lenv e' v' ->
      veq v v' = Some b ->
      
      (* Conclusion *)      
      vexpr denv dstate lenv (e_binop bo_eq e e') (Vbool b)

(** Evaluates expression with difference operator. *)

| VExprNEq (e e' : expr):
    forall (b : bool),

      (* Premises *)
      vexpr denv dstate lenv (e_binop bo_eq e e') (Vbool b) ->
      
      (* Conclusion *)      
      vexpr denv dstate lenv (e_binop bo_neq e e') (Vbool (negb b))
    
(** Defines the evaluation relation for lists of expressions.  *)
            
with vlofexprs (denv : DEnv) (dstate : DState) (lenv : LEnv) :
  list expr -> lofvalues -> Prop :=
| VLOfExprsNil : vlofexprs denv dstate lenv [] Vnil
| VLOfExprsCons :
    forall {lofexprs lofvalues e v},
      vlofexprs denv dstate lenv lofexprs lofvalues ->
      vexpr denv dstate lenv e v ->
      vlofexprs denv dstate lenv (e :: lofexprs) (Vcons v lofvalues).
                          
