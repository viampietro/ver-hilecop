(** Module that implement the relation evaluating H-VHDL
    expressions. *)

Require Import CoqLib.
Require Import ListPlus.
Require Import GlobalTypes.
Require Import AbstractSyntax.
Require Import Environment.
Require Import SemanticalDomains.
Require Import HVhdlTypes.

Import NatMap.
Open Scope abss_scope.
Local Open Scope nat_scope.

(** Defines the expression evaluation relation. 
    
    The environment is composed of:
    - [Δ], the design environment (Δ).
    - [σ], the design state.
    - [Λ], a local environment (process environment).
    - [outmode], [true] when output port identifiers
      are allowed to be read (which normally is not the case since
      output ports are write-only signals).
    
 *)

Inductive vexpr (Δ : ElDesign) (σ : DState) (Λ : LEnv) :
  bool -> expr -> value -> Prop :=

(** Evaluates nat constant. *) 
| VExprNat (outmode : bool) (n : nat) : n <= NATMAX -> vexpr Δ σ Λ outmode (e_nat n) (Vnat n) 

(** Evaluates bool constant. *)
| VExprBool (outmode : bool) (b : bool) : vexpr Δ σ Λ outmode (e_bool b) (Vbool b)
                                         
(** Evaluates aggregate expression.
    
    The list of expressions [lofexprs] and the list of values
    [lofvalues] in parameter must be of the same length. *)
| VExprAggreg (outmode : bool) (agofe : agofexprs) (arrofv : arrofvalues) :
    vagofexprs Δ σ Λ outmode agofe arrofv ->
    vexpr Δ σ Λ outmode (e_aggreg agofe) (Varr arrofv)

(** Evaluates a declared signal identifier . *)
          
| VExprSig (outmode : bool) (id : ident) (t : type) (v : value) :
    (MapsTo id (Declared t) Δ \/ MapsTo id (Input t) Δ) -> (* id ∈ Sigs(Δ) ∪ Ins(Δ) and Δ(id) = t *)
    ~NatMap.In id Λ ->                                     (* id ∉ Λ *)
    MapsTo id v (sigstore σ) ->   (* id ∈ σ and σ(id) = v *)
    vexpr Δ σ Λ outmode (#id) v

(** Evaluates a simple out port identifier. 
    Only possible when outmode is true.
 *)
  
| VExprOut (id : ident) (t : type) (v : value) :

    (* * Side conditions * *)
    MapsTo id (Output t) Δ ->   (* id ∈ Outs(Δ) and Δ(id) = t *)
    ~NatMap.In id Λ ->          (* id ∉ Λ *)
    MapsTo id v (sigstore σ) -> (* id ∈ σ and σ(id) = v *)
      
    (* * Conclusion * *)
    vexpr Δ σ Λ true (#id) v
            
(** Evaluates a variable identifier. *)
            
| VExprVar (outmode : bool) (id : ident) (t : type) (v : value) :
    MapsTo id (t, v) Λ ->      (* id ∈ Λ and Λ(id) = (t,v) *)
    ~NatMap.In id Δ ->         (* id ∉ Δ *)
    vexpr Δ σ Λ outmode (#id) v
          
(** Evaluates a generic constant identifier. *)
          
| VExprGen (outmode : bool) (id : ident) (t : type) (v : value) :
    MapsTo id (Generic t v) Δ -> (* id ∈ Gens(Δ) and Δ(id) = (t,v) *)
    ~NatMap.In id Λ ->           (* id ∉ Λ *)
    vexpr Δ σ Λ outmode (#id) v

(** Evaluates an indexed out port identifier. *)
  
| VExprIdxOut (id : ident) (ei : expr):
    forall (t : type) (i l u : nat) (v : value) (aofv : arrofvalues)
           (idx_in_bounds : i - l < length aofv),

      (* Premises *)
      vexpr Δ σ Λ true ei (Vnat i) -> (* index expression [ei] evaluates to [i] *)
      is_of_type (Vnat i) (Tnat l u) ->
      
      (* Side conditions *)

      (* id ∈ Outs(Δ) and Δ(id) = array(t, l, u) *)
      (MapsTo id (Output (Tarray t l u)) Δ) ->
      ~NatMap.In id Λ ->                       (* id ∉ Λ *)
      MapsTo id (Varr aofv) (sigstore σ) ->    (* id ∈ σ and σ(id) = aofv *)

      (* Conclusion *)
      vexpr Δ σ Λ true (id [[ei]]) (get_at (i - l) aofv idx_in_bounds)

(** Evaluates an indexed declared signal identifier. *)
          
| VExprIdxSig (outmode : bool) (id : ident) (ei : expr):
    forall (t : type) (i l u : nat) (v : value) (aofv : arrofvalues)
           (idx_in_bounds : i - l < length aofv),

      (* Premises *)
      vexpr Δ σ Λ outmode ei (Vnat i) -> (* index expression [ei] evaluates to [i] *)
      is_of_type (Vnat i) (Tnat l u) ->
      
      (* Side conditions *)

      (* id ∈ Sigs(Δ) ∪ Ins(Δ) and Δ(id) = array(t, l, u) *)
      (MapsTo id (Declared (Tarray t l u)) Δ \/ MapsTo id (Input (Tarray t l u)) Δ) ->
      ~NatMap.In id Λ ->                    (* id ∉ Λ *)
      MapsTo id (Varr aofv) (sigstore σ) -> (* id ∈ σ and σ(id) = aofv *)

      (* Conclusion *)
      vexpr Δ σ Λ outmode (id [[ei]]) (get_at (i - l) aofv idx_in_bounds)

(** Evaluates an indexed variable identifier. *)

| VExprIdxVar (outmode : bool) (id : ident) (ei : expr):
    forall (t : type) (i l u : nat) (v : value) (aofv : arrofvalues)
           (idx_in_bounds : i - l < length aofv),

      (* Premises *)
      vexpr Δ σ Λ outmode ei (Vnat i) ->  (* index expression [ei] evaluates to [i] *)
      is_of_type (Vnat i) (Tnat l u) ->   (* index value is in array bounds. *)
      
      (* Side conditions *)
      MapsTo id ((Tarray t l u), (Varr aofv)) Λ -> (* id ∈ Λ(Δ) and Λ(id) = (array(t, l, u), lofvalues) *)
      ~NatMap.In id Δ ->                           (* id ∉ Δ *)
      
      (* Conclusion *)      
      vexpr Δ σ Λ outmode (id [[ei]]) (get_at (i - l) aofv idx_in_bounds)

(** Evaluates expression with addition operator. 
    
    The "nat overflow check" (i.e, v + v' <= NATMAX)
    is done in the [vadd] function.
 *)

| VExprAdd (outmode : bool) (e e' : expr):
    forall (n n' : nat),

      (* Premises:
         - Checks that operands evaluate to nat.
         - Checks that the addition does not cause nat overflow.
       *)
      vexpr Δ σ Λ outmode e (Vnat n) -> 
      vexpr Δ σ Λ outmode e' (Vnat n') ->
      n + n' <= NATMAX ->
      
      (* Conclusion *)      
      vexpr Δ σ Λ outmode (e_binop bo_add e e') (Vnat (n + n'))

(** Evaluates expression with substraction operator. 
    
    The "out of natural scope" check (i.e, v <= v') 
    is done in the [vsub] function.
 *)

| VExprSub (outmode : bool) (e e' : expr):
    forall (n n' : nat),

      (* Premises:
         - Checks that operands evaluate to nat.     
         - Checks that the substraction does not go out of
           nat scope.
       *)
      vexpr Δ σ Λ outmode e (Vnat n) ->
      vexpr Δ σ Λ outmode e' (Vnat n') ->
      n' <= n ->
      
      (* Conclusion *)      
      vexpr Δ σ Λ outmode (e_binop bo_sub e e') (Vnat (n - n'))

(** Evaluates expression with the "less or equal" operator. *)

| VExprLE (outmode : bool) (e e' : expr):
    forall (n n' : nat),

      (* Premises: checks that operands evaluate to nat. *)
      vexpr Δ σ Λ outmode e (Vnat n) -> 
      vexpr Δ σ Λ outmode e' (Vnat n') ->
      
      (* Conclusion *)      
      vexpr Δ σ Λ outmode (e_binop bo_le e e') (Vbool (n <=? n'))

(** Evaluates expression with the "strictly less" operator. *)

| VExprLT (outmode : bool) (e e' : expr):
    forall (n n' : nat),

      (* Premises: checks that operands evaluate to nat. *)
      vexpr Δ σ Λ outmode e (Vnat n) -> 
      vexpr Δ σ Λ outmode e' (Vnat n') ->
        
      (* Conclusion *)      
      vexpr Δ σ Λ outmode (e_binop bo_lt e e') (Vbool (n <? n'))

(** Evaluates expression with the "greater or equal" operator. *)

| VExprGE (outmode : bool) (e e' : expr):
    forall (n n' : nat),

      (* Premises: checks that operands evaluate to nat. *)
      vexpr Δ σ Λ outmode e (Vnat n) -> 
      vexpr Δ σ Λ outmode e' (Vnat n') ->
      
      (* Conclusion *)      
      vexpr Δ σ Λ outmode (e_binop bo_ge e e') (Vbool (n' <=? n))

(** Evaluates expression with the "strictly greater" operator. *)

| VExprGT (outmode : bool) (e e' : expr):
    forall (n n' : nat),

      (* Premises: checks that operands evaluate to nat. *)
      vexpr Δ σ Λ outmode e (Vnat n) -> 
      vexpr Δ σ Λ outmode e' (Vnat n') ->
      
      (* Conclusion *)      
      vexpr Δ σ Λ outmode (e_binop bo_gt e e') (Vbool (n' <? n))

(** Evaluates expression with the "and" operator. *)

| VExprAnd (outmode : bool) (e e' : expr):
    forall (b b' : bool),

      (* Premises: checks that the operands evaluate to bool. *)
      vexpr Δ σ Λ outmode e (Vbool b) -> 
      vexpr Δ σ Λ outmode e' (Vbool b') ->
            
      (* Conclusion *)      
      vexpr Δ σ Λ outmode (e_binop bo_and e e') (Vbool (b && b'))

(** Evaluates expression with the or operator. *)

| VExprOr (outmode : bool) (e e' : expr):
    forall (b b' : bool),

      (* Premises: checks that the operands evaluate to bool. *)
      vexpr Δ σ Λ outmode e (Vbool b) ->
      vexpr Δ σ Λ outmode e' (Vbool b') ->
      
      (* Conclusion *)      
      vexpr Δ σ Λ outmode (e_binop bo_or e e') (Vbool (b || b'))

(** Evaluates expression with the not operator. *)

| VExprNot (outmode : bool) (e : expr):
    forall (b : bool),

      (* Premises: checks that the operand evaluates to bool. *)
      vexpr Δ σ Λ outmode e (Vbool b) ->
            
      (* Conclusion. *)
      vexpr Δ σ Λ outmode (e_not e) (Vbool (negb b))
            
(** Evaluates expression with the equality operator (bool). *)
            
| VExprEq_true (outmode : bool) (e e' : expr):
    forall (v v' : value) (b : bool),

      (* Premises *)
      vexpr Δ σ Λ outmode e v ->
      vexpr Δ σ Λ outmode e' v' ->
      VEq v v' ->
      
      (* Conclusion: Δ,σ,Λ ⊢ e = e' ⇝ b *)      
      vexpr Δ σ Λ outmode (e_binop bo_eq e e') (Vbool true)

| VExprEq_false (outmode : bool) (e e' : expr):
    forall (v v' : value) (b : bool),

      (* Premises *)
      vexpr Δ σ Λ outmode e v ->
      vexpr Δ σ Λ outmode e' v' ->
      ~VEq v v' ->
      
      (* Conclusion: Δ,σ,Λ ⊢ e = e' ⇝ b *)      
      vexpr Δ σ Λ outmode (e_binop bo_eq e e') (Vbool false)

(** Evaluates expression with difference operator. *)

| VExprNEq (outmode : bool) (e e' : expr):
    forall (b : bool),

      (* Premises *)
      vexpr Δ σ Λ outmode (e_binop bo_eq e e') (Vbool b) ->
      
      (* Conclusion *)      
      vexpr Δ σ Λ outmode (e_binop bo_neq e e') (Vbool (negb b))
    
(** Defines the evaluation relation for aggregates of expressions.  *)
            
with vagofexprs (Δ : ElDesign) (σ : DState) (Λ : LEnv) :
  bool -> agofexprs -> arrofvalues -> Prop :=
| VAgOfExprs_one :
    forall outmode e v,
      vexpr Δ σ Λ outmode e v ->
      vagofexprs Δ σ Λ outmode (agofe_one e) (Arr_one v) 
| VAgOfExprs_cons :
    forall outmode agofe arrofv e v,
      vexpr Δ σ Λ outmode e v ->
      vagofexprs Δ σ Λ outmode agofe arrofv ->
      vagofexprs Δ σ Λ outmode (agofe_cons e agofe) (Arr_cons v arrofv).

Hint Constructors vexpr : hvhdl.
Hint Constructors vagofexprs : hvhdl.

Scheme vexpr_ind_mut := Induction for vexpr Sort Prop
  with vagofexprs_ind_mut := Induction for vagofexprs Sort Prop.

