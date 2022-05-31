(** * H-VHDL expression evaluation *)

(** Module that implement the relation evaluating H-VHDL
    expressions. *)

Require Import common.CoqLib.
Require Import common.ListPlus.
Require Import common.GlobalTypes.

Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.Environment.
Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.HVhdlTypes.

Import NatMap.
Open Scope abss_scope.
Open Scope N_scope.

(** ** Expression evaluation relation *)

(** Defines the expression evaluation relation. 
    
    The environment is composed of:
    - [Δ], the elaborated design (Δ).
    - [sst], the signal store.
    - [Λ], a local environment (process environment).
    - [outmode], [true] when output port identifiers
      are allowed to be read (which normally is not the case since
      output ports are write-only signals).
    
 *)

Inductive VExpr (Δ : ElDesign) (sst : IdMap value) (Λ : LEnv) :
  bool -> expr -> value -> Prop :=

(** Evaluates nat constant. *) 
| VExprNat (outmode : bool) (n : N) : (n <= NATMAX)%N -> VExpr Δ sst Λ outmode (e_nat n) (Vnat n) 

(** Evaluates bool constant. *)
| VExprBool (outmode : bool) (b : bool) : VExpr Δ sst Λ outmode (e_bool b) (Vbool b)
                                         
(** Evaluates aggregate expression.
    
    The aggregate of expressions [agofe] and the array of values
    [arrofvalues] in parameter must be of the same length. *)
| VExprAggreg (outmode : bool) (agofe : agofexprs) (arrofv : arrofvalues) :
    VAgOfExprs Δ sst Λ outmode agofe arrofv ->
    VExpr Δ sst Λ outmode (e_aggreg agofe) (Varr arrofv)

(** Evaluates a declared signal identifier . *)
          
| VExprSig (outmode : bool) (id : ident) (t : type) (v : value) :
    (MapsTo id (Internal t) Δ \/ MapsTo id (Input t) Δ) -> (* id ∈ Sigs(Δ) ∪ Ins(Δ) and Δ(id) = t *)
    ~NatMap.In id Λ ->                                     (* id ∉ Λ *)
    MapsTo id v sst ->   (* id ∈ sst and sst(id) = v *)
    VExpr Δ sst Λ outmode (#id) v

(** Evaluates a simple out port identifier. 
    Only possible when outmode is true.
 *)
  
| VExprOut (id : ident) (t : type) (v : value) :

    (* * Side conditions * *)
    MapsTo id (Output t) Δ ->   (* id ∈ Outs(Δ) and Δ(id) = t *)
    ~NatMap.In id Λ ->          (* id ∉ Λ *)
    MapsTo id v sst -> (* id ∈ sst and sst(id) = v *)
      
    (* * Conclusion * *)
    VExpr Δ sst Λ true (#id) v
            
(** Evaluates a variable identifier. *)
            
| VExprVar (outmode : bool) (id : ident) (t : type) (v : value) :
    MapsTo id (t, v) Λ ->      (* id ∈ Λ and Λ(id) = (t,v) *)
    ~NatMap.In id Δ ->         (* id ∉ Δ *)
    VExpr Δ sst Λ outmode (#id) v
          
(** Evaluates a generic constant identifier. *)
          
| VExprGen (outmode : bool) (id : ident) (t : type) (v : value) :
    MapsTo id (Generic t v) Δ -> (* id ∈ Gens(Δ) and Δ(id) = (t,v) *)
    ~NatMap.In id Λ ->           (* id ∉ Λ *)
    VExpr Δ sst Λ outmode (#id) v

(** Evaluates an indexed out port identifier. *)
  
| VExprIdxOut (id : ident) (ei : expr):

  forall (t : type) (i l u : N) (v : value) (aofv : arrofvalues),
    let idx := (N.to_nat (i - l)) in 
    forall (idx_in_bounds : (idx < length aofv)%nat),

    (* Premises *)
    VExpr Δ sst Λ true ei (Vnat i) -> (* index expression [ei] evaluates to [i] *)
    IsOfType (Vnat i) (Tnat l u) ->
    
    (* Side conditions *)

    (* id ∈ Outs(Δ) and Δ(id) = array(t, l, u) *)
    (MapsTo id (Output (Tarray t l u)) Δ) ->
    ~NatMap.In id Λ ->                       (* id ∉ Λ *)
    MapsTo id (Varr aofv) sst ->    (* id ∈ sst and sst(id) = aofv *)

    (* Conclusion *)
    VExpr Δ sst Λ true (id [[ei]]) (get_at idx aofv idx_in_bounds)

(** Evaluates an indexed declared signal identifier. *)
          
| VExprIdxSig (outmode : bool) (id : ident) (ei : expr):
  forall (t : type) (i l u : N) (v : value) (aofv : arrofvalues),
    let idx := (N.to_nat (i - l)) in
    forall (idx_in_bounds : (idx < (length aofv))%nat),

      (* Premises *)
      VExpr Δ sst Λ outmode ei (Vnat i) -> (* index expression [ei] evaluates to [i] *)
      IsOfType (Vnat i) (Tnat l u) ->
      
      (* Side conditions *)

      (* id ∈ Sigs(Δ) ∪ Ins(Δ) and Δ(id) = array(t, l, u) *)
      (MapsTo id (Internal (Tarray t l u)) Δ \/ MapsTo id (Input (Tarray t l u)) Δ) ->
      ~NatMap.In id Λ ->                    (* id ∉ Λ *)
      MapsTo id (Varr aofv) sst -> (* id ∈ sst and sst(id) = aofv *)

      (* Conclusion *)
      VExpr Δ sst Λ outmode (id [[ei]]) (get_at idx aofv idx_in_bounds)

(** Evaluates an indexed variable identifier. *)

| VExprIdxVar (outmode : bool) (id : ident) (ei : expr):
  forall (t : type) (i l u : N) (v : value) (aofv : arrofvalues),
    let idx := N.to_nat (i - l) in
    forall (idx_in_bounds : (idx < length aofv)%nat),

      (* Premises *)
      VExpr Δ sst Λ outmode ei (Vnat i) ->  (* index expression [ei] evaluates to [i] *)
      IsOfType (Vnat i) (Tnat l u) ->   (* index value is in array bounds. *)
      
      (* Side conditions *)
      MapsTo id ((Tarray t l u), (Varr aofv)) Λ -> (* id ∈ Λ(Δ) and Λ(id) = (array(t, l, u), lofvalues) *)
      ~NatMap.In id Δ ->                           (* id ∉ Δ *)
      
      (* Conclusion *)      
      VExpr Δ sst Λ outmode (id [[ei]]) (get_at idx aofv idx_in_bounds)

(** Evaluates expression with addition operator. 
    
    The "nat overflow check" (i.e, v + v' <= NATMAX)
    is done in the [vadd] function.
 *)

| VExprAdd (outmode : bool) (e e' : expr):
    forall (n n' : N),

      (* Premises:
         - Checks that operands evaluate to nat.
         - Checks that the addition does not cause nat overflow.
       *)
      VExpr Δ sst Λ outmode e (Vnat n) -> 
      VExpr Δ sst Λ outmode e' (Vnat n') ->
      n + n' <= NATMAX ->
      
      (* Conclusion *)      
      VExpr Δ sst Λ outmode (e_binop bo_add e e') (Vnat (n + n'))

(** Evaluates expression with substraction operator. 
    
    The "out of natural scope" check (i.e, v <= v') 
    is done in the [vsub] function.
 *)

| VExprSub (outmode : bool) (e e' : expr):
    forall (n n' : N),

      (* Premises:
         - Checks that operands evaluate to nat.     
         - Checks that the substraction does not go out of
           nat scope.
       *)
      VExpr Δ sst Λ outmode e (Vnat n) ->
      VExpr Δ sst Λ outmode e' (Vnat n') ->
      n' <= n ->
      
      (* Conclusion *)      
      VExpr Δ sst Λ outmode (e_binop bo_sub e e') (Vnat (n - n'))

(** Evaluates expression with the "less or equal" operator. *)

| VExprLE (outmode : bool) (e e' : expr):
    forall (n n' : N),

      (* Premises: checks that operands evaluate to nat. *)
      VExpr Δ sst Λ outmode e (Vnat n) -> 
      VExpr Δ sst Λ outmode e' (Vnat n') ->
      
      (* Conclusion *)      
      VExpr Δ sst Λ outmode (e_binop bo_le e e') (Vbool (n <=? n'))

(** Evaluates expression with the "strictly less" operator. *)

| VExprLT (outmode : bool) (e e' : expr):
    forall (n n' : N),

      (* Premises: checks that operands evaluate to nat. *)
      VExpr Δ sst Λ outmode e (Vnat n) -> 
      VExpr Δ sst Λ outmode e' (Vnat n') ->
        
      (* Conclusion *)      
      VExpr Δ sst Λ outmode (e_binop bo_lt e e') (Vbool (n <? n'))

(** Evaluates expression with the "greater or equal" operator. *)

| VExprGE (outmode : bool) (e e' : expr):
    forall (n n' : N),

      (* Premises: checks that operands evaluate to nat. *)
      VExpr Δ sst Λ outmode e (Vnat n) -> 
      VExpr Δ sst Λ outmode e' (Vnat n') ->
      
      (* Conclusion *)      
      VExpr Δ sst Λ outmode (e_binop bo_ge e e') (Vbool (n' <=? n))

(** Evaluates expression with the "strictly greater" operator. *)

| VExprGT (outmode : bool) (e e' : expr):
    forall (n n' : N),

      (* Premises: checks that operands evaluate to nat. *)
      VExpr Δ sst Λ outmode e (Vnat n) -> 
      VExpr Δ sst Λ outmode e' (Vnat n') ->
      
      (* Conclusion *)      
      VExpr Δ sst Λ outmode (e_binop bo_gt e e') (Vbool (n' <? n))

(** Evaluates expression with the "and" operator. *)

| VExprAnd (outmode : bool) (e e' : expr):
    forall (b b' : bool),

      (* Premises: checks that the operands evaluate to bool. *)
      VExpr Δ sst Λ outmode e (Vbool b) -> 
      VExpr Δ sst Λ outmode e' (Vbool b') ->
            
      (* Conclusion *)      
      VExpr Δ sst Λ outmode (e_binop bo_and e e') (Vbool (b && b'))

(** Evaluates expression with the or operator. *)

| VExprOr (outmode : bool) (e e' : expr):
    forall (b b' : bool),

      (* Premises: checks that the operands evaluate to bool. *)
      VExpr Δ sst Λ outmode e (Vbool b) ->
      VExpr Δ sst Λ outmode e' (Vbool b') ->
      
      (* Conclusion *)      
      VExpr Δ sst Λ outmode (e_binop bo_or e e') (Vbool (b || b'))

(** Evaluates expression with the not operator. *)

| VExprNot (outmode : bool) (e : expr):
    forall (b : bool),

      (* Premises: checks that the operand evaluates to bool. *)
      VExpr Δ sst Λ outmode e (Vbool b) ->
            
      (* Conclusion. *)
      VExpr Δ sst Λ outmode (e_uop uo_not e) (Vbool (negb b))
            
(** Evaluates expression with the equality operator (bool). *)
            
| VExprEq_true (outmode : bool) (e e' : expr):
    forall (v v' : value) (b : bool),

      (* Premises *)
      VExpr Δ sst Λ outmode e v ->
      VExpr Δ sst Λ outmode e' v' ->
      VEq v v' ->
      
      (* Conclusion: Δ,sst,Λ ⊢ e = e' ⇝ b *)      
      VExpr Δ sst Λ outmode (e_binop bo_eq e e') (Vbool true)

| VExprEq_false (outmode : bool) (e e' : expr):
    forall (v v' : value) (b : bool),

      (* Premises *)
      VExpr Δ sst Λ outmode e v ->
      VExpr Δ sst Λ outmode e' v' ->
      OVEq v v' (Some false) ->
      
      (* Conclusion: Δ,sst,Λ ⊢ e = e' ⇝ b *)      
      VExpr Δ sst Λ outmode (e_binop bo_eq e e') (Vbool false)

(** Evaluates expression with difference operator. *)

| VExprNEq (outmode : bool) (e e' : expr):
    forall (b : bool),

      (* Premises *)
      VExpr Δ sst Λ outmode (e_binop bo_eq e e') (Vbool b) ->
      
      (* Conclusion *)      
      VExpr Δ sst Λ outmode (e_binop bo_neq e e') (Vbool (negb b))
    
(** Defines the evaluation relation for aggregates of expressions.  *)
            
with VAgOfExprs (Δ : ElDesign) (sst : IdMap value) (Λ : LEnv) :
  bool -> agofexprs -> arrofvalues -> Prop :=
| VAgOfExprs_one :
    forall outmode e v,
      VExpr Δ sst Λ outmode e v ->
      VAgOfExprs Δ sst Λ outmode (agofe_one e) (Arr_one v) 
| VAgOfExprs_cons :
    forall outmode agofe arrofv e v,
      VExpr Δ sst Λ outmode e v ->
      VAgOfExprs Δ sst Λ outmode agofe arrofv ->
      VAgOfExprs Δ sst Λ outmode (agofe_cons e agofe) (Arr_cons v arrofv).

#[export] Hint Constructors VExpr : hvhdl.
#[export] Hint Constructors VAgOfExprs : hvhdl.

Scheme VExpr_ind_mut := Induction for VExpr Sort Prop
  with VAgOfExprs_ind_mut := Induction for VAgOfExprs Sort Prop.

(** ** H-VHDL expression interpret *)

Require Import String.
Import ErrMonadNotations.

(** Interprets the application of the binary operator [bop] to the
    values [v1] and [v2]. *)

Definition vbinop (bop : binop) (v1 v2 : value) : optionE value :=
  match bop, v1, v2 with
  (** Evaluates Boolean operators: "and" and "or".  *)
  | bo_and, (Vbool b1), (Vbool b2) => Ret (Vbool (b1 && b2))
  | bo_or, (Vbool b1), (Vbool b2) => Ret (Vbool (b1 || b2))
  (** Evaluates natural number arithmetic operators: addition and substraction. *)
  | bo_add, (Vnat n1), (Vnat n2) =>
      let n := n1 + n2 in
      if N_le_dec n NATMAX then Ret (Vnat n)
      else Err "vbinop: addition of natural numbers causes an overflow"
  | bo_sub, (Vnat n1), (Vnat n2) =>
      if N_le_dec n2 n1 then Ret (Vnat (n1 - n2))
      else Err "vbinop: result substraction is below zero"
  (** Evaluates comparisons operations: eq, ne, gt, ge, lt, le *)
  | bo_eq, _, _ => do b <- veq v1 v2; Ret (Vbool b)
  | bo_neq, _, _ => do b <- veq v1 v2; Ret (Vbool (negb b))
  | bo_gt, (Vnat n1), (Vnat n2) => Ret (Vbool (n2 <? n1))
  | bo_ge, (Vnat n1), (Vnat n2) => Ret (Vbool (n2 <=? n1))
  | bo_lt, (Vnat n1), (Vnat n2) => Ret (Vbool (n1 <? n2))
  | bo_le, (Vnat n1), (Vnat n2) => Ret (Vbool (n1 <=? n2))
  | _, _, _ => Err "vbinop: found incompatible binary operator and operands"
  end.

(** Returns the value associated with identifier [id] in the
    environment composed of an elaborated design [Δ], a signal store
    [sst] and a local environment [Λ].

    [id] must either refer to a local variable identifier, a signal
    identifier (possibly an output port if [outmode] is on), or a
    generic constant identifier.

    An error is returned if [id] is not referenced at all in the
    environment, if it identifies another kind of construct than those
    cited above (e.g. [id] refers to a component instance identifier),
    or if the environment is inconsistent (e.g. [id] refers to both a
    local variable and an internal signal). *)

Definition read (Δ : ElDesign) (sst : IdMap value) (Λ : LEnv) (outmode : bool)
           (id : ident) : optionE value :=
  match find id Λ, find id sst, find id Δ with
  (* [id] is a local variable identifier *)
  | Some (_, v), None, None => Ret v
  (* [id] is a input port or an declared signal identifier. *)
  | None, Some v, Some (Input _ | Internal _) => Ret v
  (* [id] is an output signal identifier, checks that [outmode]
     is on to return the associated value; error otherwise. *)
  | None, Some v, Some (Output _) =>
      if outmode then Ret v
      else Err "read: trying to read an output signal identifier with outmode off"
  | None, None, Some (Component _) =>
      Err "read: trying to read a component instance identifier"
  | None, None, Some (Process _) =>
      Err "read: trying to read a process identifier"
  (* Error: id is not referenced in Δ, σ or Λ *)
  | None, None, None => Err "read: found an unknown identifier"
  (* Error: inconsistent environment *)
  | _, _, _ => Err "read: found an inconsistent environment"
  end.

(** Returns the value read at the index [v__i] in the array [v__a], where
    [v__a] must be a value of the array type, and [v__i] must be a value
    of the nat type, and [v__i] must correspond to a index within the
    bounds of [v__a]. Otherwise an error is raised. *)

Definition read_at (v__a v__i : value) : optionE value :=
  match v__a with
  | Varr aofv => 
      match v__i with
      | Vnat i =>
          match lt_dec (N.to_nat i) (List.length aofv) with
          | left lt_i_lgth => Ret (get_at (N.to_nat i) aofv lt_i_lgth)
          | _ => Err "read_at: index out of bounds"
          end
      | _ =>   Err "read_at: index value is not a natural number"
      end
  | _ => Err "read_at: first value is not of the array type"
  end.

(** Defines a interpret for H-VHDL expressions. *)

Fixpoint vexpr (Δ : ElDesign) (sst : IdMap value) (Λ : LEnv) (outmode : bool)
         (e : expr) {struct e} : optionE value :=
  match e with
  (** Evaluates nat constant. *) 
  | e_nat n => if N_le_dec n NATMAX then Ret (Vnat n) else Err "vexpr: found a natural number greater than NATMAX"
  (** Evaluates bool constant. *)
  | e_bool b => Ret (Vbool b)
  (** Evaluates aggregate expression. *)
  | e_aggreg agofe => do aofv <- vagofexprs Δ sst Λ outmode agofe; Ret (Varr aofv)
  (** Evaluates binary operation *)
  | e_binop bop e1 e2 =>
      do v1 <- vexpr Δ sst Λ outmode e1;
      do v2 <- vexpr Δ sst Λ outmode e2;
      vbinop bop v1 v2
  (** Evaluates Boolean negation operation *)
  | e_uop uo_not e1 =>
      do v1 <- vexpr Δ sst Λ outmode e1;
      match v1 with
      | Vbool b => Ret (Vbool (negb b))
      | _ => Err "vexpr: negation must be applied to a Boolean expression"
      end
        
  (** Evaluates a name that can refer to a generic constant, a signal
      or a local variable identifier, possibly indexed, in the context
      [Δ, sst, Λ], and given a certain [outmode] flag. *)
  | e_name n => vname Δ sst Λ outmode n
  end

with vname (Δ : ElDesign) (sst : IdMap value) (Λ : LEnv) (outmode : bool)
           (n : name) {struct n} : optionE value :=
       match n with
       (** Reads the value associated with the identifier [id]. *)
       | n_id id => do v <- read Δ sst Λ outmode id; Ret v
       (** Reads the value of array [v__a] at index [v__i] *)
       | n_xid id e =>
           do v__i <- vexpr Δ sst Λ outmode e;
           do v__a <- read Δ sst Λ outmode id;
           read_at v__a v__i
       end

with vagofexprs (Δ : ElDesign) (sst : IdMap value) (Λ : LEnv) (outmode : bool)
                (agofe : agofexprs) {struct agofe} : optionE arrofvalues :=
       match agofe with
       | agofe_one e => do v <- vexpr Δ sst Λ outmode e; Ret (Arr_one v)
       | _ => Ret (Arr_one (Vnat 0))
       end.

