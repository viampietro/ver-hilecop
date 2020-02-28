(** Module that implement the relation evaluating H-VHDL
    expressions. *)

Require Import Coqlib.
Require Import ListsPlus.
Require Import Arrays.
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

Inductive vexpr (denv : DEnv) (dstate : DState) (lenv : IdMap (type * value)) :
  expr -> option value -> Prop :=

(** Evaluates nat constant. *) 
| VExprNat (n : nat) : n <= NATMAX -> vexpr denv dstate lenv (e_nat n) (Some (Vnat n))

(** Evaluates bool constant. *)
| VExprBool (b : bool) : vexpr denv dstate lenv (e_bool b) (Some (Vbool b))

(** Evaluates arc_t constant. *)
| VExprArcT (a : arc_t) : vexpr denv dstate lenv (e_arc a) (Some (Varc a))

(** Evaluates arc_t constant. *)
| VExprTransT (t : transition_t) : vexpr denv dstate lenv (e_trans t) (Some (Vtransition t))
                                         
(** Evaluates aggregate expression.
    
    The list of expressions [lofexprs] and the list of values
    [lofvalues] in parameter must be of the same length. *)
| VExprAggreg (lofexprs : list expr) (lofvalues : list value) :
    vlofexprs denv dstate lenv lofexprs (Some lofvalues) ->
    vexpr denv dstate lenv (e_aggreg lofexprs) (Some (Vlist lofvalues))

(** Evaluates a declared signal identifier . *)
          
| VExprSig (id : ident) (v : value) :
    forall (t : type),
      MapsTo id (Declared t) denv ->   (* id ∈ Sigs(Δ) and Δ(id) = t *)
      MapsTo id v (sigstore dstate) -> (* id ∈ σ and σ(id) = v *)
      vexpr denv dstate lenv (e_name (n_id id)) (Some v)

(** Evaluates an input signal identifier. *)

| VExprIn (id : ident) (v : value) :
    forall (t : type),
      MapsTo id (Input t) denv ->      (* id ∈ In(Δ) and Δ(id) = t *)
      MapsTo id v (sigstore dstate) -> (* id ∈ σ and σ(id) = v *)
      vexpr denv dstate lenv (e_name (n_id id)) (Some v)

(** Evaluates a variable identifier. *)
            
| VExprVar (id : ident) (t : type) (v : value) :
    MapsTo id (t, v) lenv ->      (* id ∈ Λ and Λ(id) = (t,v) *)
    vexpr denv dstate lenv (e_name (n_id id)) (Some v)
          
(** Evaluates a constant identifier. *)
          
| VExprConst (id : ident) (t : type) (v : value) :
    MapsTo id (Constant t v) denv ->      (* id ∈ Consts(Δ) and Δ(id) = (t,v) *)
    vexpr denv dstate lenv (e_name (n_id id)) (Some v)

(** Evaluates a constant identifier. *)
          
| VExprGen (id : ident) (t : type) (v : value) :
    MapsTo id (Generic t v) denv ->      (* id ∈ Gens(Δ) and Δ(id) = (t,v) *)
    vexpr denv dstate lenv (e_name (n_id id)) (Some v)

| VExprIdxSig (id : ident) (ei : expr) (v : value):
    forall (t : type) (i l u : nat) (lofvalues : list value),

      (* Premises *)
      vexpr denv dstate lenv ei (Some (Vnat i)) -> (* index expression [ei] evaluates to [i] *)
      is_of_type (Vnat i) (Tnat l u) ->
      
      (* Side conditions *)
      MapsTo id (Declared (Tarray t l u)) denv ->      (* id ∈ Sigs(Δ) and Δ(id) = array(t, l, u) *)
      MapsTo id (Vlist lofvalues) (sigstore dstate) -> (* id ∈ σ and σ(id) = lofvalues *)
      
      (* Conclusion *)
      
      vexpr denv dstate lenv (e_name (n_xid id ei)) (get_at (i - l) lofvalues)

| VExprIdxIn (id : ident) (ei : expr) (v : value):
    forall (t : type) (i l u : nat) (lofvalues : list value),

      (* Premises *)
      vexpr denv dstate lenv ei (Some (Vnat i)) -> (* index expression [ei] evaluates to [i] *)
      is_of_type (Vnat i) (Tnat l u) ->
      
      (* Side conditions *)
      MapsTo id (Input (Tarray t l u)) denv ->         (* id ∈ Ins(Δ) and Δ(id) = array(t, l, u) *)
      MapsTo id (Vlist lofvalues) (sigstore dstate) -> (* id ∈ σ and σ(id) = lofvalues *)
      
      (* Conclusion *)
      
      vexpr denv dstate lenv (e_name (n_xid id ei)) (get_at (i - l) lofvalues)

(** Defines the evaluation relation for lists of expressions.  *)
            
with vlofexprs (denv : DEnv) (dstate : DState) (lenv : IdMap (type * value)) :
  list expr -> option (list value) -> Prop :=
| VLOfExprsNil : vlofexprs denv dstate lenv [] (Some [])
| VLOfExprsCons :
    forall {lofexprs lofvalues e v},
      vlofexprs denv dstate lenv lofexprs (Some lofvalues) ->
      vexpr denv dstate lenv e (Some v) ->
      vlofexprs denv dstate lenv (e :: lofexprs) (Some (v :: lofvalues)).
                          