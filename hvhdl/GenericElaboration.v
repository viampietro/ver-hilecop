(** Defines the relation that elaborates the generic clause of a
    design, as declared in abstract syntax.
    
    The result is the addition of entries refering to generic constant
    declarations in the design environment.  *)

Require Import common.CoqLib.
Require Import common.GlobalTypes.

Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.Environment.
Require Import hvhdl.ExpressionEvaluation.
Require Import hvhdl.StaticExpressions.
Require Import hvhdl.TypeElaboration.
Require Import hvhdl.HVhdlTypes.

Import NatMap.

(** The generic constant elaboration relation.
    
    The [M__g] parameter is the dimensioning function; that is, the
    function yielding the values assigned to the generic constants
    being elaborated.  *)

Inductive EGens (Δ : ElDesign) (M__g : IdMap value) : list gdecl -> ElDesign -> Prop :=

(** Elaborates an empty list of generic constant declaration. *)
| EGensNil: EGens Δ M__g [] Δ

(** Elaborates a non-empty list of generic constant declaration. *)
| EGensCons:
    forall gd lofgdecls Δ' Δ'',
      EGen Δ M__g gd Δ' ->
      EGens Δ' M__g lofgdecls Δ'' ->
      EGens Δ M__g (gd :: lofgdecls) Δ''
    
(** Defines the elaboration relation for one generic constant declaration. *)
with EGen (Δ : ElDesign) (M__g : IdMap value) : gdecl -> ElDesign -> Prop :=
  
(* Elaboration with given a dimensioning value. *)
| EGenM__G :
    forall idg τ e t dv v,
      
      (* Premises *)
      ETypeg τ t ->
      IsLStaticExpr e ->
      VExpr EmptyElDesign EmptySStore EmptyLEnv false e dv ->
      IsOfType dv t ->
      IsOfType v t ->
      
      (* Side conditions *)
      ~NatMap.In idg Δ -> (* idg ∉ Δ *)
      MapsTo idg v M__g ->  (* idg ∈ M and M(idg) = v *)
      
      (* Conclusion *)
      EGen Δ M__g (gdecl_ idg τ e) (MkElDesign (add idg (Generic t v) Δ))

(* Elaboration with default value. *)
| EGenDefault :
    forall idg τ e t dv,
      
      (* Premises *)
      ETypeg τ t ->
      IsLStaticExpr e ->
      VExpr EmptyElDesign EmptySStore EmptyLEnv false e dv ->
      IsOfType dv t ->

      (* Side conditions *)
      ~NatMap.In idg Δ ->      (* idg ∉ Δ *)
      ~NatMap.In idg M__g ->     (* idg ∉ M *)
      
      (* Conclusion *)
      EGen Δ M__g (gdecl_ idg τ e) (MkElDesign (add idg (Generic t dv) Δ)).

      

