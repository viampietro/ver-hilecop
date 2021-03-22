(** Defines the relation that elaborates the generic clause of a
    design, as declared in abstract syntax.
    
    The result is the addition of entries refering to generic constant
    declarations in the design environment.  *)

Require Import CoqLib.
Require Import GlobalTypes.
Require Import AbstractSyntax.
Require Import SemanticalDomains.
Require Import Environment.
Require Import ExpressionEvaluation.
Require Import StaticExpressions.
Require Import TypeElaboration.
Require Import HVhdlTypes.

Import NatMap.

(** The generic constant elaboration relation.
    
    The [M__g] parameter is the dimensioning function; that is, the
    function yielding the values assigned to the generic constants
    being elaborated.  *)

Inductive egens (Δ : ElDesign) (M__g : IdMap value) : list gdecl -> ElDesign -> Prop :=

(* Elaborates an empty list of generic constant declaration. *)
| EGensNil: egens Δ M__g [] Δ

(* Elaborates a non-empty list of generic constant declaration. *)
| EGensCons:
    forall {gd lofgdecls Δ' Δ''},
      egen Δ M__g gd Δ' ->
      egens Δ' M__g lofgdecls Δ'' ->
      egens Δ M__g (gd :: lofgdecls) Δ''
    
(** Defines the elaboration relation for one generic constant declaration. *)
with egen (Δ : ElDesign) (M__g : IdMap value) : gdecl -> ElDesign -> Prop :=
  
(* Elaboration with given a dimensioning value. *)
| EGenM__G :
    forall {idg τ e t dv v},
      
      (* Premises *)
      etypeg τ t ->
      is_lstatic_expr e ->
      vexpr EmptyElDesign EmptyDState EmptyLEnv false e dv ->
      is_of_type dv t ->
      is_of_type v t ->
      
      (* Side conditions *)
      ~NatMap.In idg Δ ->           (* idg ∉ Δ *)
      MapsTo idg v M__g ->     (* idg ∈ M and M(idg) = v *)
      
      (* Conclusion *)
      egen Δ M__g (gdecl_ idg τ e) (add idg (Generic t v) Δ)

(* Elaboration with default value. *)
| EGenDefault :
    forall {idg τ e t dv},
      
      (* Premises *)
      etypeg τ t ->
      is_lstatic_expr e ->
      vexpr EmptyElDesign EmptyDState EmptyLEnv false e dv ->
      is_of_type dv t ->

      (* Side conditions *)
      ~NatMap.In idg Δ ->      (* idg ∉ Δ *)
      ~NatMap.In idg M__g ->     (* idg ∉ M *)
      
      (* Conclusion *)
      egen Δ M__g (gdecl_ idg τ e) (add idg (Generic t dv) Δ).

      

