(** Module that implement the relation evaluating H-VHDL
    expressions. *)

Require Import Coqlib.
Require Import GlobalTypes.
Require Import AbstractSyntax.
Require Import Environment.
Require Import SemanticalDomains.

(** Defines the expression evaluation relation. 
    
    The environment is composed of:
    - [denv], the design environment.
    - [dstate], the design state.
    - [lenv], a local environment (process environment).
    
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
| VExprTransT (t : transition_t) : vexpr denv dstate lenv (e_trans t) (Some (Vtransition t)).
                                
(** Evaluates aggregate expression. *)
| VExprAggreg (le : list expr) (lv : list value) :
    (forall (e : expr), In e le -> vexpr denv dstate lenv e (Some v) /\ In v lv) ->
    length le = length lv
      
