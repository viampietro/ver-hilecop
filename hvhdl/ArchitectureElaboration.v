(** Defines the relation that elaborates the architecture declarative
    part of a design, declared in abstract syntax.

    The result is the addition of entries refering to constant and
    declared signal declarations in the design environment [denv] (Δ)
    and the mapping from declared signal id to their default value in
    the design state [dstate] (σ).  *)

Require Import Coqlib.
Require Import GlobalTypes.
Require Import AbstractSyntax.
Require Import SemanticalDomains.
Require Import Environment.
Require Import ExpressionEvaluation.
Require Import StaticExpressions.
Require Import TypeElaboration.
Require Import DefaultValue.

Import NatMap.

(** The architecture declarative part elaboration relation. *)

Inductive edecls (denv : DEnv) (dstate : DState)  : list adecl -> DEnv -> DState -> Prop :=

(** Empty list of architecture declarations. *)
| EDeclsNil : edecls denv dstate [] denv dstate
  
(** Sequence of architecture declaration. *)
| EDeclsCons :
    forall {ad lofadecls denv' dstate' denv'' dstate''},
      edecl denv dstate ad denv' dstate' ->
      edecls denv' dstate' lofadecls denv'' dstate'' ->
      edecls denv dstate (ad :: lofadecls) denv'' dstate''

(** Defines the elaboration relation for single architecture declaration. *)
with edecl (denv : DEnv) (dstate : DState)  : adecl -> DEnv -> DState -> Prop :=
  
(** Signal declaration elaboration. *)
  
| EDeclSig :
    forall {tau t v id},
      
      (* Premises. *)
      etype denv tau t ->
      defaultv t v ->
      
      (* Side conditions. *)
      ~In id denv -> (* id ∉ Δ *)
      ~InSigStore id dstate ->  (* id ∉ σ *)

      (* Conclusion *)
      edecl denv dstate (adecl_sig id tau) (add id (Declared t) denv) (sigstore_add id v dstate)

(** Constant declaration elaboration. *)
             
| EDeclConst :
    forall {id tau e t v},
      
      (* Premises. *)
      etype denv tau t ->
      is_gstatic_expr denv e ->
      vexpr denv dstate EmptyLEnv e v ->  
      
      (* Side conditions. *)
      ~In id denv -> (* id ∉ Δ *)

      (* Conclusion *)
      edecl denv dstate (adecl_const id tau e) (add id (Constant t v) denv) dstate.
