(** Defines the relation that elaborates the architecture declarative
    part of a design, declared in abstract syntax.

    The result is the addition of entries refering to constant and
    declared signal declarations in the design environment [denv] (Δ)
    and the mapping from declared signal id to their default value in
    the design state [dstate] (σ).  *)

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

Inductive edecls (denv : DEnv) (dstate : DState)  : adecl -> DEnv -> DState -> Prop :=
  
(** Signal declaration elaboration. *)
  
| EDeclsSig :
    forall {tau t v id},
      
      (* Premises. *)
      etype denv tau t ->
      defaultv t v ->
      
      (* Side conditions. *)
      ~In id denv -> (* id ∉ Δ *)
      ~InSigStore id dstate ->  (* id ∉ σ *)

      (* Conclusion *)
      edecls denv dstate (adecl_sig id tau) (add id (Declared t) denv) (sigstore_add id v dstate)

(** Constant declaration elaboration. *)
             
| EDeclsConst :
    forall {id tau e t v},
      
      (* Premises. *)
      etype denv tau t ->
      is_gstatic_expr denv e ->
      vexpr denv dstate EmptyLEnv e (Some v) ->  
      
      (* Side conditions. *)
      ~In id denv -> (* id ∉ Δ *)

      (* Conclusion *)
      edecls denv dstate (adecl_const id tau e) (add id (Constant t v) denv) dstate

(** Sequence of architecture declaration. *)
| EDeclsSeq :
    forall {ad ad' denv' dstate' denv'' dstate''},
      edecls denv dstate ad denv' dstate' ->
      edecls denv' dstate' ad' denv'' dstate'' ->
      edecls denv dstate (adecl_seq ad ad') denv'' dstate''.
