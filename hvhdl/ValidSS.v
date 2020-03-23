(** * Validss predicate. *)

Require Import GlobalTypes.
Require Import AbstractSyntax.
Require Import Environment.
Require Import ExpressionEvaluation.
Require Import SemanticalDomains.

Import NatMap.

(** Defines the validss predicate that states the well-formedness and
    well-typedness of sequential statements in an H-VHDL program. *)

Inductive validss (denv : DEnv) (dstate : DState) (lenv : LEnv) : ss -> Prop :=

(** Well-typedness of a value assignment to a declared signal. *)
| ValidSsSigAssignDecl :
    forall {id e v t},

      (* Premises *)
      vexpr denv dstate lenv e v ->
      is_of_type v t ->

      (* Side conditions *)
      MapsTo id (Declared t) denv -> (* id ∈ Sigs(Δ) and Δ(id) = t *)

      (* Conclusion *)
      validss denv dstate lenv (ss_sig (n_id id) e)
              
(** Well-typedness of a value assignment to a port in "out" mode. *)
| ValidSsSigAssignOut :
    forall {id e v t},

      (* Premises *)
      vexpr denv dstate lenv e v ->
      is_of_type v t ->

      (* Side conditions *)
      MapsTo id (Output t) denv -> (* id ∈ Outs(Δ) and Δ(id) = t *)

      (* Conclusion *)
      validss denv dstate lenv (ss_sig (n_id id) e)

(** Well-typedness of a value assignment to a declared signal
    identifier with index. *)
| ValidSsIdxSigAssignDecl :
    forall {id e ei v vi t l u},

      (* Premises *)
      vexpr denv dstate lenv e v ->
      vexpr denv dstate lenv ei vi ->
      is_of_type v t ->
      is_of_type vi (Tnat l u) ->
                 
      (* Side conditions *)
      MapsTo id (Declared (Tarray t l u)) denv -> (* id ∈ Sigs(Δ) and Δ(id) = array(t, l, u) *)

      (* Conclusion *)
      validss denv dstate lenv (ss_sig (n_xid id ei) e)

(** Well-typedness of a value assignment to an "out" port
    identifier with index. *)
| ValidSsIdxSigAssignOut :
    forall {id e ei v vi t l u},

      (* Premises *)
      vexpr denv dstate lenv e v ->
      vexpr denv dstate lenv ei vi ->
      is_of_type v t ->
      is_of_type vi (Tnat l u) ->
      
      (* Side conditions *)
      MapsTo id (Output (Tarray t l u)) denv -> (* id ∈ Sigs(Δ) and Δ(id) = array(t, l, u) *)

      (* Conclusion *)
      validss denv dstate lenv (ss_sig (n_xid id ei) e)
              
(** Well-typedness of a variable assignment. *)
| ValidSsVarAssign :
    forall {id e t v val},

      (* Premises *)
      vexpr denv dstate lenv e v ->
      is_of_type v t ->
            
      (* Side conditions *)
      MapsTo id (t, val) lenv -> (* id ∈ Λ and Λ(id) = (t, val) *)
      
      validss denv dstate lenv (ss_var (n_id id) e)

(** Well-typedness of a variable assignment, with an indexed
    variable identifier. *)
| ValidSsIdxVarAssign :
    forall {id e ei t v vi val l u},

      (* Premises *)
      vexpr denv dstate lenv e v ->
      vexpr denv dstate lenv ei vi ->
      is_of_type v t ->
      is_of_type vi (Tnat l u) ->
      
      (* Side conditions *)
      MapsTo id (Tarray t l u, val) lenv -> (* id ∈ Λ and Λ(id) = (array(t,l,u), val) *)

      (* Conclusion *)
      validss denv dstate lenv (ss_var (n_xid id ei) e)

(** Well-typedness of a simple if statement. *)
| ValidSsIf :
    forall {e stmt v},

      (* Premises *)
      vexpr denv dstate lenv e v ->
      is_of_type v Tbool ->
      validss denv dstate lenv stmt ->
      
      (* Conclusion *)
      validss denv dstate lenv (ss_if e stmt)

(** Well-typedness of a if-else statement. *)
| ValidSsIfElse :
    forall {e stmt stmt' v},

      (* Premises *)
      vexpr denv dstate lenv e v ->
      is_of_type v Tbool ->
      validss denv dstate lenv stmt ->
      validss denv dstate lenv stmt' ->
      
      (* Conclusion *)
      validss denv dstate lenv (ss_ifelse e stmt stmt')

(** Well-typedness of a loop statement. *)
| ValidSsLoop :
    forall {id e e' stmt n n' lenv'},

      (* Premises *)

      (** If [vexpr] interprets [e] and [e'] into [nat] values then it
         implies [is_of_type (Vnat n) nat(0,NATMAX)] and [is_of_type
         (Vnat n') nat(0,NATMAX)].  *)
      vexpr denv dstate lenv e (Vnat n) ->
      vexpr denv dstate lenv e' (Vnat n') ->
      validss denv dstate lenv' stmt ->
      
      (* Side conditions *)

      (* The loop variable is added to the local environment 
         before checking the validity of the loop block statement.
       *)
      lenv' = add id (Tnat n n', Vnat n) lenv ->
      
      (* Conclusion *)
      validss denv dstate lenv (ss_loop id e e' stmt)

(** Well-typedness of a rising edge block statement. *)
| ValidSsRising :
    forall {stmt},
      validss denv dstate lenv stmt ->
      validss denv dstate lenv (ss_rising stmt)

(** Well-typedness of a falling edge block statement. *)
| ValidSsFalling :
    forall {stmt},
      validss denv dstate lenv stmt ->
      validss denv dstate lenv (ss_falling stmt).
