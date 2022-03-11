(** * Validss predicate. *)

Require Import GlobalTypes.
Require Import AbstractSyntax.
Require Import Environment.
Require Import ExpressionEvaluation.
Require Import SemanticalDomains.

Import NatMap.

(** Defines the validss predicate that states the well-formedness and
    well-typedness of sequential statements in an H-VHDL program. *)

Inductive validss (Δ : ElDesign) (σ : DState) (Λ : LEnv) : ss -> Prop :=

(** Well-typedness of a value assignment to a declared signal. *)
| ValidSsSigAssignDecl :
    forall {id e v t},

      (* Premises *)
      vexpr Δ σ Λ false e v ->
      IsOfType v t ->

      (* Side conditions *)
      MapsTo id (Declared t) Δ -> (* id ∈ Sigs(Δ) and Δ(id) = t *)

      (* Conclusion *)
      validss Δ σ Λ (ss_sig (n_id id) e)
              
(** Well-typedness of a value assignment to a port in "out" mode. *)
| ValidSsSigAssignOut :
    forall {id e v t},

      (* Premises *)
      vexpr Δ σ Λ false e v ->
      IsOfType v t ->

      (* Side conditions *)
      MapsTo id (Output t) Δ -> (* id ∈ Outs(Δ) and Δ(id) = t *)

      (* Conclusion *)
      validss Δ σ Λ (ss_sig (n_id id) e)

(** Well-typedness of a value assignment to a declared signal
    identifier with index. *)
| ValidSsIdxSigAssignDecl :
    forall {id e ei v vi t l u},

      (* Premises *)
      vexpr Δ σ Λ false e v ->
      vexpr Δ σ Λ false ei vi ->
      IsOfType v t ->
      IsOfType vi (Tnat l u) ->
                 
      (* Side conditions *)
      MapsTo id (Declared (Tarray t l u)) Δ -> (* id ∈ Sigs(Δ) and Δ(id) = array(t, l, u) *)

      (* Conclusion *)
      validss Δ σ Λ (ss_sig (n_xid id ei) e)

(** Well-typedness of a value assignment to an "out" port
    identifier with index. *)
| ValidSsIdxSigAssignOut :
    forall {id e ei v vi t l u},

      (* Premises *)
      vexpr Δ σ Λ false e v ->
      vexpr Δ σ Λ false ei vi ->
      IsOfType v t ->
      IsOfType vi (Tnat l u) ->
      
      (* Side conditions *)
      MapsTo id (Output (Tarray t l u)) Δ -> (* id ∈ Sigs(Δ) and Δ(id) = array(t, l, u) *)

      (* Conclusion *)
      validss Δ σ Λ (ss_sig (n_xid id ei) e)
              
(** Well-typedness of a variable assignment. *)
| ValidSsVarAssign :
    forall {id e t v val},

      (* Premises *)
      vexpr Δ σ Λ false e v ->
      IsOfType v t ->
            
      (* Side conditions *)
      MapsTo id (t, val) Λ -> (* id ∈ Λ and Λ(id) = (t, val) *)
      
      validss Δ σ Λ (ss_var (n_id id) e)

(** Well-typedness of a variable assignment, with an indexed
    variable identifier. *)
| ValidSsIdxVarAssign :
    forall {id e ei t v vi val l u},

      (* Premises *)
      vexpr Δ σ Λ false e v ->
      vexpr Δ σ Λ false ei vi ->
      IsOfType v t ->
      IsOfType vi (Tnat l u) ->
      
      (* Side conditions *)
      MapsTo id (Tarray t l u, val) Λ -> (* id ∈ Λ and Λ(id) = (array(t,l,u), val) *)

      (* Conclusion *)
      validss Δ σ Λ (ss_var (n_xid id ei) e)

(** Well-typedness of a simple if statement. *)
| ValidSsIf :
    forall {e stmt v},

      (* Premises *)
      vexpr Δ σ Λ false e v ->
      IsOfType v Tbool ->
      validss Δ σ Λ stmt ->
      
      (* Conclusion *)
      validss Δ σ Λ (ss_if e stmt)

(** Well-typedness of a if-else statement. *)
| ValidSsIfElse :
    forall {e stmt stmt' v},

      (* Premises *)
      vexpr Δ σ Λ false e v ->
      IsOfType v Tbool ->
      validss Δ σ Λ stmt ->
      validss Δ σ Λ stmt' ->
      
      (* Conclusion *)
      validss Δ σ Λ (ss_ifelse e stmt stmt')

(** Well-typedness of a loop statement. *)
| ValidSsLoop :
    forall {id e e' stmt n n' lenv'},

      (* Premises *)

      (** If [vexpr] interprets [e] and [e'] into [nat] values then it
         implies [IsOfType (Vnat n) nat(0,NATMAX)] and [IsOfType
         (Vnat n') nat(0,NATMAX)].  *)
      vexpr Δ σ Λ false e (Vnat n) ->
      vexpr Δ σ Λ false e' (Vnat n') ->
      validss Δ σ lenv' stmt ->
      
      (* Side conditions *)

      (* The loop variable is added to the local environment 
         before checking the validity of the loop block statement.
       *)
      lenv' = add id (Tnat n n', Vnat n) Λ ->
      
      (* Conclusion *)
      validss Δ σ Λ (ss_loop id e e' stmt)

(** Well-typedness of a rising edge block statement. *)
| ValidSsRising :
    forall {stmt},
      validss Δ σ Λ stmt ->
      validss Δ σ Λ (ss_rising stmt)

(** Well-typedness of a falling edge block statement. *)
| ValidSsFalling :
    forall {stmt},
      validss Δ σ Λ stmt ->
      validss Δ σ Λ (ss_falling stmt)

(** Well-typedness of a rst block statement *)              
| ValidSsRst :
    forall stmt stmt',
      validss Δ σ Λ stmt ->
      validss Δ σ Λ stmt' ->
      validss Δ σ Λ (ss_rst stmt stmt')

(** Well-typedness of a null statement *)
| ValidSsNull : validss Δ σ Λ ss_null.
