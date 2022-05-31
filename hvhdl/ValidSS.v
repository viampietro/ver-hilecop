(** * Validity check for sequential statements *)

Require Import common.GlobalTypes.

Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.Environment.
Require Import hvhdl.ExpressionEvaluation.
Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.HVhdlTypes.

Import NatMap.

(** Defines the [ValidSS] predicate that states the well-formedness
    and well-typedness of sequential statements in an H-VHDL
    design. *)

Inductive ValidSS (Δ : ElDesign) (sst : IdMap value) (Λ : LEnv) : ss -> Prop :=

(** Well-typedness of a value assignment to a signal (either internal
    or output port). *)
| ValidSSSigAssign :
    forall id e v t,

      (* Premises *)
      VExpr Δ sst Λ false e v ->
      IsOfType v t ->

      (* Side conditions *)
      (* id ∈ S(Δ) ∪ O(Δ) and Δ(id) = t *)
      MapsTo id (Internal t) Δ \/ MapsTo id (Output t) Δ -> 

      (* Conclusion *)
      ValidSS Δ sst Λ (ss_sig (n_id id) e)
              
(** Well-typedness of a value assignment to a signal identifier
    (either internal or output port) with index. *)
| ValidSSIdxSigAssign :
    forall id e ei v i t l u,

      (* Premises *)
      VExpr Δ sst Λ false e v ->
      VExpr Δ sst Λ false ei (Vnat i) ->
      IsOfType v t ->
      IsOfType (Vnat i) (Tnat l u) ->
                 
      (* Side conditions *)
      (* id ∈ Sigs(Δ) and Δ(id) = array(t, l, u) *)
      MapsTo id (Internal (Tarray t l u)) Δ
      \/ MapsTo id (Output (Tarray t l u)) Δ ->

      (* Conclusion *)
      ValidSS Δ sst Λ (ss_sig (n_xid id ei) e)
              
(** Well-typedness of a variable assignment. *)
| ValidSSVarAssign :
    forall id e t v val,

      (* Premises *)
      VExpr Δ sst Λ false e v ->
      IsOfType v t ->
            
      (* Side conditions *)
      MapsTo id (t, val) Λ -> (* id ∈ Λ and Λ(id) = (t, val) *)
      
      ValidSS Δ sst Λ (ss_var (n_id id) e)

(** Well-typedness of a variable assignment, with an indexed
    variable identifier. *)
| ValidSSIdxVarAssign :
    forall id e ei t v i val l u,

      (* Premises *)
      VExpr Δ sst Λ false e v ->
      VExpr Δ sst Λ false ei (Vnat i) ->
      IsOfType v t ->
      IsOfType (Vnat i) (Tnat l u) ->
      
      (* Side conditions *)
      MapsTo id (Tarray t l u, val) Λ -> (* id ∈ Λ and Λ(id) = (array(t,l,u), val) *)

      (* Conclusion *)
      ValidSS Δ sst Λ (ss_var (n_xid id ei) e)

(** Well-typedness of a conditional statement. *)
| ValidSSIfElse :
    forall e stmt stmt' v,

      (* Premises *)
      VExpr Δ sst Λ false e v ->
      IsOfType v Tbool ->
      ValidSS Δ sst Λ stmt ->
      ValidSS Δ sst Λ stmt' ->
      
      (* Conclusion *)
      ValidSS Δ sst Λ (ss_ifelse e stmt stmt')

(** Well-typedness of a loop statement. *)
| ValidSSLoop :
    forall id e e' stmt n n' lenv',

      (* Premises *)

      (** If [VExpr] interprets [e] and [e'] into [nat] values then it
         implies [IsOfType (Vnat n) nat(0,NATMAX)] and [IsOfType (Vnat
         n') nat(0,NATMAX)].  *)
      VExpr Δ sst Λ false e (Vnat n) ->
      VExpr Δ sst Λ false e' (Vnat n') ->
      ValidSS Δ sst lenv' stmt ->
      
      (* Side conditions *)

      (* The loop variable is added to the local environment 
         before checking the validity of the loop block statement.
       *)
      lenv' = add id (Tnat n n', Vnat n) Λ ->
      
      (* Conclusion *)
      ValidSS Δ sst Λ (ss_loop id e e' stmt)

(** Well-typedness of a rising edge block statement. *)
| ValidSSRising :
    forall stmt,
      ValidSS Δ sst Λ stmt ->
      ValidSS Δ sst Λ (ss_rising stmt)

(** Well-typedness of a falling edge block statement. *)
| ValidSSFalling :
    forall stmt,
      ValidSS Δ sst Λ stmt ->
      ValidSS Δ sst Λ (ss_falling stmt)

(** Well-typedness of a rst block statement *)              
| ValidSSRst :
    forall stmt stmt',
      ValidSS Δ sst Λ stmt ->
      ValidSS Δ sst Λ stmt' ->
      ValidSS Δ sst Λ (ss_rst stmt stmt')

(** Well-typedness of a null statement *)
| ValidSSNull : ValidSS Δ sst Λ ss_null.
