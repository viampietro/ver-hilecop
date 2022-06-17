(** * Evaluation of sequential statements. *)

Require Import common.CoqLib.

Require Import hvhdl.Environment.
Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.ExpressionEvaluation.
Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.HVhdlTypes.

Open Scope abss_scope.
Open Scope N_scope.

Import NatMap.
Import HVhdlSsNotations.

(** Defines the relation that evaluates sequential statements.
    
    [VSeq] does not define error cases. *)

Inductive VSeq (Δ : ElDesign) (sst__r sst__w : IdMap value) (Λ : LEnv) :
  simflag -> ss -> IdMap value -> LEnv -> Prop :=

(** Evaluates a signal assignment statement.

    The target must be a declared signal or a output port
    identifier. *)
  
| VSeqSigAssign :
    forall flag id e v t,
      
      (* * Premises * *)
      VExpr Δ sst__r Λ false e v -> (* e ⇝ v *)
      IsOfType v t ->            (* [v ∈c t] *)
      
      (* * Side conditions * *)
      
      (* id ∈ S(Δ) ∪ O(Δ) and Δ(id) = t *)
      (NatMap.MapsTo id (Internal t) Δ \/ NatMap.MapsTo id (Output t) Δ) -> 
            
      (* * Conclusion: [Δ, sst, sst__w, Λ ⊢ id ⇐ e ⇝ sst__w(id) ← v, Λ] * *)
      VSeq Δ sst__r sst__w Λ flag ($id @<== e) (add id v sst__w) Λ

(** Evaluates a assignment to the subelement of a composite signal.

    The target must be a declared signal or a output port identifier
    with an index. *)
           
| VSeqIdxSigAssign :
    forall flag id e ei v n__i t l u (aofv : arrofvalues) idx_in_bounds,
      
      let i := (N.to_nat (n__i - l)) in
      
      (*  * Premises * *)
      VExpr Δ sst__r Λ false e v ->
      IsOfType v t ->
      VExpr Δ sst__r Λ false ei (Vnat n__i) ->
      IsOfType (Vnat n__i) (Tnat l u) ->
        
      (* * Side conditions * *)
      
      (* id ∈ Sigs(Δ) ∪ Outs(Δ) and Δ(id) = array(t, l, u) *)
      (NatMap.MapsTo id (Internal (Tarray t l u)) Δ \/ NatMap.MapsTo id (Output (Tarray t l u)) Δ) ->
      
      (* id ∈ sst and sst(id) = aofv *)
      NatMap.MapsTo id (Varr aofv) sst__w ->
      
      (* Conclusion *)
      VSeq Δ sst__r sst__w Λ flag (id $[[ei]] @<== e) (add id (Varr (set_at v i aofv idx_in_bounds)) sst__w) Λ
           
(** Evaluates a variable assignment statement.

    The target must be a variable identifier. *)
           
| VSeqVarAssign :
    forall flag id e v t val,
      
      (* * Premises * *)
      VExpr Δ sst__r Λ false e v ->
      IsOfType v t ->
      
      (* * Side conditions * *)
      NatMap.MapsTo id (t, val) Λ -> (* id ∈ Λ and Λ(id) = (t, val) *)
      
      (* * Conclusion * *)
      VSeq Δ sst__r sst__w Λ flag ($id @:= e) sst__w (NatMap.add id (t, v) Λ)

(** Evaluates a variable assignment statement.

    The target must be a variable identifier with an index. *)
           
| VSeqIdxVarAssign :
    forall flag id e ei v n__i t l u aofv idx_in_bounds,
      
      (* * Premises * *)
      VExpr Δ sst__r Λ false e v ->
      IsOfType v t ->
      VExpr Δ sst__r Λ false ei (Vnat n__i) ->
      IsOfType (Vnat n__i) (Tnat l u) -> 

      (* * Side conditions * *)
      
      (* id ∈ Λ and Λ(id) = (array(t, l, u), aofv) *)
      NatMap.MapsTo id (Tarray t l u, (Varr aofv)) Λ ->
      let i := (N.to_nat (n__i - l)) in
      let aofv' := set_at v i aofv idx_in_bounds in
      
      (* * Conclusion * *)
      VSeq Δ sst__r sst__w Λ flag (id $[[ei]] @:= e) sst__w (NatMap.add id (Tarray t l u, (Varr aofv')) Λ)

(** Evaluates a if-else statement with a true condition. *)

| VSeqIfElseTrue :
    forall flag e stmt stmt' sst__w' Λ',
      
      (* * Premises * *)
      VExpr Δ sst__r Λ false e (Vbool true) ->
      VSeq Δ sst__r sst__w Λ flag stmt sst__w' Λ' ->
      
      (* * Conclusion * *)
      VSeq Δ sst__r sst__w Λ flag (If e Then stmt Else stmt') sst__w' Λ'

(** Evaluates a if-else statement with a false condition. *)

| VSeqIfElseFalse :
    forall flag e stmt stmt' sst__w' Λ',
      
      (* * Premises * *)
      VExpr Δ sst__r Λ false e (Vbool false) ->
      VSeq Δ sst__r sst__w Λ flag stmt' sst__w' Λ' ->
      
      (* * Conclusion * *)
      VSeq Δ sst__r sst__w Λ flag (If e Then stmt Else stmt') sst__w' Λ'

(** Evaluates a loop statement.
    
    Case when the upper bound value is not reached yet.  *)

| VSeqLoopFalse :
    forall flag id e1 e2 v1 stmt sst__w' Λ' sst__w'' Λ'',

      (* * Premises * *)
      
      (* The upper bound is not reached, i.e. e2 does not evaluate to
         0. *)
      VExpr Δ sst__r Λ false (e2 @> 0) (Vbool true) ->
      VExpr Δ sst__r Λ false e1 v1 ->
      IsOfType v1 (Tnat 0 NATMAX) ->
      VSeq Δ sst__r sst__w (add id (Tnat 0 NATMAX, v1) Λ) flag stmt sst__w' Λ' ->
      VSeq Δ sst__r sst__w' Λ' flag (For id InR (e1 @+ 1) To (e2 @- 1) Loop stmt) sst__w'' Λ'' ->

      (* * Conclusion * *)
      VSeq Δ sst__r sst__w Λ flag (For id InR e1 To e2 Loop stmt) sst__w'' Λ''
           
(** Evaluates a loop statement.
    
    Case when the upper bound value is reached.  *)

| VSeqLoopTrue :
    forall flag id e1 e2 stmt,

      (* * Premises * *)
      VExpr Δ sst__r Λ false (e2 @= 0) (Vbool true) ->

      (* * Conclusion * *)
      (* Removes the binding of id from the local environment. *)
      VSeq Δ sst__r sst__w Λ flag (For id InR e1 To e2 Loop stmt) sst__w (NatMap.remove id Λ)
           
(** Evaluates a rising edge block statement when another flag than ↑
    is raised (i.e, during a stabilization, a ↓ or the initl phase).

    Does nothing; ↑ blocks only respond to ↑ flag. *)
           
| VSeqRisingDefault :
    forall flag stmt, flag <> rising -> VSeq Δ sst__r sst__w Λ flag (Rising stmt) sst__w Λ

(** Evaluates a rising edge block statement when the [re] flag is raised. 
    Evaluates the inner block of the rising edge statement.
 *)
           
| VSeqRising :
    forall stmt sst__w' Λ',
      
      (* * Premises * *)
      VSeq Δ sst__r sst__w Λ rising stmt sst__w' Λ' ->

      (* * Conclusion * *)
      VSeq Δ sst__r sst__w Λ rising (Rising stmt) sst__w' Λ'

(** Evaluates a falling edge block statement when another flag than ↓
    is raised (i.e, during a stabilization, a ↑ or the initl phase).

    Does nothing; ↓ blocks only respond to ↓ flag. *)
                      
| VSeqFallingDefault :
    forall flag stmt, flag <> falling -> VSeq Δ sst__r sst__w Λ flag (Rising stmt) sst__w Λ
           
(** Evaluates a falling edge block statement when the [fe] flag is
    raised. Evaluates the inner block of the falling edge statement. *)
                                   
| VSeqFalling :
    forall stmt sst__w' Λ',
      
      (* * Premises * *)
      VSeq Δ sst__r sst__w Λ falling stmt sst__w' Λ' ->

      (* * Conclusion * *)
      VSeq Δ sst__r sst__w Λ falling (Falling stmt) sst__w' Λ'
           
(** Evaluates a rst block statement when another flag than [init] is
    raised (i.e, during a stabilization, a ↑ or a ↓ phase).

    The second inner statement is evaluated. *)
           
| VSeqRstDefault :
    forall flag stmt stmt' sst__w' Λ',

      (* * Side conditions * *)
      flag <> init ->
      
      (* * Premises * *)
      VSeq Δ sst__r sst__w Λ flag stmt' sst__w' Λ' ->

      (* * Conclusion * *)
      VSeq Δ sst__r sst__w Λ flag (ss_rst stmt stmt') sst__w' Λ'

(** Evaluates a rst block statement when the [init] flag is raised
    (i.e, during the initialization phase).

    The first inner statement is evaluated. *)
           
| VSeqRst :
    forall stmt stmt' sst__w' Λ',

      (* * Premises * *)
      VSeq Δ sst__r sst__w Λ init stmt sst__w' Λ' ->

      (* * Conclusion * *)
      VSeq Δ sst__r sst__w Λ init (ss_rst stmt stmt') sst__w' Λ'
           
(** Evaluates the null statement. *)
| VSeqNull :
    forall flag, VSeq Δ sst__r sst__w Λ flag (ss_null) sst__w Λ
                      
(** Evaluates a sequence of statements. *)

| VSeqSeq :
    forall flag stmt stmt' sst__w' Λ' sst__w'' Λ'',
      
      (* * Premises * *)
      VSeq Δ sst__r sst__w Λ flag stmt sst__w' Λ' ->
      VSeq Δ sst__r sst__w' Λ' flag stmt sst__w'' Λ'' ->

      (* * Conclusion * *)
      VSeq Δ sst__r sst__w Λ flag (stmt ;; stmt') sst__w'' Λ''.

