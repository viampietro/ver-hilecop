(** * Evaluation of sequential statements. *)

Require Import common.CoqLib.

Require Import Environment.
Require Import AbstractSyntax.
Require Import ExpressionEvaluation.
Require Import SemanticalDomains.

Open Scope abss_scope.
Open Scope N_scope.

Import HVhdlSsNotations.


(** Defines the relation that evaluates the sequential statements
    of H-VHDL. 
    
    [vseq] does not define error cases. *)

Inductive seqflag : Set := fe | re | stab | initl.

Inductive vseq (Δ : ElDesign) (σ σ__w : DState) (Λ : LEnv) : seqflag -> ss -> DState -> LEnv -> Prop :=

(** Evaluates a signal assignment statement.

    The target must be a declared signal or a out port identifier.

    Case where the assignment generates an event (i.e, a change of
    value). *)
  
| VSeqSigAssignEvent :
    forall flag id e newv t currv σ__w',
      
      (* * Premises * *)
      VExpr Δ σ Λ false e newv -> (* e ⇝ newv *)
      IsOfType newv t ->             (* [newv ∈c t] *)
      IsOfType currv t ->            (* [currv ∈c t] *)
      
      (* * Side conditions * *)
      
      (* id ∈ Sigs(Δ) ∨ id ∈ Outs(Δ) and Δ(id) = t *)
      (NatMap.MapsTo id (Declared t) Δ \/ NatMap.MapsTo id (Output t) Δ) -> 
      NatMap.MapsTo id currv (sstore σ) -> (* id ∈ σ and σ(id) = currv *)

      (* new value <> current value, then an event must be registered on signal [id] *)
      OVEq newv currv (Some false) -> 
      
      (* [σ__w=<S,C,E>, S' = S(id) ← v, E' = E ∪ {id}, σ__w'=<S',C,E'>]  *)
      σ__w' = (events_add id (sstore_add id newv σ__w)) -> 
      
      (* * Conclusion: [Δ,σ,σ__w,Λ ⊢ id ⇐ e ⇝ σ__w',Λ] * *)
      vseq Δ σ σ__w Λ flag ($id @<== e) σ__w' Λ

(** Evaluates a signal assignment statement.

    The target must be a declared signal or an out port identifier.

    Case where the assignment generates no event. *)
  
| VSeqSigAssignNoEvent :
    forall flag id e newv t currv,
      
      (* * Premises * *)
      VExpr Δ σ Λ false e newv ->
      IsOfType newv t ->
      IsOfType currv t ->
      
      (* * Side conditions * *)

      (* id ∈ Sigs(Δ) ∨ id ∈ Outs(Δ) and Δ(id) = t *)
      (NatMap.MapsTo id (Declared t) Δ \/ NatMap.MapsTo id (Output t) Δ) ->
      NatMap.MapsTo id currv (sstore σ) -> (* id ∈ σ and σ(id) = currv *)
      OVEq newv currv (Some true) -> (* new value = current value *)
      
      (* * Conclusion * *)
      vseq Δ σ σ__w Λ flag ($id @<== e) σ__w Λ

(** Evaluates a signal assignment statement.

    The target must be a declared signal or a out port identifier with an index.

    Case where the assignment generates an event (i.e, a change of
    value). *)
           
| VSeqIdxSigAssignEvent :
    forall flag id e ei newv i t l u σ__w'
           (curraofv newaofv : arrofvalues)
           idx_in_bounds,
      
      let idx := (N.to_nat (i - l)) in
      
      (*  * Premises * *)
      VExpr Δ σ Λ false e newv ->
      IsOfType newv t ->
      IsOfType (Varr curraofv) (Tarray t l u) ->
      
      (* These two lines are equivalent to: ei → vi ∧ vi ∈c nat(l,u) *)
      VExpr Δ σ Λ false ei (Vnat i) ->
      l <= i <= u ->
        
      (* * Side conditions * *)
      
      (* id ∈ Sigs(Δ) ∪ Outs(Δ) and Δ(id) = array(t,l,u) *)
      (NatMap.MapsTo id (Declared (Tarray t l u)) Δ \/ NatMap.MapsTo id (Output (Tarray t l u)) Δ) ->
      
      (* id ∈ σ and σ(id) = curraofv *)
      NatMap.MapsTo id (Varr curraofv) (sstore σ) ->

      (* new value <> current value *)
      OVEq newv (get_at idx curraofv idx_in_bounds) (Some false) -> 

      (* - [σ__w = <S,C,E>, σ__w' = <S',C,E'>]
         - S' = S(id) ← set_at(newv, i, currlofv), E' = E ∪ {id} 
       *)
      σ__w' = (events_add id (sstore_add id (Varr (set_at newv idx curraofv idx_in_bounds)) σ__w)) ->
      
      (* Conclusion *)
      vseq Δ σ σ__w Λ flag (id $[[ei]] @<== e) σ__w' Λ

(** Evaluates a signal assignment statement.

    The target must be a declared signal or an out port identifier with an index.

    Case where the assignment generates no event. *)
           
| VSeqIdxSigAssignNoEvent :
    forall flag id e ei newv i t l u curraofv idx_in_bounds,

      let idx := (N.to_nat (i - l)) in
      
      (* * Premises * *)
      VExpr Δ σ Λ false e newv ->
      IsOfType newv t ->
      IsOfType (Varr curraofv) (Tarray t l u) ->
      
      (* These two lines are equivalent to: ei → vi ∧ vi ∈c nat(l,u) *)
      VExpr Δ σ Λ false ei (Vnat i) ->
      l <= i <= u ->
      
      (* Side conditions *)
      
      (* id ∈ Sigs(Δ) ∪ Outs(Δ) and Δ(id) = array(t,l,u) *)
      (NatMap.MapsTo id (Declared (Tarray t l u)) Δ \/ NatMap.MapsTo id (Output (Tarray t l u)) Δ) -> 
      NatMap.MapsTo id (Varr curraofv) (sstore σ) -> (* id ∈ σ and σ(id) = curraofv *)

      OVEq newv (get_at idx curraofv idx_in_bounds) (Some true) -> (* new value = current value *)
            
      (* Conclusion *)
      vseq Δ σ σ__w Λ flag (id $[[ei]] @<== e) σ__w Λ
           
(** Evaluates a variable assignment statement.

    The target must be a variable identifier. *)
           
| VSeqVarAssign :
    forall flag id e newv t currv,
      
      (* * Premises * *)
      VExpr Δ σ Λ false e newv ->
      IsOfType newv t ->
      IsOfType currv t ->
      
      (* * Side conditions * *)
      NatMap.MapsTo id (t, currv) Λ -> (* id ∈ Λ and Λ(id) = (t, currv) *)
      
      (* * Conclusion * *)
      vseq Δ σ σ__w Λ flag ($id @:= e) σ__w (NatMap.add id (t, newv) Λ)

(** Evaluates a variable assignment statement.

    The target must be a variable identifier with an index. *)
           
| VSeqIdxVarAssign :
    forall flag id e ei newv i t l u curraofv newaofv idx_in_bounds,

      let idx := (N.to_nat (i - l)) in
      
      (* * Premises * *)
      VExpr Δ σ Λ false e newv ->
      IsOfType newv t ->
      IsOfType (Varr curraofv) (Tarray t l u) ->
      
      (* These two lines are equivalent to: ei ⇝ vi ∧ vi ∈c nat(l,u) *)
      VExpr Δ σ Λ false ei (Vnat i) ->
      l <= i <= u ->      

      (* * Side conditions * *)
      
      (* id ∈ Λ and Λ(id) = (array(t, l, u), curraofv) *)
      NatMap.MapsTo id (Tarray t l u, (Varr curraofv)) Λ ->
      set_at newv idx curraofv idx_in_bounds = newaofv ->
      
      (* * Conclusion * *)
      vseq Δ σ σ__w Λ flag (id $[[ei]] @:= e) σ__w (NatMap.add id (Tarray t l u, (Varr newaofv)) Λ)

(** Evaluates a simple if statement with a true condition. *)

| VSeqIfTrue :
    forall flag e stmt σ__w' Λ',
      
      (* * Premises * *)
      VExpr Δ σ Λ false e (Vbool true) ->
      vseq Δ σ σ__w Λ flag stmt σ__w' Λ' ->
      
      (* * Conclusion * *)
      vseq Δ σ σ__w Λ flag (If e Then stmt) σ__w' Λ'

(** Evaluates a simple if statement with a false condition. *)

| VSeqIfFalse :
    forall flag e stmt,
      
      (* * Premises * *)
      VExpr Δ σ Λ false e (Vbool false) ->
      
      (* * Conclusion * *)
      vseq Δ σ σ__w Λ flag (If e Then stmt) σ__w Λ

(** Evaluates a if-else statement with a true condition. *)

| VSeqIfElseTrue :
    forall flag e stmt stmt' σ__w' Λ',
      
      (* * Premises * *)
      VExpr Δ σ Λ false e (Vbool true) ->
      vseq Δ σ σ__w Λ flag stmt σ__w' Λ' ->
      
      (* * Conclusion * *)
      vseq Δ σ σ__w Λ flag (If e Then stmt Else stmt') σ__w' Λ'

(** Evaluates a if-else statement with a false condition. *)

| VSeqIfElseFalse :
    forall flag e stmt stmt' σ__w' Λ',
      
      (* * Premises * *)
      VExpr Δ σ Λ false e (Vbool false) ->
      vseq Δ σ σ__w Λ flag stmt' σ__w' Λ' ->
      
      (* * Conclusion * *)
      vseq Δ σ σ__w Λ flag (If e Then stmt Else stmt') σ__w' Λ'

(** Evaluates a loop statement.
    
    Initialization, add the loop variable to the local environment
    with initial value.  *)

| VSeqLoopInit :
    forall flag id e e' stmt n n' Λi σ__w' Λ',

      (* * Premises * *)
      VExpr Δ σ Λ false e (Vnat n) ->
      VExpr Δ σ Λ false e' (Vnat n') ->
      
      vseq Δ σ σ__w Λi flag (For id InR e To e' Loop stmt) σ__w' Λ' ->

      (* * Side conditions * *)
      ~NatMap.In id Λ ->     (* id ∉ Λ *)
      Λi = NatMap.add id (Tnat n n', Vnat n) Λ -> (* Λi = Λ ∪ (id, (nat(n,n'), n)) *)

      (* * Conclusion * *)
      vseq Δ σ σ__w Λ flag (For id InR e To e' Loop stmt) σ__w' Λ'

(** Evaluates a loop statement.
    
    Case where the loop variable is already in the local environment
    (it is not the first iteration), but the upper bound value is not
    reached yet.  *)

| VSeqLoopFalse :
    forall flag id e e' stmt t n Λi σ__w' Λ' σ__w'' Λ'',

      (* * Premises * *)
      
      (* The upper bound is not reached. id = e' ⇝ ⊥ *)
      VExpr Δ σ Λi false (#id @= e') (Vbool false) ->
      vseq Δ σ σ__w Λi flag stmt σ__w' Λ' ->
      vseq Δ σ σ__w' Λ' flag (For id InR e To e' Loop stmt) σ__w'' Λ'' ->

      (* * Side conditions * *)
      NatMap.MapsTo id (t, Vnat n) Λ ->
      Λi = NatMap.add id (t, Vnat (n + 1)) Λ ->

      (* * Conclusion * *)
      vseq Δ σ σ__w Λ flag (For id InR e To e' Loop stmt) σ__w'' Λ''
           
(** Evaluates a loop statement.
    
    Case where the loop variable is already in the local environment
    (it is not the first iteration), and the upper bound value is
    reached.  *)

| VSeqLoopTrue :
    forall flag id e e' stmt t n Λi,

      (* * Premises * *)
      VExpr Δ σ Λi false (e_binop bo_eq (e_name (n_id id)) e') (Vbool true) ->

      (* * Side conditions * *)
      NatMap.MapsTo id (t, Vnat n) Λ ->
      Λi = NatMap.add id (t, Vnat (n + 1)) Λ ->

      (* * Conclusion * *)
      (* Removes the binding of id from the local environment. *)
      vseq Δ σ σ__w Λ flag (For id InR e To e' Loop stmt) σ__w (NatMap.remove id Λ)
           
(** Evaluates a rising edge block statement when another flag than ↑
    is raised (i.e, during a stabilization, a ↓ or the initl phase).

    Does nothing; ↑ blocks only respond to ↑ flag. *)
           
| VSeqRisingDefault :
    forall flag stmt, flag <> re -> vseq Δ σ σ__w Λ flag (Rising stmt) σ__w Λ

(** Evaluates a rising edge block statement when the [re] flag is raised. 
    Evaluates the inner block of the rising edge statement.
 *)
           
| VSeqRising :
    forall stmt σ__w' Λ',
      
      (* * Premises * *)
      vseq Δ σ σ__w Λ re stmt σ__w' Λ' ->

      (* * Conclusion * *)
      vseq Δ σ σ__w Λ re (Rising stmt) σ__w' Λ'

(** Evaluates a falling edge block statement when another flag than ↓
    is raised (i.e, during a stabilization, a ↑ or the initl phase).

    Does nothing; ↓ blocks only respond to ↓ flag. *)
                      
| VSeqFallingDefault :
    forall flag stmt, flag <> fe -> vseq Δ σ σ__w Λ flag (Rising stmt) σ__w Λ
           
(** Evaluates a falling edge block statement when the [fe] flag is
    raised. Evaluates the inner block of the falling edge statement. *)
                                   
| VSeqFalling :
    forall stmt σ__w' Λ',
      
      (* * Premises * *)
      vseq Δ σ σ__w Λ fe stmt σ__w' Λ' ->

      (* * Conclusion * *)
      vseq Δ σ σ__w Λ fe (Falling stmt) σ__w' Λ'
           
(** Evaluates a rst block statement when another flag than [init] is
    raised (i.e, during a stabilization, a ↑ or a ↓ phase).

    The second inner statement is evaluated. *)
           
| VSeqRstDefault :
    forall flag stmt stmt' σ__w' Λ',

      (* * Side conditions * *)
      flag <> initl ->
      
      (* * Premises * *)
      vseq Δ σ σ__w Λ flag stmt' σ__w' Λ' ->

      (* * Conclusion * *)
      vseq Δ σ σ__w Λ flag (ss_rst stmt stmt') σ__w' Λ'

(** Evaluates a rst block statement when the [init] flag is raised
    (i.e, during the initialization phase).

    The first inner statement is evaluated. *)
           
| VSeqRst :
    forall stmt stmt' σ__w' Λ',

      (* * Premises * *)
      vseq Δ σ σ__w Λ initl stmt σ__w' Λ' ->

      (* * Conclusion * *)
      vseq Δ σ σ__w Λ initl (ss_rst stmt stmt') σ__w' Λ'
           
(** Evaluates the null statement. *)
| VSeqNull :
    forall flag, vseq Δ σ σ__w Λ flag (ss_null) σ__w Λ
                      
(** Evaluates a sequence of statements. *)

| VSeqSeq :
    forall flag stmt stmt' σ__w' Λ' σ__w'' Λ'',
      
      (* * Premises * *)
      vseq Δ σ σ__w Λ flag stmt σ__w' Λ' ->
      vseq Δ σ σ__w' Λ' flag stmt σ__w'' Λ'' ->

      (* * Conclusion * *)
      vseq Δ σ σ__w Λ flag (stmt ;; stmt') σ__w'' Λ''.

