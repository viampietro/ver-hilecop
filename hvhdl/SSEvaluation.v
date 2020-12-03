(** * Evaluation of sequential statements. *)

Require Import Environment.
Require Import AbstractSyntax.
Require Import ExpressionEvaluation.
Require Import SemanticalDomains.

Open Scope abss_scope.

(** Defines the relation that evaluates the sequential statements
    of H-VHDL. 
    
    [vseq] does not define error cases.
 *)

Inductive seqflag : Set := fe | re | stab.

Inductive vseq (Δ : ElDesign) (σ : DState) (Λ : LEnv) : seqflag -> ss -> DState -> LEnv -> Prop :=

(** Evaluates a signal assignment statement.

    The target must be a declared signal or a out port identifier.

    Case where the assignment generates an event (i.e, a change of
    value). *)
  
| VSeqSigAssignEvent :
    forall flag id e newv t currv σ',
      
      (* * Premises * *)
      vexpr Δ σ Λ false e newv -> (* e ⇝ newv *)
      is_of_type newv t ->             (* newv ∈c t *)

      (* * Side conditions * *)
      
      (* id ∈ Sigs(Δ) ∨ id ∈ Outs(Δ) and Δ(id) = t *)
      (NatMap.MapsTo id (Declared t) Δ \/ NatMap.MapsTo id (Output t) Δ) -> 
      NatMap.MapsTo id currv (sigstore σ) -> (* id ∈ σ and σ(id) = currv *)

      (* new value <> current value, then an event must be registered on signal [id] *)
      OVEq newv currv (Some false) -> 
      
      (* σ=<S,C,E>, S' = S(id) ← v, E' = E ∪ {id}, σ'=<S',C,E'>  *)
      σ' = (events_add id (sstore_add id newv σ)) -> 
      
      (* * Conclusion: Δ,σ,Λ ⊢ id ⇐ e ⇝ σ',Λ * *)
      vseq Δ σ Λ flag ($id @<== e) σ' Λ

(** Evaluates a signal assignment statement.

    The target must be a declared signal or an out port identifier.

    Case where the assignment generates no event. *)
  
| VSeqSigAssignNoEvent :
    forall flag id e newv t currv,
      
      (* * Premises * *)
      vexpr Δ σ Λ false e newv ->
      is_of_type newv t ->

      (* * Side conditions * *)

      (* id ∈ Sigs(Δ) ∨ id ∈ Outs(Δ) and Δ(id) = t *)
      (NatMap.MapsTo id (Declared t) Δ \/ NatMap.MapsTo id (Output t) Δ) ->
      NatMap.MapsTo id currv (sigstore σ) -> (* id ∈ σ and σ(id) = v' *)
      OVEq newv currv (Some true) -> (* new value = current value *)
      
      (* * Conclusion * *)
      vseq Δ σ Λ flag ($id @<== e) σ Λ

(** Evaluates a signal assignment statement.

    The target must be a declared signal or a out port identifier with an index.

    Case where the assignment generates an event (i.e, a change of
    value). *)
           
| VSeqIdxSigAssignEvent :
    forall flag id e ei newv i t l u σ'
           (curraofv newaofv : arrofvalues)
           idx_in_bounds,
      
      let idx := i - l in
      
      (*  * Premises * *)
      vexpr Δ σ Λ false e newv ->
      is_of_type newv t ->

      (* These two lines are equivalent to: ei ⇝ vi ∧ vi ∈c nat(l,u) *)
      vexpr Δ σ Λ false ei (Vnat i) ->
      l <= i <= u ->
        
      (* * Side conditions * *)
      
      (* id ∈ Sigs(Δ) ∪ Outs(Δ) and Δ(id) = array(t,l,u) *)
      (NatMap.MapsTo id (Declared (Tarray t l u)) Δ \/ NatMap.MapsTo id (Output (Tarray t l u)) Δ) ->
      
      (* id ∈ σ and σ(id) = currlofv *)
      NatMap.MapsTo id (Varr curraofv) (sigstore σ) ->

      (* new value <> current value *)
      OVEq newv (get_at idx curraofv idx_in_bounds) (Some false) -> 

      (* - σ = <S,C,E>, σ' = <S',C,E'>
         - S' = S(id) ← set_at(newv, i, currlofv), E' = E ∪ {id} 
       *)
      σ' = (events_add id (sstore_add id (Varr (set_at newv idx curraofv idx_in_bounds)) σ)) ->
      
      (* Conclusion *)
      vseq Δ σ Λ flag (id $[[ei]] @<== e) σ' Λ

(** Evaluates a signal assignment statement.

    The target must be a declared signal or an out port identifier with an index.

    Case where the assignment generates no event. *)
           
| VSeqIdxSigAssignNoEvent :
    forall flag id e ei newv i t l u curraofv idx_in_bounds,

      let idx := i - l in
      
      (* * Premises * *)
      vexpr Δ σ Λ false e newv ->
      is_of_type newv t ->

      (* These two lines are equivalent to: ei ⇝ vi ∧ vi ∈c nat(l,u) *)
      vexpr Δ σ Λ false ei (Vnat i) ->
      l <= i <= u ->
      
      (* Side conditions *)
      
      (* id ∈ Sigs(Δ) ∪ Outs(Δ) and Δ(id) = array(t,l,u) *)
      (NatMap.MapsTo id (Declared (Tarray t l u)) Δ \/ NatMap.MapsTo id (Output (Tarray t l u)) Δ) -> 
      NatMap.MapsTo id (Varr curraofv) (sigstore σ) -> (* id ∈ σ and σ(id) = curraofv *)

      OVEq newv (get_at idx curraofv idx_in_bounds) (Some true) -> (* new value = current value *)
            
      (* Conclusion *)
      vseq Δ σ Λ flag (id $[[ei]] @<== e) σ Λ
           
(** Evaluates a variable assignment statement.

    The target must be a variable identifier. *)
           
| VSeqVarAssign :
    forall flag id e newv t currv,
      
      (* * Premises * *)
      vexpr Δ σ Λ false e newv ->
      is_of_type newv t ->

      (* * Side conditions * *)
      NatMap.MapsTo id (t, currv) Λ -> (* id ∈ Λ and Λ(id) = (t, currv) *)
      
      (* * Conclusion * *)
      vseq Δ σ Λ flag ($id @:= e) σ (NatMap.add id (t, newv) Λ)

(** Evaluates a variable assignment statement.

    The target must be a variable identifier with an index. *)
           
| VSeqIdxVarAssign :
    forall flag id e ei newv i t l u curraofv newaofv idx_in_bounds,

      let idx := i - l in
      
      (* * Premises * *)
      vexpr Δ σ Λ false e newv ->
      is_of_type newv t ->
      
      (* These two lines are equivalent to: ei ⇝ vi ∧ vi ∈c nat(l,u) *)
      vexpr Δ σ Λ false ei (Vnat i) ->
      l <= i <= u ->      

      (* * Side conditions * *)
      
      (* id ∈ Λ and Λ(id) = (array(t, l, u), curraofv) *)
      NatMap.MapsTo id (Tarray t l u, (Varr curraofv)) Λ ->
      set_at newv i curraofv idx_in_bounds = newaofv ->
      
      (* * Conclusion * *)
      vseq Δ σ Λ flag (id $[[ei]] @:= e) σ (NatMap.add id (Tarray t l u, (Varr newaofv)) Λ)

(** Evaluates a simple if statement with a true condition. *)

| VSeqIfTrue :
    forall flag e stmt σ' Λ',
      
      (* * Premises * *)
      vexpr Δ σ Λ false e (Vbool true) ->
      vseq Δ σ Λ flag stmt σ' Λ' ->
      
      (* * Conclusion * *)
      vseq Δ σ Λ flag (If e Then stmt) σ' Λ'

(** Evaluates a simple if statement with a false condition. *)

| VSeqIfFalse :
    forall flag e stmt,
      
      (* * Premises * *)
      vexpr Δ σ Λ false e (Vbool false) ->
      
      (* * Conclusion * *)
      vseq Δ σ Λ flag (If e Then stmt) σ Λ

(** Evaluates a if-else statement with a true condition. *)

| VSeqIfElseTrue :
    forall flag e stmt stmt' σ' Λ',
      
      (* * Premises * *)
      vexpr Δ σ Λ false e (Vbool true) ->
      vseq Δ σ Λ flag stmt σ' Λ' ->
      
      (* * Conclusion * *)
      vseq Δ σ Λ flag (If e Then stmt Else stmt') σ' Λ'

(** Evaluates a if-else statement with a false condition. *)

| VSeqIfElseFalse :
    forall flag e stmt stmt' σ' Λ',
      
      (* * Premises * *)
      vexpr Δ σ Λ false e (Vbool false) ->
      vseq Δ σ Λ flag stmt' σ' Λ' ->
      
      (* * Conclusion * *)
      vseq Δ σ Λ flag (If e Then stmt Else stmt') σ' Λ'

(** Evaluates a loop statement.
    
    Initialization, add the loop variable to the local environment
    with initial value.  *)

| VSeqLoopInit :
    forall flag id e e' stmt n n' Λi σ' Λ',

      (* * Premises * *)
      vexpr Δ σ Λ false e (Vnat n) ->
      vexpr Δ σ Λ false e' (Vnat n') ->
      
      vseq Δ σ Λi flag (For id In e To e' Loop stmt) σ' Λ' ->

      (* * Side conditions * *)
      ~NatMap.In id Λ ->     (* id ∉ Λ *)
      Λi = NatMap.add id (Tnat n n', Vnat n) Λ -> (* Λi = Λ ∪ (id, (nat(n,n'), n)) *)

      (* * Conclusion * *)
      vseq Δ σ Λ flag (For id In e To e' Loop stmt) σ' Λ'

(** Evaluates a loop statement.
    
    Case where the loop variable is already in the local environment
    (it is not the first iteration), but the upper bound value is not
    reached yet.  *)

| VSeqLoopFalse :
    forall flag id e e' stmt t n Λi σ' Λ' σ'' Λ'',

      (* * Premises * *)
      
      (* The upper bound is not reached. id = e' ⇝ ⊥ *)
      vexpr Δ σ Λi false (#id @= e') (Vbool false) ->
      vseq Δ σ Λi flag stmt σ' Λ' ->
      vseq Δ σ' Λ' flag (For id In e To e' Loop stmt) σ'' Λ'' ->

      (* * Side conditions * *)
      NatMap.MapsTo id (t, Vnat n) Λ ->
      Λi = NatMap.add id (t, Vnat (n + 1)) Λ ->

      (* * Conclusion * *)
      vseq Δ σ Λ flag (For id In e To e' Loop stmt) σ'' Λ''
           
(** Evaluates a loop statement.
    
    Case where the loop variable is already in the local environment
    (it is not the first iteration), and the upper bound value is
    reached.  *)

| VSeqLoopTrue :
    forall flag id e e' stmt t n Λi,

      (* * Premises * *)
      vexpr Δ σ Λi false (e_binop bo_eq (e_name (n_id id)) e') (Vbool true) ->

      (* * Side conditions * *)
      NatMap.MapsTo id (t, Vnat n) Λ ->
      Λi = NatMap.add id (t, Vnat (n + 1)) Λ ->

      (* * Conclusion * *)
      (* Removes the binding of id from the local environment. *)
      vseq Δ σ Λ flag (For id In e To e' Loop stmt) σ (NatMap.remove id Λ)
           
(** Evaluates a rising edge block statement when the [stab] or the [fe] flag is
    raised (i.e, during a stabilization or a ↓ phase).

    Does nothing; ↑ blocks do not respond during stabilization or ↓. *)
           
| VSeqRisingIdleOnStabAndFalling :
    forall flag stmt, flag = stab \/ flag = fe -> vseq Δ σ Λ flag (Rising stmt) σ Λ

(** Evaluates a rising edge block statement when the [re] flag is raised. 
    Evaluates the inner block of the rising edge statement.
 *)
           
| VSeqRising :
    forall stmt σ' Λ',
      
      (* * Premises * *)
      vseq Δ σ Λ re stmt σ' Λ' ->

      (* * Conclusion * *)
      vseq Δ σ Λ re (ss_rising stmt) σ' Λ'
           
(** Evaluates a falling edge block statement when the [stab] flag or the [re] flag is
    raised (i.e, during a stabilization or a ↑ phase).

    Does nothing; ↓ blocks do not respond during stabilization or ↑. *)
           
| VSeqFallingIdleOnStabAndRising :
    forall flag stmt, flag = stab \/ flag = re -> vseq Δ σ Λ flag (Rising stmt) σ Λ
           
(** Evaluates a falling edge block statement when the [fe] flag is
    raised. Evaluates the inner block of the falling edge statement. *)
                                   
| VSeqFalling :
    forall stmt σ' Λ',
      
      (* * Premises * *)
      vseq Δ σ Λ fe stmt σ' Λ' ->

      (* * Conclusion * *)
      vseq Δ σ Λ fe (Falling stmt) σ' Λ'

(** Evaluates the null statement. *)
| VSeqNull :
    forall flag, vseq Δ σ Λ flag (ss_null) σ Λ
                      
(** Evaluates a sequence of statements. *)

| VSeqSeq :
    forall flag stmt stmt' σ' Λ' σ'' Λ'',
      
      (* * Premises * *)
      vseq Δ σ Λ flag stmt σ' Λ' ->
      vseq Δ σ' Λ' flag stmt σ'' Λ'' ->

      (* * Conclusion * *)
      vseq Δ σ Λ flag (stmt ;; stmt') σ'' Λ''.

