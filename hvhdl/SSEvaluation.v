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

Inductive vseq (ed : ElDesign) (dstate : DState) (lenv : LEnv) : ss -> DState -> LEnv -> Prop :=

(** Evaluates a signal assignment statement.

    The target must be a declared signal or a out port identifier.

    Case where the assignment generates an event (i.e, a change of
    value). *)
  
| VSeqSigAssignEvent :
    forall {id e newv t currv dstate'},
      
      (* * Premises * *)
      vexpr ed dstate lenv e newv -> (* e ⇝ newv *)
      is_of_type newv t ->             (* newv ∈c t *)

      (* * Side conditions * *)
      
      (* id ∈ Sigs(Δ) ∨ id ∈ Outs(Δ) and Δ(id) = t *)
      (NatMap.MapsTo id (Declared t) ed \/ NatMap.MapsTo id (Output t) ed) -> 
      NatMap.MapsTo id currv (sigstore dstate) -> (* id ∈ σ and σ(id) = currv *)

      VEq newv currv (Some false) -> (* new value <> current value *)

      (* dstate=<S,C,E>, S' = S(id) ← v, E' = E ∪ {id}, dstate'=<S',C,E'>  *)
      dstate' = (events_add id (sstore_add id newv dstate)) -> 
      
      (* * Conclusion: Δ,σ,Λ ⊢ id ⇐ e ⇝ σ',Λ * *)
      vseq ed dstate lenv ($id @<== e) dstate' lenv

(** Evaluates a signal assignment statement.

    The target must be a declared signal or an out port identifier.

    Case where the assignment generates no event. *)
  
| VSeqSigAssignNoEvent :
    forall {id e newv t currv},
      
      (* * Premises * *)
      vexpr ed dstate lenv e newv ->
      is_of_type newv t ->

      (* * Side conditions * *)

      (* id ∈ Sigs(Δ) ∨ id ∈ Outs(Δ) and Δ(id) = t *)
      (NatMap.MapsTo id (Declared t) ed \/ NatMap.MapsTo id (Output t) ed) ->
      NatMap.MapsTo id currv (sigstore dstate) -> (* id ∈ σ and σ(id) = v' *)
      VEq newv currv (Some true) -> (* new value = current value *)
      
      (* * Conclusion * *)
      vseq ed dstate lenv ($id @<== e) dstate lenv

(** Evaluates a signal assignment statement.

    The target must be a declared signal or a out port identifier with an index.

    Case where the assignment generates an event (i.e, a change of
    value). *)
           
| VSeqIdxSigAssignEvent :
    forall {id e ei newv i t l u currlofv currv newlofv dstate'},
      
      (*  * Premises * *)
      vexpr ed dstate lenv e newv ->
      is_of_type newv t ->

      (* These two lines are equivalent to: ei ⇝ vi ∧ vi ∈c nat(l,u) *)
      vexpr ed dstate lenv ei (Vnat i) ->
      l <= i <= u ->
        
      (* * Side conditions * *)
      
      (* id ∈ Sigs(Δ) ∨ id ∈ Outs(Δ) and Δ(id) = array(t,l,u) *)
      (NatMap.MapsTo id (Declared (Tarray t l u)) ed \/
       NatMap.MapsTo id (Output (Tarray t l u)) ed) -> 
      NatMap.MapsTo id (Vlist currlofv) (sigstore dstate) -> (* id ∈ σ and σ(id) = currlofv *)

      get_at i currlofv = Some currv -> (* Retrieves current value at index i of currlofv *)
      VEq newv currv (Some false) ->                (* new value <> current value *)

      (* - dstate = <S,C,E>, dstate' = <S',C,E'>
         - S' = S(id) ← set_at(newv, i, currlofv), E' = E ∪ {id} 
       *)
      set_at newv i currlofv = Some newlofv ->
      dstate' = (events_add id (sstore_add id (Vlist newlofv) dstate)) ->
      
      (* Conclusion *)
      vseq ed dstate lenv (id $[[ei]] @<== e) dstate' lenv

(** Evaluates a signal assignment statement.

    The target must be a declared signal or an out port identifier with an index.

    Case where the assignment generates no event. *)
           
| VSeqIdxSigAssignNoEvent :
    forall {id e ei newv i t l u currlofv currv},
      
      (* * Premises * *)
      vexpr ed dstate lenv e newv ->
      is_of_type newv t ->

      (* These two lines are equivalent to: ei ⇝ vi ∧ vi ∈c nat(l,u) *)
      vexpr ed dstate lenv ei (Vnat i) ->
      l <= i <= u ->
      
      (* Side conditions *)
      
      (* id ∈ Sigs(Δ) ∨ id ∈ Outs(Δ) and Δ(id) = array(t,l,u) *)
      (NatMap.MapsTo id (Declared (Tarray t l u)) ed \/
       NatMap.MapsTo id (Output (Tarray t l u)) ed) -> 
      NatMap.MapsTo id (Vlist currlofv) (sigstore dstate) -> (* id ∈ σ and σ(id) = currlofv *)

      get_at i currlofv = Some currv -> (* Current value at index [i] of [currlofv] is [currv] *)
      VEq newv currv (Some true) -> (* new value = current value *)
            
      (* Conclusion *)
      vseq ed dstate lenv (id $[[ei]] @<== e) dstate lenv
           
(** Evaluates a variable assignment statement.

    The target must be a variable identifier. *)
           
| VSeqVarAssign :
    forall {id e newv t currv},
      
      (* * Premises * *)
      vexpr ed dstate lenv e newv ->
      is_of_type newv t ->

      (* * Side conditions * *)
      NatMap.MapsTo id (t, currv) lenv -> (* id ∈ Λ and Λ(id) = (t, currv) *)
      
      (* * Conclusion * *)
      vseq ed dstate lenv ($id @:= e) dstate (NatMap.add id (t, newv) lenv)

(** Evaluates a variable assignment statement.

    The target must be a variable identifier with an index. *)
           
| VSeqIdxVarAssign :
    forall {id e ei newv i t l u currlofv newlofv},
      
      (* * Premises * *)
      vexpr ed dstate lenv e newv ->
      is_of_type newv t ->
      
      (* These two lines are equivalent to: ei ⇝ vi ∧ vi ∈c nat(l,u) *)
      vexpr ed dstate lenv ei (Vnat i) ->
      l <= i <= u ->      

      (* * Side conditions * *)
      
      (* id ∈ Λ and Λ(id) = (array(t, l, u), currlofv) *)
      NatMap.MapsTo id (Tarray t l u, (Vlist currlofv)) lenv ->
      set_at newv i currlofv = Some newlofv ->
      
      (* * Conclusion * *)
      vseq ed dstate lenv (id $[[ei]] @:= e) dstate (NatMap.add id (Tarray t l u, (Vlist newlofv)) lenv)

(** Evaluates a simple if statement with a true condition. *)

| VSeqIfTrue :
    forall {e stmt dstate' lenv'},
      
      (* * Premises * *)
      vexpr ed dstate lenv e (Vbool true) ->
      vseq ed dstate lenv stmt dstate' lenv' ->
      
      (* * Conclusion * *)
      vseq ed dstate lenv (If e Then stmt) dstate' lenv'

(** Evaluates a simple if statement with a false condition. *)

| VSeqIfFalse :
    forall {e stmt},
      
      (* * Premises * *)
      vexpr ed dstate lenv e (Vbool false) ->
      
      (* * Conclusion * *)
      vseq ed dstate lenv (If e Then stmt) dstate lenv

(** Evaluates a if-else statement with a true condition. *)

| VSeqIfElseTrue :
    forall {e stmt stmt' dstate' lenv'},
      
      (* * Premises * *)
      vexpr ed dstate lenv e (Vbool true) ->
      vseq ed dstate lenv stmt dstate' lenv' ->
      
      (* * Conclusion * *)
      vseq ed dstate lenv (If e Then stmt Else stmt') dstate' lenv'

(** Evaluates a if-else statement with a false condition. *)

| VSeqIfElseFalse :
    forall {e stmt stmt' dstate' lenv'},
      
      (* * Premises * *)
      vexpr ed dstate lenv e (Vbool false) ->
      vseq ed dstate lenv stmt' dstate' lenv' ->
      
      (* * Conclusion * *)
      vseq ed dstate lenv (If e Then stmt Else stmt') dstate' lenv'

(** Evaluates a loop statement.
    
    Initialization, add the loop variable to the local environment
    with initial value.  *)

| VSeqLoopInit :
    forall {id e e' stmt n n' lenvi dstate' lenv'},

      (* * Premises * *)
      vexpr ed dstate lenv e (Vnat n) ->
      vexpr ed dstate lenv e' (Vnat n') ->
      
      vseq ed dstate lenvi (For id In e To e' Loop stmt) dstate' lenv' ->

      (* * Side conditions * *)
      ~NatMap.In id lenv ->     (* id ∉ Λ *)
      lenvi = NatMap.add id (Tnat n n', Vnat n) lenv -> (* lenvi = lenv ∪ (id, (nat(n,n'), n)) *)

      (* * Conclusion * *)
      vseq ed dstate lenv (For id In e To e' Loop stmt) dstate' lenv'

(** Evaluates a loop statement.
    
    Case where the loop variable is already in the local environment
    (it is not the first iteration), but the upper bound value is not
    reached yet.  *)

| VSeqLoopFalse :
    forall {id e e' stmt t n lenvi dstate' lenv' dstate'' lenv''},

      (* * Premises * *)
      
      (* The upper bound is not reached. id = e' ⇝ ⊥ *)
      vexpr ed dstate lenvi (#id @= e') (Vbool false) ->
      vseq ed dstate lenvi stmt dstate' lenv' ->
      vseq ed dstate' lenv' (For id In e To e' Loop stmt) dstate'' lenv'' ->

      (* * Side conditions * *)
      NatMap.MapsTo id (t, Vnat n) lenv ->
      lenvi = NatMap.add id (t, Vnat (n + 1)) lenv ->

      (* * Conclusion * *)
      vseq ed dstate lenv (For id In e To e' Loop stmt) dstate'' lenv''
           
(** Evaluates a loop statement.
    
    Case where the loop variable is already in the local environment
    (it is not the first iteration), and the upper bound value is
    reached.  *)

| VSeqLoopTrue :
    forall {id e e' stmt t n lenvi},

      (* * Premises * *)
      vexpr ed dstate lenvi (e_binop bo_eq (e_name (n_id id)) e') (Vbool true) ->

      (* * Side conditions * *)
      NatMap.MapsTo id (t, Vnat n) lenv ->
      lenvi = NatMap.add id (t, Vnat (n + 1)) lenv ->

      (* * Conclusion * *)
      (* Removes the binding of id from the local environment. *)
      vseq ed dstate lenv (For id In e To e' Loop stmt) dstate (NatMap.remove id lenv)
           
(** Evaluates a rising edge block statement.

    Does nothing because [vseq] does not handle synchronous statement
    blocks. See [vseqfe] and [vseqre] for evaluation of synchronous
    statement blocks. *)
           
| VSeqRising : forall {stmt}, vseq ed dstate lenv (Rising stmt) dstate lenv

(** Evaluates a falling edge block statement.

    Does nothing because [vseq] does not handle synchronous statement
    blocks. See [vseqfe] and [vseqre] for evaluation of synchronous
    statement blocks. *)
                                   
| VSeqFalling : forall {stmt}, vseq ed dstate lenv (Falling stmt) dstate lenv

(** Evaluates a sequence of statements. *)

| VSeqSeq :
    forall {stmt stmt' dstate' lenv' dstate'' lenv''},
      
      (* * Premises * *)
      vseq ed dstate lenv stmt dstate' lenv' ->
      vseq ed dstate' lenv' stmt dstate'' lenv'' ->

      (* * Conclusion * *)
      vseq ed dstate lenv (stmt ;; stmt') dstate'' lenv''.
  
(** Defines the relation that evaluates the sequential statements of
    H-VHDL, including the rising edge block statements (only executed
    at the rising edge of the clock signal).  *)

Inductive vseqre (ed : ElDesign) (dstate : DState) (lenv : LEnv) : ss -> DState -> LEnv -> Prop :=

(** Evaluates a signal assignment statement. *)
  
| VSeqRESigAssign :
    forall {sname e dstate' lenv'},
      
      (* Premises *)
      vseq ed dstate lenv (ss_sig sname e) dstate' lenv' ->
           
      (* Conclusion *)
      vseqre ed dstate lenv (ss_sig sname e) dstate' lenv'
           
(** Evaluates a variable assignment statement.

    The target must be a variable identifier. *)
           
| VSeqREVarAssign :
    forall {vname e dstate' lenv'},
      
      (* Premises *)
      vseq ed dstate lenv (ss_sig vname e) dstate' lenv' ->
      
      (* Conclusion *)
      vseqre ed dstate lenv (ss_var vname e) dstate' lenv'

(** Evaluates a simple if statement with a true condition. *)

| VSeqREIfTrue :
    forall {e stmt dstate' lenv'},
      
      (* * Premises * *)
      vexpr ed dstate lenv e (Vbool true) ->
      vseqre ed dstate lenv stmt dstate' lenv' ->
      
      (* * Conclusion * *)
      vseqre ed dstate lenv (ss_if e stmt) dstate' lenv'

(** Evaluates a simple if statement with a false condition. *)

| VSeqREIfFalse :
    forall {e stmt},
      
      (* * Premises * *)
      vexpr ed dstate lenv e (Vbool false) ->
      
      (* * Conclusion * *)
      vseqre ed dstate lenv (ss_if e stmt) dstate lenv

(** Evaluates a if-else statement with a true condition. *)

| VSeqREIfElseTrue :
    forall {e stmt stmt' dstate' lenv'},
      
      (* * Premises * *)
      vexpr ed dstate lenv e (Vbool true) ->
      vseqre ed dstate lenv stmt dstate' lenv' ->
      
      (* * Conclusion * *)
      vseqre ed dstate lenv (ss_ifelse e stmt stmt') dstate' lenv'

(** Evaluates a if-else statement with a false condition. *)

| VSeqREIfElseFalse :
    forall {e stmt stmt' dstate' lenv'},
      
      (* * Premises * *)
      vexpr ed dstate lenv e (Vbool false) ->
      vseqre ed dstate lenv stmt' dstate' lenv' ->
      
      (* * Conclusion * *)
      vseqre ed dstate lenv (ss_ifelse e stmt stmt') dstate' lenv'
           

(** Evaluates a loop statement.
    
    Initialization, add the loop variable to the local environment
    with initial value.  *)

| VSeqRELoopInit :
    forall {id e e' stmt n n' lenvi dstate' lenv'},

      (* * Premises * *)
      vexpr ed dstate lenv e (Vnat n) ->
      vexpr ed dstate lenv e' (Vnat n') ->
      
      vseqre ed dstate lenvi (For id In e To e' Loop stmt) dstate' lenv' ->

      (* * Side conditions * *)
      ~NatMap.In id lenv ->     (* id ∉ Λ *)
      lenvi = NatMap.add id (Tnat n n', Vnat n) lenv -> (* lenvi = lenv ∪ (id, (nat(n,n'), n)) *)

      (* * Conclusion * *)
      vseqre ed dstate lenv (For id In e To e' Loop stmt) dstate' lenv'

(** Evaluates a loop statement.
    
    Case where the loop variable is already in the local environment
    (it is not the first iteration), but the upper bound value is not
    reached yet.  *)

| VSeqRELoopFalse :
    forall {id e e' stmt t n lenvi dstate' lenv' dstate'' lenv''},

      (* * Premises * *)
      
      (* The upper bound is not reached. id = e' ⇝ ⊥ *)
      vexpr ed dstate lenvi (e_binop bo_eq (e_name (n_id id)) e') (Vbool false) ->
      vseqre ed dstate lenvi stmt dstate' lenv' ->
      vseqre ed dstate' lenv' (For id In e To e' Loop stmt) dstate'' lenv'' ->

      (* * Side conditions * *)
      NatMap.MapsTo id (t, Vnat n) lenv ->
      lenvi = NatMap.add id (t, Vnat (n + 1)) lenv ->

      (* * Conclusion * *)
      vseqre ed dstate lenv (For id In e To e' Loop stmt) dstate'' lenv''
           
(** Evaluates a loop statement.
    
    Case where the loop variable is already in the local environment
    (it is not the first iteration), and the upper bound value is
    reached.  *)

| VSeqRELoopTrue :
    forall {id e e' stmt t n lenvi},

      (* * Premises * *)
      vexpr ed dstate lenvi (e_binop bo_eq (e_name (n_id id)) e') (Vbool true) ->

      (* * Side conditions * *)
      NatMap.MapsTo id (t, Vnat n) lenv ->
      lenvi = NatMap.add id (t, Vnat (n + 1)) lenv ->

      (* * Conclusion * *)
      (* Remove the binding of id from the local environment. *)
      vseqre ed dstate lenv (For id In e To e' Loop stmt) dstate (NatMap.remove id lenv)
           
(** Evaluates a rising edge block statement. 
    Contrary to [vseq], [vseqre] evaluates rising edge blocks.
 *)
           
| VSeqRERising :
    forall {stmt dstate' lenv'},
      (* * Premises * *)
      vseqre ed dstate lenv stmt dstate' lenv' ->

      (* * Conclusion * *)
      vseqre ed dstate lenv (ss_rising stmt) dstate' lenv'

(** Evaluates a falling edge block statement (do nothing). *)
                                   
| VSeqREFalling : forall {stmt}, vseqre ed dstate lenv (ss_falling stmt) dstate lenv

(** Evaluates a sequence of statements. *)

| VSeqRESeq :
    forall {stmt stmt' dstate' lenv' dstate'' lenv''},
      
      (* * Premises * *)
      vseqre ed dstate lenv stmt dstate' lenv' ->
      vseqre ed dstate' lenv' stmt dstate'' lenv'' ->

      (* * Conclusion * *)
      vseqre ed dstate lenv (ss_seq stmt stmt') dstate'' lenv''.

(** Defines the relation that evaluates the sequential statements of
    H-VHDL, including the falling edge block statements (only executed
    at the falling edge of the clock signal).  *)

Inductive vseqfe (ed : ElDesign) (dstate : DState) (lenv : LEnv) : ss -> DState -> LEnv -> Prop :=

(** Evaluates a signal assignment statement. *)
  
| VSeqFESigAssign :
    forall {sname e dstate' lenv'},
      
      (* Premises *)
      vseq ed dstate lenv (ss_sig sname e) dstate' lenv' ->
           
      (* Conclusion *)
      vseqfe ed dstate lenv (ss_sig sname e) dstate' lenv'
           
(** Evaluates a variable assignment statement.

    The target must be a variable identifier. *)
           
| VSeqFEVarAssign :
    forall {vname e dstate' lenv'},
      
      (* Premises *)
      vseq ed dstate lenv (ss_sig vname e) dstate' lenv' ->
      
      (* Conclusion *)
      vseqfe ed dstate lenv (ss_var vname e) dstate' lenv'

(** Evaluates a simple if statement with a true condition. *)

| VSeqFEIfTrue :
    forall {e stmt dstate' lenv'},
      
      (* * Premises * *)
      vexpr ed dstate lenv e (Vbool true) ->
      vseqfe ed dstate lenv stmt dstate' lenv' ->
      
      (* * Conclusion * *)
      vseqfe ed dstate lenv (ss_if e stmt) dstate' lenv'

(** Evaluates a simple if statement with a false condition. *)

| VSeqFEIfFalse :
    forall {e stmt},
      
      (* * Premises * *)
      vexpr ed dstate lenv e (Vbool false) ->
      
      (* * Conclusion * *)
      vseqfe ed dstate lenv (ss_if e stmt) dstate lenv

(** Evaluates a if-else statement with a true condition. *)

| VSeqFEIfElseTrue :
    forall {e stmt stmt' dstate' lenv'},
      
      (* * Premises * *)
      vexpr ed dstate lenv e (Vbool true) ->
      vseqfe ed dstate lenv stmt dstate' lenv' ->
      
      (* * Conclusion * *)
      vseqfe ed dstate lenv (ss_ifelse e stmt stmt') dstate' lenv'

(** Evaluates a if-else statement with a false condition. *)

| VSeqFEIfElseFalse :
    forall {e stmt stmt' dstate' lenv'},
      
      (* * Premises * *)
      vexpr ed dstate lenv e (Vbool false) ->
      vseqfe ed dstate lenv stmt' dstate' lenv' ->
      
      (* * Conclusion * *)
      vseqfe ed dstate lenv (ss_ifelse e stmt stmt') dstate' lenv'
           

(** Evaluates a loop statement.
    
    Initialization, add the loop variable to the local environment
    with initial value.  *)

| VSeqFELoopInit :
    forall {id e e' stmt n n' lenvi dstate' lenv'},

      (* * Premises * *)
      vexpr ed dstate lenv e (Vnat n) ->
      vexpr ed dstate lenv e' (Vnat n') ->
      
      vseqfe ed dstate lenvi (For id In e To e' Loop stmt) dstate' lenv' ->

      (* * Side conditions * *)
      ~NatMap.In id lenv ->     (* id ∉ Λ *)
      lenvi = NatMap.add id (Tnat n n', Vnat n) lenv -> (* lenvi = lenv ∪ (id, (nat(n,n'), n)) *)

      (* * Conclusion * *)
      vseqfe ed dstate lenv (For id In e To e' Loop stmt) dstate' lenv'

(** Evaluates a loop statement.
    
    Case where the loop variable is already in the local environment
    (it is not the first iteration), but the upper bound value is not
    reached yet.  *)

| VSeqFELoopFalse :
    forall {id e e' stmt t n lenvi dstate' lenv' dstate'' lenv''},

      (* * Premises * *)
      
      (* The upper bound is not reached. id = e' ⇝ ⊥ *)
      vexpr ed dstate lenvi (e_binop bo_eq (e_name (n_id id)) e') (Vbool false) ->
      vseqfe ed dstate lenvi stmt dstate' lenv' ->
      vseqfe ed dstate' lenv' (For id In e To e' Loop stmt) dstate'' lenv'' ->

      (* * Side conditions * *)
      NatMap.MapsTo id (t, Vnat n) lenv ->
      lenvi = NatMap.add id (t, Vnat (n + 1)) lenv ->

      (* * Conclusion * *)
      vseqfe ed dstate lenv (For id In e To e' Loop stmt) dstate'' lenv''
           
(** Evaluates a loop statement.
    
    Case where the loop variable is already in the local environment
    (it is not the first iteration), and the upper bound value is
    reached.  *)

| VSeqFELoopTrue :
    forall {id e e' stmt t n lenvi},

      (* * Premises * *)
      vexpr ed dstate lenvi (e_binop bo_eq (e_name (n_id id)) e') (Vbool true) ->

      (* * Side conditions * *)
      NatMap.MapsTo id (t, Vnat n) lenv ->
      lenvi = NatMap.add id (t, Vnat (n + 1)) lenv ->

      (* * Conclusion * *)
      (* Remove the binding of id from the local environment. *)
      vseqfe ed dstate lenv (For id In e To e' Loop stmt) dstate (NatMap.remove id lenv)
           
(** Evaluates a falling edge block statement.  Contrary to [vseq] and
    [vseqre], [vseqfe] evaluates falling edge blocks.  *)
           
| VSeqFEFalling :
    forall {stmt dstate' lenv'},
      (* * Premises * *)
      vseqfe ed dstate lenv stmt dstate' lenv' ->

      (* * Conclusion * *)
      vseqfe ed dstate lenv (ss_falling stmt) dstate' lenv'

(** Evaluates a rising edge block statement (does nothing). *)
                                   
| VSeqFERising : forall {stmt}, vseqfe ed dstate lenv (ss_rising stmt) dstate lenv

(** Evaluates a sequence of statements. *)

| VSeqFESeq :
    forall {stmt stmt' dstate' lenv' dstate'' lenv''},
      
      (* * Premises * *)
      vseqfe ed dstate lenv stmt dstate' lenv' ->
      vseqfe ed dstate' lenv' stmt dstate'' lenv'' ->

      (* * Conclusion * *)
      vseqfe ed dstate lenv (ss_seq stmt stmt') dstate'' lenv''.
