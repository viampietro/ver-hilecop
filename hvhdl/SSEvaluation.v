(** * Evaluation of sequential statements. *)

Require Import Environment.
Require Import AbstractSyntax.
Require Import IsOfType.
Require Import ExpressionEvaluation.
Require Import SemanticalDomains.

(** Defines the relation that evaluates the sequential statements
    of H-VHDL. 
    
    [vseq] does not define error cases.
 *)

Inductive vseq (denv : DEnv) (dstate : DState) (lenv : LEnv) : ss -> DState -> LEnv -> Prop :=

(** Evaluates a signal assignment statement.

    The target must be a declared signal or a out port identifier.

    Case where the assignment generates an event (i.e, a change of
    value). *)
  
| VSeqSigAssignEvent :
    forall {id e v t v' sigstore' events'},
      
      (* Premises *)
      vexpr denv dstate lenv e v ->
      is_of_type v t ->

      (* Side conditions *)
      (NatMap.MapsTo id (Declared t) denv \/
       NatMap.MapsTo id (Output t) denv) -> (* id ∈ Sigs(Δ) ∨ id ∈ Outs(Δ) and Δ(id) = t *)
      NatMap.MapsTo id v' (sigstore dstate) -> (* id ∈ σ and σ(id) = v' *)
      sigstore' = (NatMap.add id v (sigstore dstate)) -> (* S' = S(id) ← v  *)
      
      ~VEq v v' ->                                 (* new value <> current value *)
      events' = (NatSet.add id (events dstate)) -> (* E' = E ∪ {id} *)
      
      (* Conclusion *)
      vseq denv dstate lenv (ss_sig (n_id id) e) (MkDState sigstore' (compstore dstate) events') lenv

(** Evaluates a signal assignment statement.

    The target must be a declared signal or an out port identifier.

    Case where the assignment generates no event. *)
  
| VSeqSigAssignNoEvent :
    forall {id e v t v'},
      
      (* Premises *)
      vexpr denv dstate lenv e v ->
      is_of_type v t ->

      (* Side conditions *)
      (NatMap.MapsTo id (Declared t) denv \/
       NatMap.MapsTo id (Output t) denv) ->    (* id ∈ Sigs(Δ) ∨ id ∈ Outs(Δ) and Δ(id) = t *)
      NatMap.MapsTo id v' (sigstore dstate) -> (* id ∈ σ and σ(id) = v' *)
      VEq v v' ->                              (* new value = current value *)
      
      (* Conclusion *)
      vseq denv dstate lenv (ss_sig (n_id id) e) dstate lenv

(** Evaluates a signal assignment statement.

    The target must be a declared signal or a out port identifier with an index.

    Case where the assignment generates an event (i.e, a change of
    value). *)
           
| VSeqIdxSigAssignEvent :
    forall {id e ei v i t l u lofv v' lofv' sigstore' events'},
      
      (* Premises *)
      vexpr denv dstate lenv e v ->
      is_of_type v t ->

      (* These two lines are equivalent to: ei ⇝ vi ∧ vi ∈c nat(l,u) *)
      vexpr denv dstate lenv ei (Vnat i) ->
      l <= i <= u ->
        
      (* Side conditions *)
      
      (* id ∈ Sigs(Δ) ∨ id ∈ Outs(Δ) and Δ(id) = array(t,l,u) *)
      (NatMap.MapsTo id (Declared (Tarray t l u)) denv \/
       NatMap.MapsTo id (Output (Tarray t l u)) denv) -> 
      NatMap.MapsTo id (Vlist lofv) (sigstore dstate) -> (* id ∈ σ and σ(id) = v' *)

      get_at i lofv = Some v' ->                   (* Current value at index i of lofv is v' *)
      ~VEq v v' ->                                 (* new value <> current value *)
      events' = (NatSet.add id (events dstate)) -> (* E' = E ∪ {id} *)
      
      (* S' = S(id) ← set_at(v, i, lofv) *)
      set_at v i lofv = Some lofv' ->
      sigstore' = (NatMap.add id (Vlist lofv') (sigstore dstate)) ->     
      
      (* Conclusion *)
      vseq denv dstate lenv (ss_sig (n_xid id ei) e) (MkDState sigstore' (compstore dstate) events') lenv

(** Evaluates a signal assignment statement.

    The target must be a declared signal or an out port identifier with an index.

    Case where the assignment generates no event. *)
           
| VSeqIdxSigAssignNoEvent :
    forall {id e ei v i t l u lofv v'},
      
      (* Premises *)
      vexpr denv dstate lenv e v ->
      is_of_type v t ->

      (* These two lines are equivalent to: ei ⇝ vi ∧ vi ∈c nat(l,u) *)
      vexpr denv dstate lenv ei (Vnat i) ->
      l <= i <= u ->
      
      (* Side conditions *)
      
      (* id ∈ Sigs(Δ) ∨ id ∈ Outs(Δ) and Δ(id) = array(t,l,u) *)
      (NatMap.MapsTo id (Declared (Tarray t l u)) denv \/
       NatMap.MapsTo id (Output (Tarray t l u)) denv) -> 
      NatMap.MapsTo id (Vlist lofv) (sigstore dstate) -> (* id ∈ σ and σ(id) = v' *)

      get_at i lofv = Some v' -> (* Current value at index [i] of [lofv] is [v'] *)
      VEq v v' ->                (* new value <> current value *)
            
      (* Conclusion *)
      vseq denv dstate lenv (ss_sig (n_xid id ei) e) dstate lenv
           
(** Evaluates a variable assignment statement.

    The target must be a variable identifier. *)
           
| VSeqVarAssign :
    forall {id e v t val},
      
      (* Premises *)
      vexpr denv dstate lenv e v ->
      is_of_type v t ->

      (* Side conditions *)
      NatMap.MapsTo id (t, val) lenv -> (* id ∈ Λ and Λ(id) = (t, val) *)
      
      (* Conclusion *)
      vseq denv dstate lenv (ss_var (n_id id) e) dstate (NatMap.add id (t, v) lenv)

(** Evaluates a variable assignment statement.

    The target must be a variable identifier with an index. *)
           
| VSeqIdxVarAssign :
    forall {id e ei v i t l u lofv lofv'},
      
      (* * Premises * *)
      vexpr denv dstate lenv e v ->
      is_of_type v t ->
      
      (* These two lines are equivalent to: ei ⇝ vi ∧ vi ∈c nat(l,u) *)
      vexpr denv dstate lenv ei (Vnat i) ->
      l <= i <= u ->      

      (* * Side conditions * *)
      
      (* id ∈ Λ and Λ(id) = (array(t, l, u), lofv) *)
      NatMap.MapsTo id (Tarray t l u, (Vlist lofv)) lenv ->
      set_at v i lofv = Some lofv' ->
      
      (* * Conclusion * *)
      vseq denv dstate lenv (ss_var (n_xid id ei) e) dstate (NatMap.add id (Tarray t l u, (Vlist lofv')) lenv)

(** Evaluates a simple if statement with a true condition. *)

| VSeqIfTrue :
    forall {e stmt dstate' lenv'},
      
      (* * Premises * *)
      vexpr denv dstate lenv e (Vbool true) ->
      vseq denv dstate lenv stmt dstate' lenv' ->
      
      (* * Conclusion * *)
      vseq denv dstate lenv (ss_if e stmt) dstate' lenv'

(** Evaluates a simple if statement with a false condition. *)

| VSeqIfFalse :
    forall {e stmt},
      
      (* * Premises * *)
      vexpr denv dstate lenv e (Vbool false) ->
      
      (* * Conclusion * *)
      vseq denv dstate lenv (ss_if e stmt) dstate lenv

(** Evaluates a if-else statement with a true condition. *)

| VSeqIfElseTrue :
    forall {e stmt stmt' dstate' lenv'},
      
      (* * Premises * *)
      vexpr denv dstate lenv e (Vbool true) ->
      vseq denv dstate lenv stmt dstate' lenv' ->
      
      (* * Conclusion * *)
      vseq denv dstate lenv (ss_ifelse e stmt stmt') dstate' lenv'

(** Evaluates a if-else statement with a false condition. *)

| VSeqIfElseFalse :
    forall {e stmt stmt' dstate' lenv'},
      
      (* * Premises * *)
      vexpr denv dstate lenv e (Vbool false) ->
      vseq denv dstate lenv stmt' dstate' lenv' ->
      
      (* * Conclusion * *)
      vseq denv dstate lenv (ss_ifelse e stmt stmt') dstate' lenv'
           

(** Evaluates a loop statement.
    
    Initialization, add the loop variable to the local environment
    with initial value.  *)

| VSeqLoopInit :
    forall {id e e' stmt n n' lenvi dstate' lenv'},

      (* * Premises * *)
      vexpr denv dstate lenv e (Vnat n) ->
      vexpr denv dstate lenv e' (Vnat n') ->
      
      vseq denv dstate lenvi (ss_loop id e e' stmt) dstate' lenv' ->

      (* * Side conditions * *)
      ~NatMap.In id lenv ->     (* id ∉ Λ *)
      lenvi = NatMap.add id (Tnat n n', Vnat n) lenv -> (* lenvi = lenv ∪ (id, (nat(n,n'), n)) *)

      (* * Conclusion * *)
      vseq denv dstate lenv (ss_loop id e e' stmt) dstate' lenv'

(** Evaluates a loop statement.
    
    Case where the loop variable is already in the local environment
    (it is not the first iteration), but the upper bound value is not
    reached yet.  *)

| VSeqLoopFalse :
    forall {id e e' stmt t n lenvi dstate' lenv' dstate'' lenv''},

      (* * Premises * *)
      
      (* The upper bound is not reached. id = e' ⇝ ⊥ *)
      vexpr denv dstate lenvi (e_binop bo_eq (e_name (n_id id)) e') (Vbool false) ->
      vseq denv dstate lenvi stmt dstate' lenv' ->
      vseq denv dstate' lenv' (ss_loop id e e' stmt) dstate'' lenv'' ->

      (* * Side conditions * *)
      NatMap.MapsTo id (t, Vnat n) lenv ->
      lenvi = NatMap.add id (t, Vnat (n + 1)) lenv ->

      (* * Conclusion * *)
      vseq denv dstate lenv (ss_loop id e e' stmt) dstate'' lenv''
           
(** Evaluates a loop statement.
    
    Case where the loop variable is already in the local environment
    (it is not the first iteration), and the upper bound value is
    reached.  *)

| VSeqLoopTrue :
    forall {id e e' stmt t n lenvi},

      (* * Premises * *)
      vexpr denv dstate lenvi (e_binop bo_eq (e_name (n_id id)) e') (Vbool true) ->

      (* * Side conditions * *)
      NatMap.MapsTo id (t, Vnat n) lenv ->
      lenvi = NatMap.add id (t, Vnat (n + 1)) lenv ->

      (* * Conclusion * *)
      (* Remove the binding of id from the local environment. *)
      vseq denv dstate lenv (ss_loop id e e' stmt) dstate (NatMap.remove id lenv)
           
(** Evaluates a rising edge block statement.

    Does nothing because [vseq] does not handle synchronous statement
    blocks. See [vseqfe] and [vseqre] for evaluation of synchronous
    statement blocks. *)
           
| VSeqRising : forall {stmt}, vseq denv dstate lenv (ss_rising stmt) dstate lenv

(** Evaluates a falling edge block statement.

    Does nothing because [vseq] does not handle synchronous statement
    blocks. See [vseqfe] and [vseqre] for evaluation of synchronous
    statement blocks. *)
                                   
| VSeqFalling : forall {stmt}, vseq denv dstate lenv (ss_falling stmt) dstate lenv

(** Evaluates a sequence of statements. *)

| VSeqSeq :
    forall {stmt stmt' dstate' lenv' dstate'' lenv''},
      
      (* * Premises * *)
      vseq denv dstate lenv stmt dstate' lenv' ->
      vseq denv dstate' lenv' stmt dstate'' lenv'' ->

      (* * Conclusion * *)
      vseq denv dstate lenv (stmt;; stmt') dstate'' lenv''.
  
(** Defines the relation that evaluates the sequential statements of
    H-VHDL, including the rising edge block statements (only executed
    at the rising edge of the clock signal).  *)

Inductive vseqre (denv : DEnv) (dstate : DState) (lenv : LEnv) : ss -> DState -> LEnv -> Prop :=

(** Evaluates a signal assignment statement. *)
  
| VSeqRESigAssign :
    forall {sname e dstate' lenv'},
      
      (* Premises *)
      vseq denv dstate lenv (ss_sig sname e) dstate' lenv' ->
           
      (* Conclusion *)
      vseqre denv dstate lenv (ss_sig sname e) dstate' lenv'
           
(** Evaluates a variable assignment statement.

    The target must be a variable identifier. *)
           
| VSeqREVarAssign :
    forall {vname e dstate' lenv'},
      
      (* Premises *)
      vseq denv dstate lenv (ss_sig vname e) dstate' lenv' ->
      
      (* Conclusion *)
      vseqre denv dstate lenv (ss_var vname e) dstate' lenv'

(** Evaluates a simple if statement with a true condition. *)

| VSeqREIfTrue :
    forall {e stmt dstate' lenv'},
      
      (* * Premises * *)
      vexpr denv dstate lenv e (Vbool true) ->
      vseqre denv dstate lenv stmt dstate' lenv' ->
      
      (* * Conclusion * *)
      vseqre denv dstate lenv (ss_if e stmt) dstate' lenv'

(** Evaluates a simple if statement with a false condition. *)

| VSeqREIfFalse :
    forall {e stmt},
      
      (* * Premises * *)
      vexpr denv dstate lenv e (Vbool false) ->
      
      (* * Conclusion * *)
      vseqre denv dstate lenv (ss_if e stmt) dstate lenv

(** Evaluates a if-else statement with a true condition. *)

| VSeqREIfElseTrue :
    forall {e stmt stmt' dstate' lenv'},
      
      (* * Premises * *)
      vexpr denv dstate lenv e (Vbool true) ->
      vseqre denv dstate lenv stmt dstate' lenv' ->
      
      (* * Conclusion * *)
      vseqre denv dstate lenv (ss_ifelse e stmt stmt') dstate' lenv'

(** Evaluates a if-else statement with a false condition. *)

| VSeqREIfElseFalse :
    forall {e stmt stmt' dstate' lenv'},
      
      (* * Premises * *)
      vexpr denv dstate lenv e (Vbool false) ->
      vseqre denv dstate lenv stmt' dstate' lenv' ->
      
      (* * Conclusion * *)
      vseqre denv dstate lenv (ss_ifelse e stmt stmt') dstate' lenv'
           

(** Evaluates a loop statement.
    
    Initialization, add the loop variable to the local environment
    with initial value.  *)

| VSeqRELoopInit :
    forall {id e e' stmt n n' lenvi dstate' lenv'},

      (* * Premises * *)
      vexpr denv dstate lenv e (Vnat n) ->
      vexpr denv dstate lenv e' (Vnat n') ->
      
      vseqre denv dstate lenvi (ss_loop id e e' stmt) dstate' lenv' ->

      (* * Side conditions * *)
      ~NatMap.In id lenv ->     (* id ∉ Λ *)
      lenvi = NatMap.add id (Tnat n n', Vnat n) lenv -> (* lenvi = lenv ∪ (id, (nat(n,n'), n)) *)

      (* * Conclusion * *)
      vseqre denv dstate lenv (ss_loop id e e' stmt) dstate' lenv'

(** Evaluates a loop statement.
    
    Case where the loop variable is already in the local environment
    (it is not the first iteration), but the upper bound value is not
    reached yet.  *)

| VSeqRELoopFalse :
    forall {id e e' stmt t n lenvi dstate' lenv' dstate'' lenv''},

      (* * Premises * *)
      
      (* The upper bound is not reached. id = e' ⇝ ⊥ *)
      vexpr denv dstate lenvi (e_binop bo_eq (e_name (n_id id)) e') (Vbool false) ->
      vseqre denv dstate lenvi stmt dstate' lenv' ->
      vseqre denv dstate' lenv' (ss_loop id e e' stmt) dstate'' lenv'' ->

      (* * Side conditions * *)
      NatMap.MapsTo id (t, Vnat n) lenv ->
      lenvi = NatMap.add id (t, Vnat (n + 1)) lenv ->

      (* * Conclusion * *)
      vseqre denv dstate lenv (ss_loop id e e' stmt) dstate'' lenv''
           
(** Evaluates a loop statement.
    
    Case where the loop variable is already in the local environment
    (it is not the first iteration), and the upper bound value is
    reached.  *)

| VSeqRELoopTrue :
    forall {id e e' stmt t n lenvi},

      (* * Premises * *)
      vexpr denv dstate lenvi (e_binop bo_eq (e_name (n_id id)) e') (Vbool true) ->

      (* * Side conditions * *)
      NatMap.MapsTo id (t, Vnat n) lenv ->
      lenvi = NatMap.add id (t, Vnat (n + 1)) lenv ->

      (* * Conclusion * *)
      (* Remove the binding of id from the local environment. *)
      vseqre denv dstate lenv (ss_loop id e e' stmt) dstate (NatMap.remove id lenv)
           
(** Evaluates a rising edge block statement. 
    Contrary to [vseq], [vseqre] evaluates rising edge blocks.
 *)
           
| VSeqRERising :
    forall {stmt dstate' lenv'},
      (* * Premises * *)
      vseqre denv dstate lenv stmt dstate' lenv' ->

      (* * Conclusion * *)
      vseqre denv dstate lenv (ss_rising stmt) dstate' lenv'

(** Evaluates a falling edge block statement (do nothing). *)
                                   
| VSeqREFalling : forall {stmt}, vseqre denv dstate lenv (ss_falling stmt) dstate lenv

(** Evaluates a sequence of statements. *)

| VSeqRESeq :
    forall {stmt stmt' dstate' lenv' dstate'' lenv''},
      
      (* * Premises * *)
      vseqre denv dstate lenv stmt dstate' lenv' ->
      vseqre denv dstate' lenv' stmt dstate'' lenv'' ->

      (* * Conclusion * *)
      vseqre denv dstate lenv (stmt;; stmt') dstate'' lenv''.

(** Defines the relation that evaluates the sequential statements of
    H-VHDL, including the falling edge block statements (only executed
    at the falling edge of the clock signal).  *)

Inductive vseqfe (denv : DEnv) (dstate : DState) (lenv : LEnv) : ss -> DState -> LEnv -> Prop :=

(** Evaluates a signal assignment statement. *)
  
| VSeqFESigAssign :
    forall {sname e dstate' lenv'},
      
      (* Premises *)
      vseq denv dstate lenv (ss_sig sname e) dstate' lenv' ->
           
      (* Conclusion *)
      vseqfe denv dstate lenv (ss_sig sname e) dstate' lenv'
           
(** Evaluates a variable assignment statement.

    The target must be a variable identifier. *)
           
| VSeqFEVarAssign :
    forall {vname e dstate' lenv'},
      
      (* Premises *)
      vseq denv dstate lenv (ss_sig vname e) dstate' lenv' ->
      
      (* Conclusion *)
      vseqfe denv dstate lenv (ss_var vname e) dstate' lenv'

(** Evaluates a simple if statement with a true condition. *)

| VSeqFEIfTrue :
    forall {e stmt dstate' lenv'},
      
      (* * Premises * *)
      vexpr denv dstate lenv e (Vbool true) ->
      vseqfe denv dstate lenv stmt dstate' lenv' ->
      
      (* * Conclusion * *)
      vseqfe denv dstate lenv (ss_if e stmt) dstate' lenv'

(** Evaluates a simple if statement with a false condition. *)

| VSeqFEIfFalse :
    forall {e stmt},
      
      (* * Premises * *)
      vexpr denv dstate lenv e (Vbool false) ->
      
      (* * Conclusion * *)
      vseqfe denv dstate lenv (ss_if e stmt) dstate lenv

(** Evaluates a if-else statement with a true condition. *)

| VSeqFEIfElseTrue :
    forall {e stmt stmt' dstate' lenv'},
      
      (* * Premises * *)
      vexpr denv dstate lenv e (Vbool true) ->
      vseqfe denv dstate lenv stmt dstate' lenv' ->
      
      (* * Conclusion * *)
      vseqfe denv dstate lenv (ss_ifelse e stmt stmt') dstate' lenv'

(** Evaluates a if-else statement with a false condition. *)

| VSeqFEIfElseFalse :
    forall {e stmt stmt' dstate' lenv'},
      
      (* * Premises * *)
      vexpr denv dstate lenv e (Vbool false) ->
      vseqfe denv dstate lenv stmt' dstate' lenv' ->
      
      (* * Conclusion * *)
      vseqfe denv dstate lenv (ss_ifelse e stmt stmt') dstate' lenv'
           

(** Evaluates a loop statement.
    
    Initialization, add the loop variable to the local environment
    with initial value.  *)

| VSeqFELoopInit :
    forall {id e e' stmt n n' lenvi dstate' lenv'},

      (* * Premises * *)
      vexpr denv dstate lenv e (Vnat n) ->
      vexpr denv dstate lenv e' (Vnat n') ->
      
      vseqfe denv dstate lenvi (ss_loop id e e' stmt) dstate' lenv' ->

      (* * Side conditions * *)
      ~NatMap.In id lenv ->     (* id ∉ Λ *)
      lenvi = NatMap.add id (Tnat n n', Vnat n) lenv -> (* lenvi = lenv ∪ (id, (nat(n,n'), n)) *)

      (* * Conclusion * *)
      vseqfe denv dstate lenv (ss_loop id e e' stmt) dstate' lenv'

(** Evaluates a loop statement.
    
    Case where the loop variable is already in the local environment
    (it is not the first iteration), but the upper bound value is not
    reached yet.  *)

| VSeqFELoopFalse :
    forall {id e e' stmt t n lenvi dstate' lenv' dstate'' lenv''},

      (* * Premises * *)
      
      (* The upper bound is not reached. id = e' ⇝ ⊥ *)
      vexpr denv dstate lenvi (e_binop bo_eq (e_name (n_id id)) e') (Vbool false) ->
      vseqfe denv dstate lenvi stmt dstate' lenv' ->
      vseqfe denv dstate' lenv' (ss_loop id e e' stmt) dstate'' lenv'' ->

      (* * Side conditions * *)
      NatMap.MapsTo id (t, Vnat n) lenv ->
      lenvi = NatMap.add id (t, Vnat (n + 1)) lenv ->

      (* * Conclusion * *)
      vseqfe denv dstate lenv (ss_loop id e e' stmt) dstate'' lenv''
           
(** Evaluates a loop statement.
    
    Case where the loop variable is already in the local environment
    (it is not the first iteration), and the upper bound value is
    reached.  *)

| VSeqFELoopTrue :
    forall {id e e' stmt t n lenvi},

      (* * Premises * *)
      vexpr denv dstate lenvi (e_binop bo_eq (e_name (n_id id)) e') (Vbool true) ->

      (* * Side conditions * *)
      NatMap.MapsTo id (t, Vnat n) lenv ->
      lenvi = NatMap.add id (t, Vnat (n + 1)) lenv ->

      (* * Conclusion * *)
      (* Remove the binding of id from the local environment. *)
      vseqfe denv dstate lenv (ss_loop id e e' stmt) dstate (NatMap.remove id lenv)
           
(** Evaluates a falling edge block statement.  Contrary to [vseq] and
    [vseqre], [vseqfe] evaluates falling edge blocks.  *)
           
| VSeqFEFalling :
    forall {stmt dstate' lenv'},
      (* * Premises * *)
      vseqfe denv dstate lenv stmt dstate' lenv' ->

      (* * Conclusion * *)
      vseqfe denv dstate lenv (ss_falling stmt) dstate' lenv'

(** Evaluates a rising edge block statement (does nothing). *)
                                   
| VSeqFERising : forall {stmt}, vseqfe denv dstate lenv (ss_rising stmt) dstate lenv

(** Evaluates a sequence of statements. *)

| VSeqFESeq :
    forall {stmt stmt' dstate' lenv' dstate'' lenv''},
      
      (* * Premises * *)
      vseqfe denv dstate lenv stmt dstate' lenv' ->
      vseqfe denv dstate' lenv' stmt dstate'' lenv'' ->

      (* * Conclusion * *)
      vseqfe denv dstate lenv (stmt;; stmt') dstate'' lenv''.
