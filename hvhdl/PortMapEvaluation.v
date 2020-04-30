(** * Port map evaluation relation. *)

(** Defines the relation that evaluates in and out port maps.

    States that the evaluation of a "in" port map entry (resp. "out"
    port map entry) transforms the state of the component instance
    (resp. the embedding design) in a certain manner. *)

Require Import Coqlib.
Require Import GlobalTypes.
Require Import NatSet.
Require Import NatMap.
Require Import SemanticalDomains.
Require Import Environment.
Require Import AbstractSyntax.
Require Import ExpressionEvaluation.

(** Defines the evaluation relation for "in" port maps, i.e, port maps
    relating ports in "in" mode to expressions.
    
    The evaluation of an "in" port map affects the current state of
    the component instance to which the port map is related. *)

Inductive mapip (denv cenv : DEnv) (dstate cstate : DState) : list associp -> DState -> Prop := 

(** An empty list of port associations does not change the state
    [cstate] of the component instance. *)
| MapipNil : mapip denv cenv dstate cstate [] cstate 

(** Evaluates a non-empty list of port associations. *)
| MapipCons :
    forall {asip lofasips cstate' cstate''},
      vassocip denv cenv dstate cstate asip cstate' ->
      mapip denv cenv dstate cstate' lofasips cstate'' ->
      mapip denv cenv dstate cstate (asip :: lofasips) cstate''

(** Defines the relation that evaluates a single association present
    in an "in" port map.  *)
with vassocip (denv cenv : DEnv) (dstate cstate : DState) : associp -> DState -> Prop := 

(** Evaluates a "in" port map association, with a simple port
    identifier in the formal part.
    
    Case where the evaluation generates an event, i.e a change of
    value for the considered port identifier.  *)
  
| VAssocipSimpleEvent :
    forall {id e newv currv t sigstore' events'},
      
      (* * Premises * *)
      vexpr denv dstate EmptyLEnv e newv ->
      is_of_type newv t ->

      (* * Side conditions (where σc = <S,C,E>) * *)
      NatMap.MapsTo id (Input t) cenv ->         (* id ∈ Ins(Δc) and Δc(id) = t *)
      NatMap.MapsTo id currv (sigstore cstate) -> (* id ∈ σc and σc(id) = v' *)

      VEq newv currv (Some false) -> (* new value <> current value *)
      sigstore' = (NatMap.add id newv (sigstore cstate)) -> (* S' = S(id) ← v  *)
      events' = (NatSet.add id (events cstate)) -> (* E' = E ∪ {id} *)
      
      (* * Conclusion * *)
      vassocip denv cenv dstate cstate (associp_ (n_id id) e) (MkDState sigstore' (compstore cstate) events')

(** Evaluates a "in" port map association, with a simple port
    identifier in the formal part.
    
    Case where no event are generated.  *)
  
| VAssocipSimpleNoEvent :
    forall {id e newv currv t},
      
      (* * Premises * *)
      vexpr denv dstate EmptyLEnv e newv ->
      is_of_type newv t ->

      (* * Side conditions (where σc = <S,C,E>) * *)
      NatMap.MapsTo id (Input t) cenv ->         (* id ∈ Ins(Δc) and Δc(id) = t *)
      NatMap.MapsTo id currv (sigstore cstate) -> (* id ∈ σc and σc(id) = v' *)

      VEq newv currv (Some true) -> (* new value = current value *)
            
      (* * Conclusion * *)
      vassocip denv cenv dstate cstate (associp_ (n_id id) e) cstate

(** Evaluates a "in" port map association, with an indexed port
    identifier in the formal part.
    
    Case where the evaluation generates an event, i.e a change of
    value for the considered port identifier.  *)
  
| VAssocipPartialEvent :
    forall {id e ei newv i t l u lofv currv lofv' sigstore' events'},
      
      (* * Premises * *)
      vexpr denv dstate EmptyLEnv e newv ->
      is_of_type newv t ->

      (* These two lines are equivalent to: ei ⇝ vi ∧ vi ∈c nat(l,u) *)
      vexpr EmptyDEnv EmptyDState EmptyLEnv ei (Vnat i) ->
      l <= i <= u ->
        
      (* * Side conditions * *)
      NatMap.MapsTo id (Input (Tarray t l u)) cenv ->    (* id ∈ Ins(Δc) and Δc(id) = array(t,l,u) *)
      NatMap.MapsTo id (Vlist lofv) (sigstore cstate) -> (* id ∈ σ and σ(id) = v' *)

      get_at i lofv = Some currv -> (* Current value at index [i] of [lofv] is [currv] *)
      VEq newv currv (Some false) -> (* new value <> current value *)
      events' = NatSet.add id (events dstate) -> (* E' = E ∪ {id} *)
      
      (* S' = S(id) ← set_at(v, i, lofv) *)
      set_at newv i lofv = Some lofv' ->
      sigstore' = NatMap.add id (Vlist lofv') (sigstore dstate) ->
      
      (* * Conclusion * *)
      vassocip denv cenv dstate cstate (associp_ (n_xid id ei) e) (MkDState sigstore' (compstore cstate) events')

(** Evaluates a "in" port map association, with an indexed port
    identifier in the formal part.
    
    Case where the evaluation generates no event.  *)
               
| VAssocipPartialNoEvent :
    forall {id e ei newv i t l u lofv currv},
      
      (* * Premises * *)
      vexpr denv dstate EmptyLEnv e newv ->
      is_of_type newv t ->

      (* These two lines are equivalent to: ei ⇝ vi ∧ vi ∈c nat(l,u) *)
      vexpr EmptyDEnv EmptyDState EmptyLEnv ei (Vnat i) ->
      l <= i <= u ->
      
      (* * Side conditions * *)
      NatMap.MapsTo id (Input (Tarray t l u)) cenv ->    (* id ∈ Ins(Δc) and Δc(id) = array(t,l,u) *)
      NatMap.MapsTo id (Vlist lofv) (sigstore cstate) -> (* id ∈ σ and σ(id) = v' *)

      get_at i lofv = Some currv -> (* Current value at index [i] of [lofv] is [currv] *)
      VEq newv currv (Some true) -> (* new value = current value *)
            
      (* * Conclusion * *)
      vassocip denv cenv dstate cstate (associp_ (n_xid id ei) e) cstate.

    
(** Defines the evaluation relation for "out" port maps, i.e, port
    maps relating ports in "out" mode to other out ports or declared
    signals.
    
    The evaluation of an "out" port map affects the current state
    [dstate] of the embedding design. *)

Inductive mapop (denv cenv : DEnv) (dstate cstate : DState) : list assocop -> DState -> Prop :=

(** An empty list of port associations does not change the state
    [dstate] of the embedding design. *)
  
| MapopNil : mapop denv cenv dstate cstate [] cstate 

(** Evaluates a non-empty list of port associations. *)
| MapopCons :
    forall {asop lofasops dstate' dstate''},
      vassocop denv cenv dstate cstate asop dstate' ->
      mapop denv cenv dstate' cstate lofasops dstate'' ->
      mapop denv cenv dstate cstate (asop :: lofasops) dstate''

(** Defines the relation that evaluates a single association present
    in an "out" port map.  *)
with vassocop (denv cenv : DEnv) (dstate cstate : DState) : assocop -> DState -> Prop :=

(** Evaluates an association where the formal part is not bound, i.e
    the actual part is [None] (the "open" keyword is used in concrete
    VHDL syntax) *)
| VAssocopOpen : forall {pname}, vassocop denv cenv dstate cstate (assocop_ pname None) dstate

(** Evaluates an out port map association where the actual part is a
    simple declared signal or out port identifier.
    
    Case where the evaluation generates an event (i.e, change of value
    for the considered signal). *)

| VAssocopSimpleEvent :
    forall {pname id newv t currv sigstore' events' dstate'},
      
      (* * Premises * *)
      vexpro cenv cstate pname newv ->
      is_of_type newv t ->
      
      (* * Side conditions * *)

      (* id ∈ Sigs(Δ) ∨ Outs(Δ) and Δ(id) = t *)
      (MapsTo id (Declared t) denv \/ MapsTo id (Output t) denv) -> 
      MapsTo id currv (sigstore dstate) -> (* id ∈ σ and σ(id) = currv *)
      
      VEq newv currv (Some false) -> (* new value <> current value *)
      sigstore' = NatMap.add id newv (sigstore dstate) -> (* S' = S(id) ← newv *)
      events' = NatSet.add id (events dstate) -> (* E' = E ∪ {id} *)
      dstate' = (MkDState sigstore' (compstore dstate) events') -> (* σ' = <S',C,E'> *)
      
      (* * Conclusion * *)
      vassocop denv cenv dstate cstate (assocop_ pname (Some (n_id id))) dstate'
               
(** Evaluates an out port map association where the actual part is a
    simple declared signal or out port identifier.
    
    Case where the evaluation generates no event. *)

| VAssocopSimpleNoEvent :
    forall {pname id newv t currv},
      
      (* * Premises * *)
      vexpro cenv cstate pname newv ->
      is_of_type newv t ->
      
      (* * Side conditions * *)

      (* id ∈ Sigs(Δ) ∨ Outs(Δ) and Δ(id) = t *)
      (MapsTo id (Declared t) denv \/ MapsTo id (Output t) denv) -> 
      MapsTo id currv (sigstore dstate) -> (* id ∈ σ and σ(id) = currv *)
      
      VEq newv currv (Some true) -> (* new value = current value *)
      
      (* * Conclusion * *)
      vassocop denv cenv dstate cstate (assocop_ pname (Some (n_id id))) dstate

(** Evaluates an "out" port map association, with an indexed declared
    signal or port identifier in the actual part.
    
    Case where the evaluation generates an event, i.e a change of
    value for the considered signal.  *)
  
| VAssocopPartialEvent :
    forall {pname id ei newv i t l u lofv currv lofv' sigstore' events' dstate'},
      
      (* * Premises * *)
      vexpro cenv cstate pname newv ->
      is_of_type newv t ->

      (* These two lines are equivalent to: ei ⇝ vi ∧ vi ∈c nat(l,u) *)
      vexpr EmptyDEnv EmptyDState EmptyLEnv ei (Vnat i) ->
      l <= i <= u ->
        
      (* * Side conditions * *)
      (MapsTo id (Declared (Tarray t l u)) denv \/
       MapsTo id (Output (Tarray t l u)) denv) -> (* id ∈ Sigs(Δ) ∨ Outs(Δ) and Δ(id) = array(t,l,u) *)
      MapsTo id (Vlist lofv) (sigstore dstate) -> (* id ∈ σ and σ(id) = lofv *)

      get_at i lofv = Some currv ->              (* Current value at index [i] of [lofv] is [currv] *)
      VEq newv currv (Some false) ->             (* new value <> current value *)
      events' = NatSet.add id (events dstate) -> (* E' = E ∪ {id} *)
      
      (* S' = S(id) ← set_at(v, i, lofv) *)
      set_at newv i lofv = Some lofv' ->
      sigstore' = NatMap.add id (Vlist lofv') (sigstore dstate) ->

      (* σ' = <S',C,E'> *)
      dstate' = MkDState sigstore' (compstore dstate) events' ->
      
      (* * Conclusion * *)
      vassocop denv cenv dstate cstate (assocop_ pname (Some (n_xid id ei))) dstate'

(** Evaluates an "out" port map association, with an indexed declared
    signal or port identifier in the actual part.
    
    Case where the evaluation generates no event, then
    no changes on [dstate].  *)
  
| VAssocopPartialNoEvent :
    forall {pname id ei newv i t l u lofv currv},
      
      (* * Premises * *)
      vexpro cenv cstate pname newv ->
      is_of_type newv t ->

      (* These two lines are equivalent to: ei ⇝ vi ∧ vi ∈c nat(l,u) *)
      vexpr EmptyDEnv EmptyDState EmptyLEnv ei (Vnat i) ->
      l <= i <= u ->
        
      (* * Side conditions * *)
      (MapsTo id (Declared (Tarray t l u)) denv \/
       MapsTo id (Output (Tarray t l u)) denv) -> (* id ∈ Sigs(Δ) ∨ Outs(Δ) and Δ(id) = array(t,l,u) *)
      MapsTo id (Vlist lofv) (sigstore dstate) -> (* id ∈ σ and σ(id) = lofv *)

      get_at i lofv = Some currv -> (* Current value at index [i] of [lofv] is [currv] *)
      VEq newv currv (Some true) -> (* new value = current value *)
            
      (* * Conclusion * *)
      vassocop denv cenv dstate cstate (assocop_ pname (Some (n_xid id ei))) dstate.               

