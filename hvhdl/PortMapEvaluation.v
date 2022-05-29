(** * Port map evaluation relation. *)

(** Defines the relation that evaluates in and out port maps.

    States that the evaluation of a "in" port map entry (resp. "out"
    port map entry) transforms the state of the component instance
    (resp. the embedding design) in a certain manner. *)

Require Import CoqLib.
Require Import GlobalTypes.
Require Import NatSet.
Require Import NatMap.
Require Import SemanticalDomains.
Require Import Environment.
Require Import AbstractSyntax.
Require Import ExpressionEvaluation.

(** Defines the evaluation relation for "input" port maps.
    
    The evaluation of an "input" port map possibly modifies the value of
    the input ports of the component instance [Δ__c]. *)

Inductive mapip (Δ Δ__c : ElDesign) (σ σ__c : DState) : list associp -> DState -> Prop := 

(** An empty list of port associations does not change the state
    [σ__c] of the component instance. *)
| MapipNil : mapip Δ Δ__c σ σ__c [] σ__c 

(** Evaluates a non-empty list of port associations. *)
| MapipCons :
    forall {asip lofasips σ__c' σ__c''},
      vassocip Δ Δ__c σ σ__c asip σ__c' ->
      mapip Δ Δ__c σ σ__c' lofasips σ__c'' ->
      mapip Δ Δ__c σ σ__c (asip :: lofasips) σ__c''

(** Defines the relation that evaluates a single association present
    in an input port map.  *)
with vassocip (Δ Δ__c : ElDesign) (σ σ__c : DState) : associp -> DState -> Prop := 

(** Evaluates a input port map association, with a simple port
    identifier in the formal part. *)
  
| VAssocipSimpleEvent :
    forall id e v t,
      
      (* * Premises * *)
      VExpr Δ σ EmptyLEnv false e v ->
      IsOfType v t ->

      (* * Side conditions (where σc = <S,C,E>) * *)
      NatMap.MapsTo id (Input t) Δ__c -> (* id ∈ Ins(Δc) and Δc(id) = t *)

      (* * Conclusion * *)
      vassocip Δ Δ__c σ σ__c (associp_ ($id) e) (sstore_add id v σ__c)

(** Evaluates a input port map association, with an indexed port
    identifier in the formal part.  *)
  
| VAssocipPartialEvent :
    forall id e ei v i t l u aofv idx_in_bounds,

      let idx := (N.to_nat (i - l)) in
      
      (* * Premises * *)
      VExpr Δ σ EmptyLEnv false e v ->
      IsOfType v t ->

      (* These two lines are equivalent to: ei ⇝ vi ∧ vi ∈c nat(l,u) *)
      VExpr EmptyElDesign EmptyDState EmptyLEnv false ei (Vnat i) ->
      l <= i <= u ->
        
      (* * Side conditions * *)
      NatMap.MapsTo id (Input (Tarray t l u)) Δ__c -> (* id ∈ Ins(Δc) and Δc(id) = array(t,l,u) *)
      NatMap.MapsTo id (Varr aofv) (sstore σ__c) -> (* id ∈ σ and σ(id) = v' *)
      
      (* * Conclusion * *)
      vassocip Δ Δ__c σ σ__c (associp_ (id $[[ei]]) e) (sstore_add id (Varr (set_at v idx aofv idx_in_bounds)) σ__c).
    
(** Defines the evaluation relation for "out" port maps, i.e, port
    maps relating ports in "out" mode to other out ports or declared
    signals.
    
    The evaluation of an "out" port map affects the current state
    [σ] of the embedding design. *)

Inductive mapop (Δ Δ__c : ElDesign) (σ σ__c : DState) : list assocop -> DState -> Prop :=

(** An empty list of port associations does not change the state
    [σ] of the embedding design. *)
  
| MapopNil : mapop Δ Δ__c σ σ__c [] σ 

(** Evaluates a non-empty list of port associations. *)
| MapopCons :
    forall {asop lofasops σ' σ''},
      vassocop Δ Δ__c σ σ__c asop σ' ->
      mapop Δ Δ__c σ' σ__c lofasops σ'' ->
      mapop Δ Δ__c σ σ__c (asop :: lofasops) σ''

(** Defines the relation that evaluates a single association present
    in an "out" port map.  *)
with vassocop (Δ Δ__c : ElDesign) (σ σ__c : DState) : assocop -> DState -> Prop :=

(** Evaluates an association where the formal part is not bound, i.e
    the actual part is [None] (the "open" keyword is used in concrete
    VHDL syntax) *)
| VAssocopOpen : forall id__f, vassocop Δ Δ__c σ σ__c (assocop_simpl id__f None) σ

(** Evaluates an out port map association where the actual part is a
    simple declared signal or out port identifier.
    
    Case where the evaluation generates an event (i.e, change of value
    for the considered signal). *)

| VAssocopSimpleToSimpleEvent :
    forall id__f id__a newv t currv sstore' events' σ',
      
      (* * Premises * *)
      VExpr Δ__c σ__c EmptyLEnv true (e_name ($id__f)) newv ->
      IsOfType newv t ->
      
      (* * Side conditions * *)

      (* [id__a ∈ Sigs(Δ) ∪ Outs(Δ) and Δ(id__a) = t] *)
      (MapsTo id__a (Declared t) Δ \/ MapsTo id__a (Output t) Δ) -> 
      MapsTo id__a currv (sstore σ) -> (* [id__a ∈ σ and σ(id__a) = currv] *)
      
      OVEq newv currv (Some false) -> (* new value <> current value *)
      sstore' = NatMap.add id__a newv (sstore σ) -> (* S' = S(id) ← newv *)
      events' = NatSet.add id__a (events σ) -> (* E' = E ∪ {id} *)
      σ' = (MkDState sstore' (cstore σ) events') -> (* σ' = <S',C,E'> *)
      
      (* * Conclusion * *)
      vassocop Δ Δ__c σ σ__c (assocop_simpl id__f (Some ($id__a))) σ'
               
(** Evaluates an out port map association where the actual part is a
    simple declared signal or out port identifier.
    
    Case where the evaluation generates no event. *)

| VAssocopSimpleToSimpleNoEvent :
    forall id__f id__a newv t currv,
      
      (* * Premises * *)
      VExpr Δ__c σ__c EmptyLEnv true (e_name ($id__f)) newv ->
      IsOfType newv t ->
      
      (* * Side conditions * *)

      (* [id__a ∈ Sigs(Δ) ∪ Outs(Δ) and Δ(id__a) = t] *)
      (MapsTo id__a (Declared t) Δ \/ MapsTo id__a (Output t) Δ) -> 
      MapsTo id__a currv (sstore σ) -> (* [id__a ∈ σ and σ(id__a) = currv] *)
      
      OVEq newv currv (Some true) -> (* new value = current value *)
      
      (* * Conclusion * *)
      vassocop Δ Δ__c σ σ__c (assocop_simpl id__f (Some ($id__a))) σ

(** Evaluates an "out" port map association, with an indexed declared
    signal or port identifier in the actual part.
    
    Case where the evaluation generates an event, i.e a change of
    value for the considered signal.  *)
  
| VAssocopSimpleToPartialEvent :
    forall id__f id__a ei newv i t l u aofv idx_in_bounds aofv' sstore' events' σ',

      let idx := (N.to_nat (i - l)) in
      
      (* * Premises * *)
      VExpr Δ__c σ__c EmptyLEnv true (e_name ($id__f)) newv ->
      IsOfType newv t ->

      (* These two lines are equivalent to: ei ⇝ vi ∧ vi ∈c nat(l,u) *)
      VExpr EmptyElDesign EmptyDState EmptyLEnv false ei (Vnat i) ->
      l <= i <= u ->
        
      (* * Side conditions * *)
      
      (* [id__a ∈ Sigs(Δ) ∪ Outs(Δ) and Δ(id__a) = array(t,l,u)] *)
      (MapsTo id__a (Declared (Tarray t l u)) Δ \/ MapsTo id__a (Output (Tarray t l u)) Δ) -> 
      MapsTo id__a (Varr aofv) (sstore σ) -> (* [id__a ∈ σ and σ(id__a) = aofv] *)

      OVEq newv (get_at idx aofv idx_in_bounds) (Some false) -> (* new value <> current value *)
      events' = NatSet.add id__a (events σ) ->                    (* [E' = E ∪ {id__a}] *)
      
      (* [S' = S(id__a) ← set_at(v, i, aofv)] *)
      set_at newv idx aofv idx_in_bounds = aofv' ->
      sstore' = NatMap.add id__a (Varr aofv') (sstore σ) ->

      (* σ' = <S',C,E'> *)
      σ' = MkDState sstore' (cstore σ) events' ->
      
      (* * Conclusion * *)
      vassocop Δ Δ__c σ σ__c (assocop_simpl id__f (Some (id__a $[[ei]]))) σ'

(** Evaluates an "out" port map association, with an indexed declared
    signal or port identifier in the actual part.
    
    Case where the evaluation generates no event, then
    no changes on [σ].  *)
  
| VAssocopSimpleToPartialNoEvent :
    forall id__f id__a ei newv i t l u aofv idx_in_bounds,

      let idx := (N.to_nat (i - l)) in
      
      (* * Premises * *)
      VExpr Δ__c σ__c EmptyLEnv true (e_name ($id__f)) newv ->
      IsOfType newv t ->

      (* These two lines are equivalent to: ei ⇝ vi ∧ vi ∈c nat(l,u) *)
      VExpr EmptyElDesign EmptyDState EmptyLEnv false ei (Vnat i) ->
      l <= i <= u ->
        
      (* * Side conditions * *)
      (* [id__a ∈ Sigs(Δ) ∨ Outs(Δ) and Δ(id__a) = array(t,l,u)] *)
      (MapsTo id__a (Declared (Tarray t l u)) Δ \/ MapsTo id__a (Output (Tarray t l u)) Δ) ->
      MapsTo id__a (Varr aofv) (sstore σ) -> (* [id__a ∈ σ and σ(id__a) = aofv] *)

      OVEq newv (get_at idx aofv idx_in_bounds) (Some true) -> (* new value = current value *)
            
      (* * Conclusion * *)
      vassocop Δ Δ__c σ σ__c (assocop_simpl id__f (Some (n_xid id__a ei))) σ

(** Evaluates an output port map association, with an indexed declared
    signal or output port identifier in the actual part, and a indexed
    output port identifier in the formal part.
    
    Case where the evaluation generates an event, i.e a change of
    value for the considered signal.  *)
               
| VAssocopPartialToPartialEvent :
    forall id__f id__a e'__i ei newv i t l u aofv idx_in_bounds aofv' sstore' events' σ',

      let idx := (N.to_nat (i - l)) in
      
      (* * Premises * *)
      VExpr Δ__c σ__c EmptyLEnv true (e_name (id__f $[[e'__i]])) newv ->
      IsOfType newv t ->

      (* These two lines are equivalent to: ei ⇝ vi ∧ vi ∈c nat(l,u) *)
      VExpr EmptyElDesign EmptyDState EmptyLEnv false ei (Vnat i) ->
      l <= i <= u ->
      
      (* * Side conditions * *)
      
      (* [id__a ∈ Sigs(Δ) ∪ Outs(Δ) and Δ(id__a) = array(t,l,u)] *)
      (MapsTo id__a (Declared (Tarray t l u)) Δ \/ MapsTo id__a (Output (Tarray t l u)) Δ) -> 
      MapsTo id__a (Varr aofv) (sstore σ) -> (* [id__a ∈ σ and σ(id__a) = aofv] *)

      OVEq newv (get_at idx aofv idx_in_bounds) (Some false) -> (* new value <> current value *)
      events' = NatSet.add id__a (events σ) ->                    (* [E' = E ∪ {id__a}] *)
      
      (* [S' = S(id__a) ← set_at(v, i, aofv)] *)
      set_at newv idx aofv idx_in_bounds = aofv' ->
      sstore' = NatMap.add id__a (Varr aofv') (sstore σ) ->

      (* σ' = <S',C,E'> *)
      σ' = MkDState sstore' (cstore σ) events' ->
      
      (* * Conclusion * *)
      vassocop Δ Δ__c σ σ__c (assocop_idx id__f e'__i (id__a $[[ei]])) σ'
               
(** Evaluates an output port map association, with an indexed declared
    signal or output port identifier in the actual part, and a indexed output
    port identifier in the formal part.
    
    Case where the evaluation generates no event, then no changes on
    [σ].  *)
               
| VAssocopPartialToPartialNoEvent :
    forall id__f id__a e__i e__i' newv i t l u aofv idx_in_bounds,

      let idx := (N.to_nat (i - l)) in
      
      (* * Premises * *)
      VExpr Δ__c σ__c EmptyLEnv true (e_name (id__f $[[e__i]])) newv ->
      IsOfType newv t ->

      (* These two lines are equivalent to: ei ⇝ vi ∧ vi ∈c nat(l,u) *)
      VExpr EmptyElDesign EmptyDState EmptyLEnv false e__i' (Vnat i) ->
      l <= i <= u ->
      
      (* * Side conditions * *)
      (* [id__a ∈ Sigs(Δ) ∨ Outs(Δ) and Δ(id__a) = array(t,l,u)] *)
      (MapsTo id__a (Declared (Tarray t l u)) Δ \/ MapsTo id__a (Output (Tarray t l u)) Δ) ->
      MapsTo id__a (Varr aofv) (sstore σ) -> (* [id__a ∈ σ and σ(id__a) = aofv] *)

      OVEq newv (get_at idx aofv idx_in_bounds) (Some true) -> (* new value = current value *)
      
      (* * Conclusion * *)
      vassocop Δ Δ__c σ σ__c (assocop_idx id__f e__i (id__a $[[e__i']])) σ

(** Evaluates an out port map association where the actual part is a
    simple declared signal or out port identifier, and the formal part
    is an indexed output port identifier.
    
    Case where the evaluation generates an event (i.e, change of value
    for the considered signal). *)

| VAssocopPartialToSimpleEvent :
    forall id__f id__a e__i newv t currv sstore' events' σ',
      
      (* * Premises * *)
      VExpr Δ__c σ__c EmptyLEnv true (e_name (id__f $[[e__i]])) newv ->
      IsOfType newv t ->
      
      (* * Side conditions * *)

      (* [id__a ∈ Sigs(Δ) ∪ Outs(Δ) and Δ(id__a) = t] *)
      (MapsTo id__a (Declared t) Δ \/ MapsTo id__a (Output t) Δ) -> 
      MapsTo id__a currv (sstore σ) -> (* [id__a ∈ σ and σ(id__a) = currv] *)
      
      OVEq newv currv (Some false) -> (* new value <> current value *)
      sstore' = NatMap.add id__a newv (sstore σ) -> (* S' = S(id) ← newv *)
      events' = NatSet.add id__a (events σ) -> (* E' = E ∪ {id} *)
      σ' = (MkDState sstore' (cstore σ) events') -> (* σ' = <S',C,E'> *)
      
      (* * Conclusion * *)
      vassocop Δ Δ__c σ σ__c (assocop_idx id__f e__i ($id__a)) σ'
               
(** Evaluates an out port map association where the actual part is a
    simple declared signal or out port identifier, and the formal part
    is an indexed output port identifier.
    
    Case where the evaluation generates no event. *)

| VAssocopPartialToSimpleNoEvent :
    forall id__f e__i id__a newv t currv,
      
      (* * Premises * *)
      VExpr Δ__c σ__c EmptyLEnv true (e_name (id__f $[[e__i]])) newv ->
      IsOfType newv t ->
      
      (* * Side conditions * *)

      (* [id__a ∈ Sigs(Δ) ∪ Outs(Δ) and Δ(id__a) = t] *)
      (MapsTo id__a (Declared t) Δ \/ MapsTo id__a (Output t) Δ) -> 
      MapsTo id__a currv (sstore σ) -> (* [id__a ∈ σ and σ(id__a) = currv] *)
      
      OVEq newv currv (Some true) -> (* new value = current value *)
      
      (* * Conclusion * *)
      vassocop Δ Δ__c σ σ__c (assocop_idx id__f e__i ($id__a)) σ.

               

