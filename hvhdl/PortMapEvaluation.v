(** * Port map evaluation relation. *)

(** Defines the relation that evaluates input and output port maps.

    The evaluation of an input port map association (resp. output port
    map association) modifies the state of the design instance (resp. the
    embedding design). *)

Require Import common.CoqLib.
Require Import common.GlobalTypes.
Require Import common.NatSet.
Require Import common.NatMap.

Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.Environment.
Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.ExpressionEvaluation.
Require Import hvhdl.HVhdlTypes.

(** Defines the evaluation relation for input port maps.
    
    The evaluation of an input port map possibly modifies the value of
    the input ports in the signal store [sst__c]. *)

Inductive MIP (Δ Δ__c : ElDesign) (sst sst__c : IdMap value) : list ipassoc -> IdMap value -> Prop := 

(** An empty list of port associations does not change the state
    [sst__c] of the component instance. *)
| MIPNil : MIP Δ Δ__c sst sst__c [] sst__c 

(** Evaluates a non-empty list of port associations. *)
| MIPCons :
    forall ipa lofipas sst__c' sst__c'',
      VIPAssoc Δ Δ__c sst sst__c ipa sst__c' ->
      MIP Δ Δ__c sst sst__c' lofipas sst__c'' ->
      MIP Δ Δ__c sst sst__c (ipa :: lofipas) sst__c''

(** Defines the relation that evaluates a single association present
    in an input port map.  *)
with VIPAssoc (Δ Δ__c : ElDesign) (sst sst__c : IdMap value) : ipassoc -> IdMap value -> Prop := 

(** Evaluates a input port map association, with a simple port
    identifier in the formal part. *)
  
| VIPAssocSimple :
    forall id e v t,
      
      (* * Premises * *)
      VExpr Δ sst EmptyLEnv false e v ->
      IsOfType v t ->

      (* * Side conditions (where sstc = <S,C,E>) * *)
      NatMap.MapsTo id (Input t) Δ__c -> (* id ∈ Ins(Δc) and Δc(id) = t *)

      (* * Conclusion * *)
      VIPAssoc Δ Δ__c sst sst__c (ipa_ ($id) e) (add id v sst__c)

(** Evaluates a input port map association, with an indexed port
    identifier in the formal part.  *)
  
| VIPAssocPartial :
    forall id e ei v n__i t l u aofv idx_in_bounds,
      
      (* * Premises * *)
      VExpr Δ sst EmptyLEnv false e v ->
      IsOfType v t ->
      VExpr EmptyElDesign EmptySStore EmptyLEnv false ei (Vnat n__i) ->
      IsOfType (Vnat n__i) (Tnat l u) ->
        
      (* * Side conditions * *)
      NatMap.MapsTo id (Input (Tarray t l u)) Δ__c -> (* id ∈ Ins(Δc) and Δc(id) = array(t,l,u) *)
      NatMap.MapsTo id (Varr aofv) sst__c -> (* [id ∈ sst__c] and [sst__c(id) = aofv] *)
      let i := (N.to_nat (n__i - l)) in
      
      (* * Conclusion * *)
      VIPAssoc Δ Δ__c sst sst__c (ipa_ (id $[[ei]]) e) (add id (Varr (set_at v i aofv idx_in_bounds)) sst__c).
    
(** Defines the evaluation relation for output port maps.
    
    The evaluation of an output port map modifies the signal store
    [sst] of the embedding design. *)

Inductive MOP (Δ Δ__c : ElDesign) (sst sst__c : IdMap value) : list opassoc -> IdMap value -> Prop :=

(** An empty list of port associations does not change the state
    [sst] of the embedding design. *)
  
| MapopNil : MOP Δ Δ__c sst sst__c [] sst 

(** Evaluates a non-empty list of port associations. *)
| MapopCons :
    forall {opa lofopas sst' sst''},
      VOPAssoc Δ Δ__c sst sst__c opa sst' ->
      MOP Δ Δ__c sst' sst__c lofopas sst'' ->
      MOP Δ Δ__c sst sst__c (opa :: lofopas) sst''

(** Defines the relation that evaluates an output port map
    association.  *)
with VOPAssoc (Δ Δ__c : ElDesign) (sst sst__c : IdMap value) : opassoc -> IdMap value -> Prop :=

(** Evaluates an association where the formal part is not bound, i.e
    the actual part is [None] (the "open" keyword is used in concrete
    VHDL syntax) *)
| VOPAssocOpen : forall id__f, VOPAssoc Δ Δ__c sst sst__c (opa_simpl id__f None) sst

(** Evaluates an output port map association where the actual part is
    a simple declared signal or output port identifier.
    
    Case when the formal part is a simple identifier. *)

| VOPAssocSimpleToSimple :
    forall id__f id__a v t,
      
      (* * Premises * *)
      VExpr Δ__c sst__c EmptyLEnv true (#id__f) v ->
      IsOfType v t ->
      
      (* * Side conditions * *)

      (* [id__a ∈ S(Δ) ∪ O(Δ) and Δ(id__a) = t] *)
      (MapsTo id__a (Declared t) Δ \/ MapsTo id__a (Output t) Δ) -> 
      
      (* * Conclusion * *)
      VOPAssoc Δ Δ__c sst sst__c (opa_simpl id__f (Some ($id__a))) (add id__a v sst)

(** Evaluates an output port map association where the actual part is
    a simple declared signal or output port identifier.
    
    Case when the formal part is an indexed identifier. *)

| VOPAssocIdxToSimple :
  forall id__f e__i id__a v t,
    
    (* * Premises * *)
    VExpr Δ__c sst__c EmptyLEnv true (id__f [[e__i]]) v ->
    IsOfType v t ->
    
    (* * Side conditions * *)

    (* [id__a ∈ S(Δ) ∪ O(Δ) and Δ(id__a) = t] *)
    (MapsTo id__a (Declared t) Δ \/ MapsTo id__a (Output t) Δ) -> 
    
    (* * Conclusion * *)
    VOPAssoc Δ Δ__c sst sst__c (opa_idx id__f e__i ($id__a)) (add id__a v sst)
               
(** Evaluates an "out" port map association, with an indexed declared
    signal or port identifier in the actual part.
    
    Case when the formal part is a simple identifier.  *)
  
| VOPAssocSimpleToPartial :
    forall id__f id__a ei v n__i t l u aofv idx_in_bounds,
      
      (* * Premises * *)
      VExpr Δ__c sst__c EmptyLEnv true (#id__f) v ->
      IsOfType v t ->
      VExpr EmptyElDesign EmptySStore EmptyLEnv false ei (Vnat n__i) ->
      IsOfType (Vnat n__i) (Tnat l u) ->
      
      (* * Side conditions * *)
      
      (* [id__a ∈ Sigs(Δ) ∪ Outs(Δ) and Δ(id__a) = array(t,l,u)] *)
      (MapsTo id__a (Declared (Tarray t l u)) Δ \/ MapsTo id__a (Output (Tarray t l u)) Δ) -> 
      MapsTo id__a (Varr aofv) sst -> (* [id__a ∈ sst and sst(id__a) = aofv] *)
      let i := (N.to_nat (n__i - l)) in
      let aofv' := set_at v i aofv idx_in_bounds in
      
      (* * Conclusion * *)
      VOPAssoc Δ Δ__c sst sst__c (opa_simpl id__f (Some (id__a $[[ei]]))) (add id__a (Varr aofv') sst)

(** Evaluates an "out" port map association, with an indexed declared
    signal or port identifier in the actual part.
    
    Case when the formal part is an indexed identifier.  *)
  
| VOPAssocIdxToPartial :
  forall id__f e__i' id__a ei v n__i t l u aofv idx_in_bounds,
    
    (* * Premises * *)
    VExpr Δ__c sst__c EmptyLEnv true (id__f [[e__i']]) v ->
    IsOfType v t ->
    VExpr EmptyElDesign EmptySStore EmptyLEnv false ei (Vnat n__i) ->
    IsOfType (Vnat n__i) (Tnat l u) ->
    
    (* * Side conditions * *)
    
    (* [id__a ∈ Sigs(Δ) ∪ Outs(Δ) and Δ(id__a) = array(t,l,u)] *)
    (MapsTo id__a (Declared (Tarray t l u)) Δ \/ MapsTo id__a (Output (Tarray t l u)) Δ) -> 
    MapsTo id__a (Varr aofv) sst -> (* [id__a ∈ sst and sst(id__a) = aofv] *)
    let i := (N.to_nat (n__i - l)) in
    let aofv' := set_at v i aofv idx_in_bounds in
    
    (* * Conclusion * *)
    VOPAssoc Δ Δ__c sst sst__c (opa_idx id__f e__i' (id__a $[[ei]])) (add id__a (Varr aofv') sst).

               

