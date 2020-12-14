(** * Design behavior elaboration. *)

(** Defines the relations that pertain to the elaboration 
    of the behavioral part of a H-VHDL design.
 *)

Require Import Coqlib.
Require Import GlobalTypes.
Require Import AbstractSyntax.
Require Import Environment.
Require Import TypeElaboration.
Require Import DefaultValue.
Require Import SemanticalDomains.
Require Import StaticExpressions.
Require Import ExpressionEvaluation.
Require Import ValidSS.
Require Import GenericElaboration.
Require Import PortElaboration.
Require Import ArchitectureElaboration.
Require Import ValidPortMap.
Require Import HVhdlTypes.

Import NatMap.

(** ** Process elaboration. *)

(** Defines the relation that elaborates the declarative part of a
    process. *)

Inductive evars (Δ : ElDesign) (Λ : LEnv) : list vdecl -> LEnv -> Prop :=

(* Elaborates an empty list of local variable declarations. *)
| EVarsNil : evars Δ Λ [] Λ

(* Elaborates a non-empty list of local variable decls. *)
| EVarsCons :
    forall vd lofvdecls Λ' Λ'',
      evar Δ Λ vd Λ' ->
      evars Δ Λ' lofvdecls Λ'' ->
      evars Δ Λ (vd :: lofvdecls) Λ''

(** Defines the elaboration relation for one local variable declaration. *)
with evar (Δ : ElDesign) (Λ : LEnv) : vdecl -> LEnv -> Prop :=
| EVar :
    forall tau t v id,
      
      (* Premises *)
      etype Δ tau t ->
      defaultv t v ->

      (* Side conditions *)
      ~NatMap.In id Λ ->            (* id ∉ Λ *)
      ~NatMap.In id Δ ->            (* id ∉ Δ *)

      (* Conclusion *)
      evar Δ Λ (vdecl_ id tau) (add id (t, v) Λ).

(** ** Component instantiation elaboration. *)

(** Defines the relation that elaborates a generic map.
    
    It creates a map (i.e, a dimensioning function) binding generic
    constant ids to values.  *)

Inductive emapg (dimen : IdMap value) : list assocg -> IdMap value -> Prop :=
  
(* Elaborates an empty generic map. No effect on the dimensioning function. *)
| EMapGNil : emapg dimen [] dimen

(* Elaborates a sequence of generic map associations. *)
| EMapGCons :
    forall ag lofassocgs dimen' dimen'',
      eassocg dimen ag dimen' ->
      emapg dimen' lofassocgs dimen'' ->
      emapg dimen (ag :: lofassocgs) dimen''

(** Defines the elaboration relation for a single generic map association. *)
            
with eassocg (dimen : IdMap value) : assocg -> IdMap value -> Prop :=
| EAssocG :
    forall id e v,

      (* Premises *)
      is_lstatic_expr e ->
      vexpr EmptyElDesign EmptyDState EmptyLEnv false e v ->

      (* Side conditions *)
      ~NatMap.In id dimen ->

      (* Conclusion *)
      eassocg dimen (assocg_ id e) (add id v dimen).
      

(** * Design elaboration relation. *)

(** Defines the design elaboration relation. *)

Inductive edesign (dstore : IdMap design) : IdMap value -> design -> ElDesign -> DState -> Prop :=
| EDesign :
    forall dimen entid archid gens ports sigs behavior
           Δ Δ' Δ'' Δ''' σ σ' σ'',

      (* Premises *)
      egens EmptyElDesign dimen gens Δ ->
      eports Δ EmptyDState ports Δ' σ ->
      edecls Δ' σ sigs Δ'' σ' ->
      ebeh dstore Δ'' σ' behavior Δ''' σ'' ->
      
      (* Conclusion *)
      edesign dstore dimen (design_ entid archid gens ports sigs behavior) Δ''' σ''    

(** Defines the relation that elaborates the concurrent statements
    defining the behavior of a design.  *)

with ebeh (dstore : IdMap design) : ElDesign -> DState -> cs -> ElDesign -> DState -> Prop :=

(** Elaborates and type-checks a process statement. *)
| EBehPs :
    forall id sl vars stmt Λ Δ σ,

      (* Premises *)
      evars Δ EmptyLEnv vars Λ ->
      validss Δ σ Λ stmt ->

      (* Side conditions *)
      ~NatMap.In id Δ ->
      (* sl ⊆ Ins(Δ) ∪ Sigs(Δ) *)
      (forall s,
          NatSet.In s sl ->
          exists t, MapsTo s (Declared t) Δ \/ MapsTo s (Input t) Δ) ->

      (* Conclusion *)
      ebeh dstore Δ σ (cs_ps id sl vars stmt) (NatMap.add id (Process Λ) Δ) σ

(** Elaborates and type-checks a component instantiation statement. *)
| EBehComp :
    forall Δ σ id__c id__e gmap ipmap opmap
           dimen Δ__c σ__c cdesign,

      (* Premises *)
      emapg (NatMap.empty value) gmap dimen ->
      edesign dstore dimen cdesign Δ__c σ__c ->
      validipm Δ Δ__c σ ipmap ->
      validopm Δ Δ__c opmap ->
      
      (* Side conditions *)
      MapsTo id__e cdesign dstore ->
      (forall g, NatMap.In g dimen -> exists t v, MapsTo g (Generic t v) Δ__c) ->
      
      (* Conclusion *)
      ebeh dstore Δ σ
           (cs_comp id__c id__e gmap ipmap opmap)
           (NatMap.add id__c (Component Δ__c (behavior cdesign)) Δ)
           (cstore_add id__c σ__c σ).
