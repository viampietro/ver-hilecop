(** * Design behavior elaboration. *)

(** Defines the relations that pertain to the elaboration 
    of the behavioral part of a H-VHDL design.
 *)

Require Import CoqLib.
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
      DefaultV t v ->

      (* Side conditions *)
      ~NatMap.In id Λ ->            (* id ∉ Λ *)
      ~NatMap.In id Δ ->            (* id ∉ Δ *)

      (* Conclusion *)
      evar Δ Λ (vdecl_ id tau) (add id (t, v) Λ).

(** ** Component instantiation elaboration. *)

(** Defines the relation that elaborates a generic map.
    
    It creates a map (i.e, a dimensioning function) binding generic
    constant ids to values.  *)

Inductive emapg (M__g : IdMap value) : list assocg -> IdMap value -> Prop :=
  
(* Elaborates an empty generic map. No effect on the dimensioning function. *)
| EMapGNil : emapg M__g [] M__g

(* Elaborates a sequence of generic map associations. *)
| EMapGCons :
    forall ag lofassocgs M__g' M__g'',
      eassocg M__g ag M__g' ->
      emapg M__g' lofassocgs M__g'' ->
      emapg M__g (ag :: lofassocgs) M__g''

(** Defines the elaboration relation for a single generic map association. *)
            
with eassocg (M__g : IdMap value) : assocg -> IdMap value -> Prop :=
| EAssocG :
    forall id e v,

      (* Premises *)
      IsLStaticExpr e ->
      VExpr EmptyElDesign EmptyDState EmptyLEnv false e v ->

      (* Side conditions *)
      ~NatMap.In id M__g ->

      (* Conclusion *)
      eassocg M__g (assocg_ id e) (add id v M__g).
      

(** * Design elaboration relation. *)

(** Defines the design elaboration relation. *)

Inductive edesign (D__s : IdMap design) : IdMap value -> design -> ElDesign -> DState -> Prop :=
| EDesign :
    forall M__g id__e id__a gens ports sigs behavior
           Δ Δ' Δ'' Δ''' σ σ' σ'',

      (* Premises *)
      egens EmptyElDesign M__g gens Δ ->
      eports Δ EmptyDState ports Δ' σ ->
      edecls Δ' σ sigs Δ'' σ' ->
      ebeh D__s Δ'' σ' behavior Δ''' σ'' ->
      
      (* Conclusion *)
      edesign D__s M__g (design_ id__e id__a gens ports sigs behavior) Δ''' σ''    

(** Defines the relation that elaborates the concurrent statements
    defining the behavior of a design.  *)

with ebeh (D__s : IdMap design) : ElDesign -> DState -> cs -> ElDesign -> DState -> Prop :=

(** Elaborates and type-checks a process statement. *)
| EBehPs :
    forall id__p sl vars stmt Λ Δ σ,

      (* Premises *)
      evars Δ EmptyLEnv vars Λ ->
      validss Δ σ Λ stmt ->

      (* Side conditions *)
      ~NatMap.In id__p Δ ->

      (* sl ⊆ Ins(Δ) ∪ Sigs(Δ) *)
      (forall id__s,
          NatSet.In id__s sl ->
          exists t, MapsTo id__s (Declared t) Δ \/ MapsTo id__s (Input t) Δ) ->

      (* Conclusion *)
      ebeh D__s Δ σ (cs_ps id__p sl vars stmt) (NatMap.add id__p (Process Λ) Δ) σ

(** Elaborates and type-checks a component instantiation statement. *)
| EBehComp :
    forall Δ σ id__c id__e g i o M__g Δ__c σ__c cdesign,

      (* Premises *)
      emapg (NatMap.empty value) g M__g ->
      edesign D__s M__g cdesign Δ__c σ__c ->
      validipm Δ Δ__c σ i ->
      validopm Δ Δ__c o ->
      
      (* Side conditions *)
      ~NatMap.In id__c Δ ->
      ~NatMap.In id__c (cstore σ) ->
      ~NatMap.In id__c (sstore σ) ->
      MapsTo id__e cdesign D__s ->
      (forall id__g, NatMap.In id__g M__g -> exists t v, MapsTo id__g (Generic t v) Δ__c) ->
      
      (* Conclusion *)
      ebeh D__s Δ σ
           (cs_comp id__c id__e g i o)
           (NatMap.add id__c (Component Δ__c) Δ)
           (cstore_add id__c σ__c σ)
           
(** Elaborates a null cs statement *)
| EBehNull:
    forall Δ σ, ebeh D__s Δ σ cs_null Δ σ

(** Elaborates a || cs statement *)
| EBehPar:
    forall Δ Δ' Δ'' σ σ' σ'' cstmt cstmt',
      ebeh D__s Δ σ cstmt Δ' σ' ->
      ebeh D__s Δ' σ' cstmt' Δ'' σ'' ->
      ebeh D__s Δ σ (cs_par cstmt cstmt') Δ'' σ''.
