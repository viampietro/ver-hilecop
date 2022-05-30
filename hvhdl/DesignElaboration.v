(** * Design behavior elaboration. *)

(** Defines the relations that pertain to the elaboration 
    of the behavioral part of a H-VHDL design.
 *)

Require Import common.CoqLib.
Require Import common.GlobalTypes.

Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.Environment.
Require Import hvhdl.TypeElaboration.
Require Import hvhdl.DefaultValue.
Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.StaticExpressions.
Require Import hvhdl.ExpressionEvaluation.
Require Import hvhdl.ValidSS.
Require Import hvhdl.GenericElaboration.
Require Import hvhdl.PortElaboration.
Require Import hvhdl.ArchitectureElaboration.
Require Import hvhdl.ValidPortMap.
Require Import hvhdl.HVhdlTypes.
Require Import hvhdl.MultiplyDrivenSignals.

Import NatMap.

(** ** Process declarative part elaboration *)

(** Defines the relation that elaborates the declarative part of a
    process. *)

Inductive EVars (Δ : ElDesign) (Λ : LEnv) : list vdecl -> LEnv -> Prop :=

(** Elaborates an empty list of local variable declarations. *)
| EVarsNil : EVars Δ Λ [] Λ

(** Elaborates a non-empty list of local variable decls. *)
| EVarsCons :
    forall vd lofvdecls Λ' Λ'',
      EVar Δ Λ vd Λ' ->
      EVars Δ Λ' lofvdecls Λ'' ->
      EVars Δ Λ (vd :: lofvdecls) Λ''

(** Defines the elaboration relation for one local variable
    declaration. *)
with EVar (Δ : ElDesign) (Λ : LEnv) : vdecl -> LEnv -> Prop :=
| EVar_ :
    forall τ t v id,
      
      (* Premises *)
      EType Δ τ t ->
      DefaultV t v ->

      (* Side conditions *)
      ~NatMap.In id Λ ->            (* id ∉ Λ *)
      ~NatMap.In id Δ ->            (* id ∉ Δ *)

      (* Conclusion *)
      EVar Δ Λ (vdecl_ id τ) (add id (t, v) Λ).

(** ** Design instantiation elaboration *)

(** Defines the relation that elaborates a generic map.
    
    It creates a map (i.e, a dimensioning function) binding generic
    constant ids to values.  *)

Inductive EMapG (M__g : IdMap value) : list assocg -> IdMap value -> Prop :=
  
(* Elaborates an empty generic map. No effect on the dimensioning function. *)
| EMapGNil : EMapG M__g [] M__g

(* Elaborates a sequence of generic map associations. *)
| EMapGCons :
    forall ag lofassocgs M__g' M__g'',
      EAssocG M__g ag M__g' ->
      EMapG M__g' lofassocgs M__g'' ->
      EMapG M__g (ag :: lofassocgs) M__g''

(** Defines the elaboration relation for a single generic map association. *)
            
with EAssocG (M__g : IdMap value) : assocg -> IdMap value -> Prop :=
| EAssocG_ :
    forall id e v,

      (* Premises *)
      IsLStaticExpr e ->
      VExpr EmptyElDesign EmptySStore EmptyLEnv false e v ->

      (* Side conditions *)
      ~NatMap.In id M__g ->

      (* Conclusion *)
      EAssocG M__g (assocg_ id e) (add id v M__g).

(** * Design elaboration relation *)

(** Defines the design elaboration relation. *)

Inductive EDesign (D__s : IdMap design) : IdMap value -> design -> ElDesign -> DState -> Prop :=
| EDesign_ :
    forall M__g d Δ Δ' Δ'' Δ''' σ σ' σ'',

      (* Premises *)
      EGens EmptyElDesign M__g (gens d) Δ ->
      EPorts Δ EmptyDState (ports d) Δ' σ ->
      EDecls Δ' σ (sigs d) Δ'' σ' ->
      EBeh D__s Δ'' σ' (beh d) Δ''' σ'' ->
      NoMDInCS Δ''' (beh d) ->
      
      (* Conclusion *)
      EDesign D__s M__g d Δ''' σ''    

(** Defines the relation that elaborates the concurrent statements
    defining the behavior of a design.  *)

with EBeh (D__s : IdMap design) : ElDesign -> DState -> cs -> ElDesign -> DState -> Prop :=

(** Elaborates and type-checks a process statement. *)
| EBehPs :
    forall id__p vars stmt Λ Δ σ,

      (* Premises *)
      EVars Δ EmptyLEnv vars Λ ->
      ValidSS Δ (sstore σ) Λ stmt ->

      (* Side conditions *)
      ~NatMap.In id__p Δ ->

      (* Conclusion *)
      EBeh D__s Δ σ (cs_ps id__p vars stmt) (MkElDesign (NatMap.add id__p (Process Λ) Δ)) σ

(** Elaborates and type-checks a component instantiation statement. *)
| EBehComp :
    forall Δ σ id__c id__e g i o M__g Δ__c σ__c cdesign,

      (* Premises *)
      EMapG (NatMap.empty value) g M__g ->
      EDesign D__s M__g cdesign Δ__c σ__c ->
      ValidIPM Δ Δ__c (sstore σ) i ->
      ValidOPM Δ Δ__c o ->
      
      (* Side conditions *)
      ~NatMap.In id__c Δ ->
      ~NatMap.In id__c (cstore σ) ->
      ~NatMap.In id__c (sstore σ) ->
      MapsTo id__e cdesign D__s ->
      (forall id__g, NatMap.In id__g M__g -> exists t v, MapsTo id__g (Generic t v) Δ__c) ->
      
      (* Conclusion *)
      EBeh D__s Δ σ
           (cs_comp id__c id__e g i o)
           (MkElDesign (NatMap.add id__c (Component Δ__c) Δ))
           (cstore_add id__c σ__c σ)
           
(** Elaborates a null cs statement *)
| EBehNull:
    forall Δ σ, EBeh D__s Δ σ cs_null Δ σ

(** Elaborates the parallel composition of concurrent statements *)
| EBehPar:
    forall Δ Δ' Δ'' σ σ' σ'' cstmt cstmt',
      EBeh D__s Δ σ cstmt Δ' σ' ->
      EBeh D__s Δ' σ' cstmt' Δ'' σ'' ->
      EBeh D__s Δ σ (cs_par cstmt cstmt') Δ'' σ''.
