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

Inductive evars (ed : ElDesign) (lenv : LEnv) : list vdecl -> LEnv -> Prop :=

(* Elaborates an empty list of local variable declarations. *)
| EVarsNil : evars ed lenv [] lenv

(* Elaborates a non-empty list of local variable decls. *)
| EVarsCons :
    forall {vd lofvdecls lenv' lenv''},
      evar ed lenv vd lenv' ->
      evars ed lenv' lofvdecls lenv'' ->
      evars ed lenv (vd :: lofvdecls) lenv''

(** Defines the elaboration relation for one local variable declaration. *)
with evar (ed : ElDesign) (lenv : LEnv) : vdecl -> LEnv -> Prop :=
| EVar :
    forall {tau t v id},
      
      (* Premises *)
      etype ed tau t ->
      defaultv t v ->

      (* Side conditions *)
      ~NatMap.In id lenv ->            (* id ∉ Λ *)
      ~NatMap.In id ed ->            (* id ∉ Δ *)

      (* Conclusion *)
      evar ed lenv (vdecl_ id tau) (add id (t, v) lenv).

(** ** Component instantiation elaboration. *)

(** Defines the relation that elaborates a generic map.
    
    It creates a map (i.e, a dimensioning function) binding generic
    constant ids to values.  *)

Inductive emapg (dimen : IdMap value) : list assocg -> IdMap value -> Prop :=
  
(* Elaborates an empty generic map. No effect on the dimensioning function. *)
| EMapGNil : emapg dimen [] dimen

(* Elaborates a sequence of generic map associations. *)
| EMapGCons :
    forall {ag lofassocgs dimen' dimen''},
      eassocg dimen ag dimen' ->
      emapg dimen' lofassocgs dimen'' ->
      emapg dimen (ag :: lofassocgs) dimen''

(** Defines the elaboration relation for a single generic map association. *)
            
with eassocg (dimen : IdMap value) : assocg -> IdMap value -> Prop :=
| EAssocG :
    forall {id e v},

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
    forall {dimen entid archid gens ports sigs behavior
                  ed ed' ed'' ed''' dstate dstate' dstate''},

      (* Premises *)
      egens EmptyElDesign dimen gens ed ->
      eports ed EmptyDState ports ed' dstate ->
      edecls ed' dstate sigs ed'' dstate' ->
      ebeh dstore ed'' dstate' behavior ed''' dstate'' ->
      
      (* Conclusion *)
      edesign dstore dimen (design_ entid archid gens ports sigs behavior) ed''' dstate''    

(** Defines the relation that elaborates the concurrent statements
    defining the behavior of a design.  *)

with ebeh (dstore : IdMap design) : ElDesign -> DState -> cs -> ElDesign -> DState -> Prop :=

(** Elaborates and type-checks a process statement. *)
| EBehPs :
    forall {id sl vars stmt lenv ed dstate},

      (* Premises *)
      evars ed EmptyLEnv vars lenv ->
      validss ed dstate lenv stmt ->

      (* Side conditions *)
      ~NatMap.In id ed ->
      (* sl ⊆ Ins(Δ) ∪ Sigs(Δ) *)
      (forall {s},
          NatSet.In s sl ->
          exists {t}, MapsTo s (Declared t) ed \/ MapsTo s (Input t) ed) ->

      (* Conclusion *)
      ebeh dstore ed dstate (cs_ps id sl vars stmt) (NatMap.add id (Process lenv) ed) dstate

(** Elaborates and type-checks a component instantiation statement. *)
| EBehComp :
    forall {ed dstate idc ide gmap ipmap opmap
                 entid archid gens ports sigs behavior
                 dimen cenv cstate cdesign},

      (* Premises *)
      emapg (NatMap.empty value) gmap dimen ->
      edesign dstore dimen cdesign cenv cstate ->
      validipm ed cenv dstate ipmap ->
      validopm ed cenv opmap ->
      
      (* Side conditions *)
      cdesign = design_ entid archid gens ports sigs behavior ->
      MapsTo ide cdesign dstore ->
      (forall {g}, NatMap.In g dimen -> exists {t v}, MapsTo g (Generic t v) cenv) ->
      
      (* Conclusion *)
      ebeh dstore ed dstate (cs_comp idc ide gmap ipmap opmap) ed dstate.
