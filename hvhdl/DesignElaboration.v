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

Import NatMap.

(** ** Process elaboration. *)

(** Defines the relation that elaborates the declarative part of a
    process. *)

Inductive evars (denv : DEnv) (lenv : LEnv) : list vdecl -> LEnv -> Prop :=

(* Elaborates an empty list of local variable declarations. *)
| EVarsNil : evars denv lenv [] lenv

(* Elaborates a non-empty list of local variable decls. *)
| EVarsCons :
    forall {vd lofvdecls lenv' lenv''},
      evar denv lenv vd lenv' ->
      evars denv lenv' lofvdecls lenv'' ->
      evars denv lenv (vd :: lofvdecls) lenv''

(** Defines the elaboration relation for one local variable declaration. *)
with evar (denv : DEnv) (lenv : LEnv) : vdecl -> LEnv -> Prop :=
| EVar :
    forall {tau t v id},
      
      (* Premises *)
      etype denv tau t ->
      defaultv t v ->

      (* Side conditions *)
      ~In id lenv ->            (* id ∉ Λ *)
      ~In id denv ->            (* id ∉ Δ *)

      (* Conclusion *)
      evar denv lenv (vdecl_ id tau) (add id (t, v) lenv).

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
      vexpr EmptyDEnv EmptyDState EmptyLEnv e v ->

      (* Side conditions *)
      ~In id dimen ->

      (* Conclusion *)
      eassocg dimen (assocg_ id e) (add id v dimen).
      

(** * Design elaboration relation. *)

(** Defines the design elaboration relation. *)

Inductive edesign (dstore : IdMap design) : IdMap value -> design -> DEnv -> DState -> Prop :=
| EDesign :
    forall {dimen entid archid gens ports adecls behavior
                  denv denv' denv'' denv''' dstate dstate' dstate''},

      (* Premises *)
      egens EmptyDEnv dimen gens denv ->
      eports denv EmptyDState ports denv' dstate ->
      edecls denv' dstate adecls denv'' dstate' ->
      ebeh dstore denv'' dstate' behavior denv''' dstate'' ->
      
      (* Conclusion *)
      edesign dstore dimen (design_ entid archid gens ports adecls behavior) denv''' dstate''    

(** Defines the relation that elaborates the concurrent statements
    defining the behavior of a design.  *)

with ebeh (dstore : IdMap design) : DEnv -> DState -> cs -> DEnv -> DState -> Prop :=

(** Elaborates and type-checks a process statement. *)
| EBehPs :
    forall {id sl vars stmt lenv denv dstate},

      (* Premises *)
      evars denv EmptyLEnv vars lenv ->
      validss denv dstate lenv stmt ->

      (* Side conditions *)
      ~In id denv ->
      (* sl ⊆ Ins(Δ) ∪ Sigs(Δ) *)
      (forall {s},
          NatSet.In s sl ->
          exists {t}, MapsTo s (Declared t) denv \/ MapsTo s (Input t) denv) ->

      (* Conclusion *)
      ebeh dstore denv dstate (cs_ps id sl vars stmt) (add id (Process lenv) denv) dstate

(** Elaborates and type-checks a component instantiation statement. *)
| EBehComp :
    forall {denv dstate idc ide gmap ipmap opmap
                 entid archid gens ports adecls behavior
                 dimen cenv cstate cdesign},

      (* Premises *)
      emapg (NatMap.empty value) gmap dimen ->
      edesign dstore dimen cdesign cenv cstate ->
      validipm denv cenv dstate ipmap ->
      validopm denv cenv opmap ->
      
      (* Side conditions *)
      cdesign = design_ entid archid gens ports adecls behavior ->
      MapsTo ide cdesign dstore ->
      (forall {g}, In g dimen -> exists {t v}, MapsTo g (Generic t v) cenv) ->
      
      (* Conclusion *)
      ebeh dstore denv dstate (cs_comp idc ide gmap ipmap opmap) denv dstate.
