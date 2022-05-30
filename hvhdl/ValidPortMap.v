(** * Valid port map relations. *)

(** Defines the relations that check the validity of port maps
    encountered in the component instantiation statements that are
    part of the description of an H-VHDL design's behavior.  *)

Require Import common.CoqLib.
Require Import common.GlobalTypes.
Require Import common.NatMap.

Require Import hvhdl.Environment.
Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.ExpressionEvaluation.
Require Import hvhdl.StaticExpressions.
Require Import hvhdl.HVhdlTypes.

Open Scope N_scope.

(** ** Valid check for input port maps *)

(** Defines the relation that lists the connection of ports in a given
    input port map, i.e a port map where all formal parts of the
    associations corresponds to input port identifiers.
    
    - [Δ] represents the embedding design in its elaborated version;
      remember that a port map appears in a design instantiation
      statement that is part of the behavior description for a
      embedding design.

    - [Δ__c] is the design instance in its elaborated version.

    - [sst] is the signal store of the default design state being
      constructed by the elaboration phase.

    - [formals] lists the port identifiers that appears in the formal
      part of a port map.
    
      If a couple [(id, None)] appears in [formals], then [id] appears
      as a formal part of the port map.
      
      If a couple [(id, Some v)] appears in [formals], then [id(v)]
      appears as formal part of the port map.  *)

Inductive ListIPM (Δ Δ__c : ElDesign) (sst : IdMap value) (formals : list (ident * option N)) :
  list ipassoc -> list (ident * option N) -> Prop :=
  
(** An empty list of port associations does not change the [formals] list. *)
| ListIPMNil : ListIPM Δ Δ__c sst formals [] formals

(** Lists an non-empty list of port associations. *)
| ListIPMCons :
    forall ipa lofipas formals' formals'',
      EIPAssoc Δ Δ__c sst formals ipa formals' ->
      ListIPM Δ Δ__c sst formals' lofipas formals'' ->
      ListIPM Δ Δ__c sst formals (ipa :: lofipas) formals''

(** Defines the relation that checks the validity of a single input
    port map association. *)
              
with EIPAssoc (Δ Δ__c : ElDesign) (sst : IdMap value) (formals : list (ident * option N)) :
  ipassoc -> list (ident * option N) -> Prop :=

(** Checks an association with a simple port identifier (no index). *)
| EIPAssocSimple :
    forall id e v t,

      (* Premises *)
      VExpr Δ sst EmptyLEnv false e v ->
      IsOfType v t ->

      (* Side conditions *)
      (~exists optn, List.In (id, optn) formals) ->  (* (id, optn) ∉ formals *)
      MapsTo id (Input t) Δ__c -> (* [id ∈ Ins(Δ__c) and Δ__c(id) = t] *)

      (* Conclusion *)
      EIPAssoc Δ Δ__c sst formals (ipa_ (n_id id) e) (formals ++ [(id, None)])

(** Checks an association with a partial port identifier (with index). *)
| EIPAssocPartial :
    forall id ei e v i t l u,

      (* Premises *)
      IGStaticExpr Δ ei ->
      VExpr Δ sst EmptyLEnv false e v ->
      VExpr Δ sst EmptyLEnv false ei (Vnat i) ->
      IsOfType v t ->
      IsOfType (Vnat i) (Tnat l u) ->
      
      (* Side conditions *)
      ~List.In (id, None) formals -> (* (id, None) ∉ formals *)
      ~List.In (id, Some i) formals -> (* (id, Some i) ∉ formals *)
      MapsTo id (Input (Tarray t l u)) Δ__c ->  (* [id ∈ Ins(Δ__c) and Δ__c(id) = array(t,l,u)] *)

      (* Conclusion *)
      EIPAssoc Δ Δ__c sst formals (ipa_ (n_xid id ei) e) (formals ++ [(id, Some i)]).

#[export] Hint Constructors ListIPM : hvhdl.
#[export] Hint Constructors EIPAssoc : hvhdl.

(** Defines the predicate that checks the [formals] list (built by the
    [ListIPM] relation) against the component environment [Δ__c].

    For all input port identifier declared in the elaborated design
    [Δ__c], the identifier must appear as a left part of a couple in the
    [formals] list. If the input port identifier is of the array type,
    then all its subelements must appear as a left part of a couple in
    the [formals] list. *)

Definition CheckFormals (Δ__c : ElDesign) (formals : list (ident * option N)) : Prop :=
  forall (id : ident) (t : type),
    MapsTo id (Input t) Δ__c ->
    match t with
    | Tbool | Tnat _ _ => List.In (id, None) formals
    | Tarray t' l u => List.In (id, None) formals \/ forall i, l <= i <= u -> List.In (id, Some i) formals
    end.

(** Defines the predicate stating that an input port map is valid. *)

Inductive ValidIPM (Δ Δ__c : ElDesign) (sst : IdMap value) (i : inputmap) : Prop :=
| ValidIPM_ (formals : list (ident * option N)) :  
  ListIPM Δ Δ__c sst [] i formals ->
  CheckFormals Δ__c formals ->
  ValidIPM Δ Δ__c sst i.

(** ** Validity check for output port maps. *)

(** Defines the relation that lists and checks the port identifiers
    present in an output port map. *)

Inductive ListOPM (Δ Δ__c : ElDesign) (formals : list (ident * option N)) :
  list opassoc -> list (ident * option N) -> Prop :=

(** An empty list of port associations does not change the [formals]
    list. *)
| ListOPMNil : ListOPM Δ Δ__c formals [] formals

(** Lists an non-empty list of port associations. *)
| ListOPMCons :
    forall opa lofopas formals' formals'',
      EOPAssoc Δ Δ__c formals opa formals' ->
      ListOPM Δ Δ__c formals' lofopas formals'' ->
      ListOPM Δ Δ__c formals (opa :: lofopas) formals''

(** Defines the relation that checks the validity of an output port
    map association.  *)

with EOPAssoc (Δ Δ__c : ElDesign) (formals : list (ident * option N)) :
  opassoc -> list (ident * option N) -> Prop :=

(** Checks an output port map association of the form [idf ⇒ ida],
    where [ida] refers to a declared signal or an output port
    identifier of the embedding elaborated design.  *)
| EOPAssocSimpleToSimple :
    forall idf ida t,
      
      (* Side conditions *)
      (forall optv, ~List.In (idf, optv) formals) -> 

      (* idf and ida have the same type. *)
      MapsTo idf (Output t) Δ__c -> (* [idf ∈ Outs(Δ__c)] *)
      (* [ida ∈ Sigs(Δ) ∪ Outs(Δ)] *)
      MapsTo ida (Declared t) Δ \/ MapsTo ida (Output t) Δ ->

      (* Conclusion *)
      EOPAssoc Δ Δ__c formals (opa_simpl idf (Some (n_id ida))) (formals ++ [(idf, None)])

(** Checks an output port map association of the form [idf ⇒ ida(ei)],
    where the actual part refers to a composite declared signal or
    output port identifier .  *)
               
| EOPAssocSimpleToPartial :
    forall idf ida ei i t l u,

      (* Premises *)
      IGStaticExpr Δ ei ->
      VExpr Δ EmptySStore EmptyLEnv false ei (Vnat i) ->
      IsOfType (Vnat i) (Tnat l u) ->
      
      (* Side conditions *)
      (forall optv, ~List.In (idf, optv) formals) -> 

      (* idf and ida(ei) have the same type. *)
      MapsTo idf (Output t) Δ__c ->
      MapsTo ida (Declared (Tarray t l u)) Δ \/ MapsTo ida (Output (Tarray t l u)) Δ ->

      (* Conclusion *)
      EOPAssoc Δ Δ__c formals (opa_simpl idf (Some (n_xid ida ei))) (formals ++ [(idf, None)])

(** Checks an output port map association of the form [idf ⇒ open]. *)
| EOPAssocSimpleToOpen :
    forall idf t,
      
      (* Side conditions *)
      (forall optv, ~List.In (idf, optv) formals) -> 
      MapsTo idf (Output t) Δ__c ->

      (* Conclusion *)
      EOPAssoc Δ Δ__c formals (opa_simpl idf None) (formals ++ [(idf,None)])

(** Checks an output port map association of the form [idf(ei) ⇒ ida],
    where [ida] refers to a declared signal or an output port
    identifier. *)
| EOPAssocPartialToSimple :
    forall idf ei ida i t l u,

      (* Premises *)
      IGStaticExpr Δ ei ->
      VExpr Δ EmptySStore EmptyLEnv false ei (Vnat i) ->
      IsOfType (Vnat i) (Tnat l u) ->
      
      (* Side conditions *)
      ~List.In (idf, None) formals ->
      ~List.In (idf, Some i) formals ->
      MapsTo idf (Output (Tarray t l u)) Δ__c ->
      MapsTo ida (Declared t) Δ \/ MapsTo ida (Output t) Δ ->

      (* Conclusion *)
      EOPAssoc Δ Δ__c formals (opa_idx idf ei ($ida)) (formals ++ [(idf, Some i)])
               
(** Checks an output port map association of the form [idf(ei) =>
    ida(ei')], where [ida] refers to a declared signal or an output
    port identifier. *)
               
| EOPAssocPartialToPartial :
    forall idf ei ida ei' i i' t l u l' u',

      (* Premises *)
      IGStaticExpr Δ ei ->
      IGStaticExpr Δ ei' ->
      VExpr Δ EmptySStore EmptyLEnv false ei (Vnat i) ->
      VExpr Δ EmptySStore EmptyLEnv false ei' (Vnat i') ->
      IsOfType (Vnat i) (Tnat l u) ->
      IsOfType (Vnat i') (Tnat l' u') ->
      
      (* Side conditions *)
      ~List.In (idf, None) formals ->
      ~List.In (idf, Some i) formals ->
      MapsTo idf (Output (Tarray t l u)) Δ__c ->
      MapsTo ida (Declared (Tarray t l' u')) Δ \/ MapsTo ida (Output (Tarray t l' u')) Δ ->

      (* Conclusion *)
      EOPAssoc Δ Δ__c formals (opa_idx idf ei (ida$[[ei']])) (formals ++ [(idf, Some i)]).

#[export] Hint Constructors ListOPM : hvhdl.
#[export] Hint Constructors EOPAssoc : hvhdl.

(** Defines the relation that checks the validity of an output port
    map. *)

Inductive ValidOPM (Δ Δ__c : ElDesign) (o : list opassoc) : Prop :=
| ValidOPM_ (formals : list (ident * option N)) :  
  ListOPM Δ Δ__c [] o formals ->
  ValidOPM Δ Δ__c o.
    



