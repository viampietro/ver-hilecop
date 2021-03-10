(** * Valid port map relations. *)

(** Defines the relations that check the validity of port maps
    encountered in the component instantiation statements that are
    part of the description of an H-VHDL design's behavior.  *)

Require Import common.CoqLib.
Require Import common.GlobalTypes.

Require Import hvhdl.Environment.
Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.ExpressionEvaluation.
Require Import hvhdl.StaticExpressions.
Require Import hvhdl.HVhdlTypes.

Local Open Scope nat_scope.

(** ** Valid port map for "in" mode ports. *)

(** Defines the relation that lists the connection of ports in a given
    "in" port map, i.e a port map where all formal parts of the
    associations corresponds to input port identifiers.
    
    - [Δ] is the embedding design environment; remember that a port
      map appears in a component instantiation statement that is part
      of the behavior description for a higher-level design.

    - [Δ__c] is the design environment of the component instance.

    - [formals] lists the port identifiers that appears in the formal
      part of a port map.
    
      If a couple [(id, None)] appears in [formals], then [id] appears
      as a formal part of the port map.
      
      If a couple [(id, Some v)] appears in [formals], then [id(v)]
      appears as formal part of the port map.

 *)

Inductive listipm (Δ Δ__c : ElDesign) (σ : DState) (formals : list (ident * option nat)) :
  list associp -> list (ident * option nat) -> Prop :=
  
(** An empty list of port associations does not change the [formals] list. *)
| ListIPMNil : listipm Δ Δ__c σ formals [] formals

(** Lists an non-empty list of port associations. *)
| ListIPMCons :
    forall asip lofasips formals' formals'',
      eassocip Δ Δ__c σ formals asip formals' ->
      listipm Δ Δ__c σ formals' lofasips formals'' ->
      listipm Δ Δ__c σ formals (asip :: lofasips) formals''

(** Defines the relation that checks the validity of a single
    association present in an "in" port map. *)
with eassocip (Δ Δ__c : ElDesign) (σ : DState) (formals : list (ident * option nat)) :
  associp -> list (ident * option nat) -> Prop :=

(** Checks an association with a simple port identifier (no index). *)
| EAssocipSimple :
    forall id e v t,

      (* Premises *)
      vexpr Δ σ EmptyLEnv false e v ->
      is_of_type v t ->

      (* Side conditions *)
      (~exists optn, List.In (id, optn) formals) ->  (* (id, optn) ∉ formals *)
      MapsTo id (Input t) Δ__c -> (* [id ∈ Ins(Δ__c) and Δ__c(id) = t] *)

      (* Conclusion *)
      eassocip Δ Δ__c σ formals (associp_ (n_id id) e) (formals ++ [(id, None)])

(** Checks an association with a partial port identifier (with index). *)
| EAssocipPartial :
    forall id ei e v i t l u,

      (* Premises *)
      is_gstatic_expr Δ ei ->
      vexpr Δ σ EmptyLEnv false e v ->
      vexpr Δ σ EmptyLEnv false ei (Vnat i) ->
      is_of_type v t ->
      is_of_type (Vnat i) (Tnat l u) ->
      
      (* Side conditions *)
      ~List.In (id, None) formals -> (* (id, None) ∉ formals *)
      ~List.In (id, Some i) formals ->
      MapsTo id (Input (Tarray t l u)) Δ__c ->  (* [id ∈ Ins(Δ__c) and Δ__c(id) = array(t,l,u)] *)

      (* Conclusion *)
      eassocip Δ Δ__c σ formals (associp_ (n_xid id ei) e) (formals ++ [(id, Some i)]).

Hint Constructors listipm : hvhdl.
Hint Constructors eassocip : hvhdl.

(** Defines the predicate that checks the [formals] list (built by the
    [listipm] relation) against the component environment [Δ__c].  *)

Definition checkformals (Δ__c : ElDesign) (formals : list (ident * option nat)) : Prop :=
  forall (id : ident),
    (MapsTo id (Input Tbool) Δ__c \/ (exists l u, MapsTo id (Input (Tnat l u)) Δ__c) <-> List.In (id, None) formals)
    /\ (forall t l u, MapsTo id (Input (Tarray t l u)) Δ__c -> forall i, l <= i <= u -> List.In (id, Some i) formals)
    /\ (forall i, List.In (id, Some i) formals -> exists t l u, MapsTo id (Input (Tarray t l u)) Δ__c /\ l <= i <= u).

(** Defines the predicate stating that an "in" port map is valid. *)

Definition validipm (Δ Δ__c : ElDesign) (σ : DState) (ipmap : list associp) (formals : list (ident * option nat)) : Prop :=
  listipm Δ Δ__c σ [] ipmap formals /\ checkformals Δ__c formals.

(** ** Valid port map for "out" mode ports. *)

(** Defines the relation that lists and checks the port identifiers
    present in an "out" port map. *)

Inductive listopm (Δ Δ__c : ElDesign) (formals actuals : list (ident * option nat)) :
  list assocop -> list (ident * option nat) -> list (ident * option nat) -> Prop :=

(** An empty list of port associations does not change the [formals]
    and [actuals] list. *)
| ListOPMNil : listopm Δ Δ__c formals actuals [] formals actuals

(** Lists an non-empty list of port associations. *)
| ListOPMCons :
    forall aspo lofaspos formals' actuals' formals'' actuals'',
      eassocop Δ Δ__c formals actuals aspo formals' actuals' ->
      listopm Δ Δ__c formals' actuals' lofaspos formals'' actuals'' ->
      listopm Δ Δ__c formals actuals (aspo :: lofaspos) formals'' actuals''

(** Defines the relation that checks the validity of an association 
    present in an "out" port map.
 *)

with eassocop (Δ Δ__c : ElDesign) (formals actuals : list (ident * option nat)) :
  assocop -> list (ident * option nat) -> list (ident * option nat) -> Prop :=

(** Checks an "out" port map association of the form "idf => ida",
    where [ida] refers to a declared signal or an output port
    identifier of the embedding elaborated design.  *)
| EAssocopSimpleToSimple :
    forall idf ida t,
      
      (* Side conditions *)
      (forall optv, ~List.In (idf, optv) formals) -> 
      (forall optv, ~List.In (ida, optv) actuals) ->

      (* idf and ida have the same type. *)
      MapsTo idf (Output t) Δ__c -> (* [idf ∈ Outs(Δ__c)] *)
      (* [ida ∈ Sigs(Δ) ∪ Outs(Δ)] *)
      MapsTo ida (Declared t) Δ \/ MapsTo ida (Output t) Δ ->

      (* Conclusion *)
      eassocop Δ Δ__c formals actuals
               (assocop_simpl idf (Some (n_id ida)))
               (formals ++ [(idf, None)]) (actuals ++ [(ida, None)])

(** Checks an "out" port map association of the form "idf => ida(ei)", where 
    the actual part refers to a declared signal identifier.
 *)
| EAssocopSimpleToPartial :
    forall idf ida ei i t l u,

      (* Premises *)
      is_gstatic_expr Δ ei ->
      vexpr Δ EmptyDState EmptyLEnv false ei (Vnat i) ->
      is_of_type (Vnat i) (Tnat l u) ->
      
      (* Side conditions *)
      (forall optv, ~List.In (idf, optv) formals) -> 
      ~List.In (ida, None) actuals ->
      ~List.In (ida, Some i) actuals ->

      (* idf and ida(ei) have the same type. *)
      MapsTo idf (Output t) Δ__c ->
      MapsTo ida (Declared (Tarray t l u)) Δ \/ MapsTo ida (Output (Tarray t l u)) Δ ->

      (* Conclusion *)
      eassocop Δ Δ__c formals actuals
               (assocop_simpl idf (Some (n_xid ida ei)))
               (formals ++ [(idf, None)]) (actuals ++ [(ida, Some i)])

(** Checks an "out" port map association of the form "idf => open". *)
| EAssocopSimpleToOpen :
    forall idf t,
      
      (* Side conditions *)
      (forall optv, ~List.In (idf, optv) formals) -> 
      MapsTo idf (Output t) Δ__c ->

      (* Conclusion *)
      eassocop Δ Δ__c formals actuals
               (assocop_simpl idf None)
               (formals ++ [(idf,None)]) actuals

(** Checks an "out" port map association of the form "idf(ei) => ida",
    where [ida] refers to a declared signal or an output port identifier. *)
| EAssocopPartialToSimple :
    forall idf ei ida i t l u,

      (* Premises *)
      is_gstatic_expr Δ ei ->
      vexpr Δ EmptyDState EmptyLEnv false ei (Vnat i) ->
      is_of_type (Vnat i) (Tnat l u) ->
      
      (* Side conditions *)
      ~List.In (idf, None) formals ->
      ~List.In (idf, Some i) formals ->
      (forall optv, ~List.In (ida, optv) actuals) ->
      MapsTo idf (Output (Tarray t l u)) Δ__c ->
      MapsTo ida (Declared t) Δ \/ MapsTo ida (Output t) Δ ->

      (* Conclusion *)
      eassocop Δ Δ__c formals actuals
               (assocop_idx idf ei ($ida))
               (formals ++ [(idf, Some i)]) (actuals ++ [(ida, None)])
               
(** Checks an "out" port map association of the form "idf(ei) => ida(ei')",
    where [ida] refers to a declared signal or an output port identifier. *)
| EAssocopPartialToPartial :
    forall idf ei ida ei' i i' t l u l' u',

      (* Premises *)
      is_gstatic_expr Δ ei ->
      is_gstatic_expr Δ ei' ->
      vexpr Δ EmptyDState EmptyLEnv false ei (Vnat i) ->
      vexpr Δ EmptyDState EmptyLEnv false ei' (Vnat i') ->
      is_of_type (Vnat i) (Tnat l u) ->
      is_of_type (Vnat i') (Tnat l' u') ->
      
      (* Side conditions *)
      ~List.In (idf, None) formals ->
      ~List.In (idf, Some i) formals ->
      ~List.In (ida, None) actuals ->
      ~List.In (ida, Some i') actuals ->
      MapsTo idf (Output (Tarray t l u)) Δ__c ->
      MapsTo ida (Declared (Tarray t l' u')) Δ \/ MapsTo ida (Output (Tarray t l' u')) Δ ->

      (* Conclusion *)
      eassocop Δ Δ__c formals actuals
               (assocop_idx idf ei (ida$[[ei']]))
               (formals ++ [(idf, Some i)]) (actuals ++ [(ida, Some i')]).

Hint Constructors listopm : hvhdl.
Hint Constructors eassocop : hvhdl.

(** Defines the relation that checks the validity of an "out" port
    map. *)

Definition validopm (Δ Δ__c : ElDesign) (opmap : list assocop)
           (formals actuals : list (ident * option nat)) : Prop :=
  listopm Δ Δ__c [] [] opmap formals actuals.
    



