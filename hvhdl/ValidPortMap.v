(** * Valid port map relations. *)

(** Defines the relations that check the validity of port maps
    encountered in the component instantiation statements that are
    part of the description of an H-VHDL design's behavior.  *)

Require Import Coqlib.
Require Import GlobalTypes.
Require Import Environment.
Require Import SemanticalDomains.
Require Import AbstractSyntax.
Require Import ExpressionEvaluation.
Require Import IsOfType.
Require Import StaticExpressions.

(** ** Valid port map for "in" mode ports. *)

(** Defines the relation that lists the connection of ports in a given
    "in" port map, i.e a port map where all formal parts of the
    associations corresponds to input port identifiers.
    
    - [denv] is the embedding design environment; remember that a port
      map appears in a component instantiation statement that is part
      of the behavior description for a higher-level design.

    - [cenv] is the design environment of the component instance.

    - [formals] lists the port identifiers that appears in the formal
      part of a port map.
    
      If a couple [(id, None)] appears in [formals], then [id] appears
      as a formal part of the port map.
      
      If a couple [(id, Some v)] appears in [formals], then [id(v)]
      appears as formal part of the port map.

 *)

Inductive listipm (denv cenv : DEnv) (dstate : DState) (formals : list (ident * option value)) :
  list associp -> list (ident * option value) -> Prop :=

(** An empty list of port associations does not change the [formals] list. *)
| ListIPMNil : listipm denv cenv dstate formals [] formals

(** Lists an non-empty list of port associations. *)
| ListIPMCons :
    forall {asip lofasips formals' formals''},
      eassocip denv cenv dstate formals asip formals' ->
      listipm denv cenv dstate formals' lofasips formals'' ->
      listipm denv cenv dstate formals (asip :: lofasips) formals''

(** Defines the relation that checks the validity of a single
    association present in an "in" port map.
 *)
with eassocip (denv cenv : DEnv) (dstate : DState) (formals : list (ident * option value)) :
  associp -> list (ident * option value) -> Prop :=

(** Checks an association with a simple port identifier (no index). *)
| EAssocipPartial :
    forall {id e v t},

      (* Premises *)
      vexpr denv dstate EmptyLEnv e v ->
      is_of_type v t ->

      (* Side conditions *)
      (forall {optv}, ~List.In (id, optv) formals) -> (* ∄ optv, (id, optv) ∈ formals *)
      MapsTo id (Input t) cenv ->                     (* id ∈ Ins(Δ_c) and Δ_c(id) = t *)

      (* Conclusion *)
      eassocip denv cenv dstate formals (associp_ (n_id id) e) (formals ++ [(id,None)])

(** Checks an association with a partial port identifier (with index). *)
| EAssocipSimple :
    forall {id ei e v vi t l u},

      (* Premises *)
      is_gstatic_expr denv ei ->
      vexpr denv dstate EmptyLEnv e v ->
      vexpr denv dstate EmptyLEnv ei vi ->
      is_of_type v t ->
      is_of_type vi (Tnat l u) ->
      
      (* Side conditions *)
      ~List.In (id, None) formals ->            (* (id, None) ∉ formals *)
      ~List.In (id, Some vi) formals ->         (* (id, Some vi) ∉ formals *)
      MapsTo id (Input (Tarray t l u)) cenv ->  (* id ∈ Ins(Δ_c) and Δ_c(id) = array(t,l,u) *)

      (* Conclusion *)
      eassocip denv cenv dstate formals (associp_ (n_xid id ei) e) (formals ++ [(id, Some vi)]).

(** Defines the predicate that checks the [formals] list (built by the
    [listipm] relation) against the component environment [cenv].  *)

Definition checkipm (cenv : DEnv) (formals : list (ident * option value)) : Prop :=
  forall (id : ident) (t : type),
    MapsTo id (Input t) cenv ->
    List.In (id, None) formals \/
    (exists {t' l u}, t = (Tarray t' l u) /\ forall {i}, l <= i <= u -> List.In (id, Some (Vnat i)) formals).

(** Defines the predicate stating that an "in" port map is valid. *)

Inductive validipm (denv cenv : DEnv) (dstate : DState) (ipmap : list associp) : Prop :=
| ValidIpm :
    forall {formals},
      listipm denv cenv dstate [] ipmap formals ->
      checkipm cenv formals ->
      validipm denv cenv dstate ipmap.

(** ** Valid port map for "out" mode ports. *)

(** Defines the relation that lists and checks the port identifiers
    present in an "out" port map. *)

Inductive listopm (denv cenv : DEnv) (formals actuals : list (ident * option value)) :
  list assocop -> list (ident * option value) -> list (ident * option value) -> Prop :=

(** An empty list of port associations does not change the [formals]
    and [actuals] list. *)
| ListOPMNil : listopm denv cenv formals actuals [] formals actuals

(** Lists an non-empty list of port associations. *)
| ListOPMCons :
    forall {aspo lofaspos formals' actuals' formals'' actuals''},
      eassocop denv cenv formals actuals aspo formals' actuals' ->
      listopm denv cenv formals' actuals' lofaspos formals'' actuals'' ->
      listopm denv cenv formals actuals (aspo :: lofaspos) formals'' actuals''

(** Defines the relation that checks the validity of an association 
    present in an "out" port map.
 *)

with eassocop (denv cenv : DEnv) (formals actuals : list (ident * option value)) :
  assocop -> list (ident * option value) -> list (ident * option value) -> Prop :=

(** Checks an "out" port map association of the form "idf => ida", where 
    the actual part refers to a declared signal identifier.
 *)
| EAssocopSimpleToSimpleDecl :
    forall {idf ida t},
      
      (* Side conditions *)
      (forall {optv}, ~List.In (idf, optv) formals) -> 
      (forall {optv}, ~List.In (ida, optv) actuals) ->

      (* idf and ida have the same type. *)
      MapsTo idf (Output t) cenv ->
      MapsTo ida (Declared t) denv ->

      (* Conclusion *)
      eassocop denv cenv formals actuals
               (assocop_ (n_id idf) (Some (n_id ida)))
               (formals ++ [(idf, None)]) (actuals ++ [(ida, None)])

(** Checks an "out" port map association of the form "idf => ida", where 
    the actual part refers to an output port identifier.
 *)
| EAssocopSimpleToSimpleOut :
    forall {idf ida t},
      
      (* Side conditions *)
      (forall {optv}, ~List.In (idf, optv) formals) -> 
      (forall {optv}, ~List.In (ida, optv) actuals) ->

      (* idf and ida have the same type. *)
      MapsTo idf (Output t) cenv ->
      MapsTo ida (Output t) denv ->

      (* Conclusion *)
      eassocop denv cenv formals actuals
               (assocop_ (n_id idf) (Some (n_id ida)))
               (formals ++ [(idf, None)]) (actuals ++ [(ida, None)])

(** Checks an "out" port map association of the form "idf => ida(ei)", where 
    the actual part refers to a declared signal identifier.
 *)
| EAssocopSimpleToPartialDecl :
    forall {idf ida ei vi t l u},

      (* Premises *)
      is_gstatic_expr denv ei ->
      vexpr denv EmptyDState EmptyLEnv ei vi ->
      is_of_type vi (Tnat l u) ->
      
      (* Side conditions *)
      (forall {optv}, ~List.In (idf, optv) formals) -> 
      ~List.In (ida, None) actuals ->
      ~List.In (ida, Some vi) actuals ->

      (* idf and ida(ei) have the same type. *)
      MapsTo idf (Output t) cenv ->
      MapsTo ida (Declared (Tarray t l u)) denv ->

      (* Conclusion *)
      eassocop denv cenv formals actuals
               (assocop_ (n_id idf) (Some (n_xid ida ei)))
               (formals ++ [(idf, None)]) (actuals ++ [(ida, Some vi)])

(** Checks an "out" port map association of the form "idf => ida(ei)", where 
    the actual part refers to a declared signal identifier.
 *)
| EAssocopSimpleToPartialOut :
    forall {idf ida ei vi t l u},

      (* Premises *)
      is_gstatic_expr denv ei ->
      vexpr denv EmptyDState EmptyLEnv ei vi ->
      is_of_type vi (Tnat l u) ->
      
      (* Side conditions *)
      (forall {optv}, ~List.In (idf, optv) formals) -> 
      ~List.In (ida, None) actuals ->
      ~List.In (ida, Some vi) actuals ->

      (* idf and ida(ei) have the same type. *)
      MapsTo idf (Output t) cenv ->
      MapsTo ida (Output (Tarray t l u)) denv ->

      (* Conclusion *)
      eassocop denv cenv formals actuals
               (assocop_ (n_id idf) (Some (n_xid ida ei)))
               (formals ++ [(idf, None)]) (actuals ++ [(ida, Some vi)])

(** Checks an "out" port map association of the form "idf => open". *)
| EAssocopSimpleToOpen :
    forall {idf t},
      
      (* Side conditions *)
      (forall {optv}, ~List.In (idf, optv) formals) -> 
      MapsTo idf (Output t) cenv ->

      (* Conclusion *)
      eassocop denv cenv formals actuals
               (assocop_ (n_id idf) None)
               (formals ++ [(idf,None)]) actuals

(** Checks an "out" port map association of the form "idf(ei) => open". *)
| EAssocopPartialToOpen :
    forall {idf ei vi t l u},

      (* Premises *)
      is_gstatic_expr denv ei ->
      vexpr denv EmptyDState EmptyLEnv ei vi ->
      is_of_type vi (Tnat l u) ->
      
      (* Side conditions *)
      ~List.In (idf, None) formals ->
      ~List.In (idf, Some vi) formals ->
      MapsTo idf (Output (Tarray t l u)) cenv ->

      (* Conclusion *)
      eassocop denv cenv formals actuals
               (assocop_ (n_xid idf ei) None)
               (formals ++ [(idf, Some vi)]) actuals

(** Checks an "out" port map association of the form "idf(ei) => ida",
    where ida refers to a declared signal identifier. *)
| EAssocopPartialToSimpleDecl :
    forall {idf ei ida vi t l u},

      (* Premises *)
      is_gstatic_expr denv ei ->
      vexpr denv EmptyDState EmptyLEnv ei vi ->
      is_of_type vi (Tnat l u) ->
      
      (* Side conditions *)
      ~List.In (idf, None) formals ->
      ~List.In (idf, Some vi) formals ->
      (forall {optv}, ~List.In (ida, optv) actuals) ->
      MapsTo idf (Output (Tarray t l u)) cenv ->
      MapsTo ida (Declared t) denv ->

      (* Conclusion *)
      eassocop denv cenv formals actuals
               (assocop_ (n_xid idf ei) (Some (n_id ida)))
               (formals ++ [(idf, Some vi)]) (actuals ++ [(ida, None)])

(** Checks an "out" port map association of the form "idf(ei) => ida",
    where ida refers to an output port identifier. *)
| EAssocopPartialToSimpleOut :
    forall {idf ei ida vi t l u},

      (* Premises *)
      is_gstatic_expr denv ei ->
      vexpr denv EmptyDState EmptyLEnv ei vi ->
      is_of_type vi (Tnat l u) ->
      
      (* Side conditions *)
      ~List.In (idf, None) formals ->
      ~List.In (idf, Some vi) formals ->
      (forall {optv}, ~List.In (ida, optv) actuals) ->
      MapsTo idf (Output (Tarray t l u)) cenv ->
      MapsTo ida (Output t) denv ->

      (* Conclusion *)
      eassocop denv cenv formals actuals
               (assocop_ (n_xid idf ei) (Some (n_id ida)))
               (formals ++ [(idf, Some vi)]) (actuals ++ [(ida, None)])
               
(** Checks an "out" port map association of the form "idf(ei) => ida(ei')",
    where ida refers to a declared signal identifier. *)
| EAssocopPartialToPartialDecl :
    forall {idf ei ida ei' vi vi' t l u l' u'},

      (* Premises *)
      is_gstatic_expr denv ei ->
      is_gstatic_expr denv ei' ->
      vexpr denv EmptyDState EmptyLEnv ei vi ->
      vexpr denv EmptyDState EmptyLEnv ei' vi' ->
      is_of_type vi (Tnat l u) ->
      is_of_type vi' (Tnat l' u') ->
      
      (* Side conditions *)
      ~List.In (idf, None) formals ->
      ~List.In (idf, Some vi) formals ->
      ~List.In (ida, None) actuals ->
      ~List.In (ida, Some vi') actuals ->
      MapsTo idf (Output (Tarray t l u)) cenv ->
      MapsTo ida (Declared (Tarray t l' u')) denv ->

      (* Conclusion *)
      eassocop denv cenv formals actuals
               (assocop_ (n_xid idf ei) (Some (n_xid ida ei')))
               (formals ++ [(idf, Some vi)]) (actuals ++ [(ida, Some vi')])
               
(** Checks an "out" port map association of the form "idf(ei) => ida(ei')",
    where ida refers to an output port identifier. *)
| EAssocopPartialToPartialOut :
    forall {idf ei ida ei' vi vi' t l u l' u'},

      (* Premises *)
      is_gstatic_expr denv ei ->
      is_gstatic_expr denv ei' ->
      vexpr denv EmptyDState EmptyLEnv ei vi ->
      vexpr denv EmptyDState EmptyLEnv ei' vi' ->
      is_of_type vi (Tnat l u) ->
      is_of_type vi' (Tnat l' u') ->
      
      (* Side conditions *)
      ~List.In (idf, None) formals ->
      ~List.In (idf, Some vi) formals ->
      ~List.In (ida, None) actuals ->
      ~List.In (ida, Some vi') actuals ->
      MapsTo idf (Output (Tarray t l u)) cenv ->
      MapsTo ida (Output (Tarray t l' u')) denv ->

      (* Conclusion *)
      eassocop denv cenv formals actuals
               (assocop_ (n_xid idf ei) (Some (n_xid ida ei')))
               (formals ++ [(idf, Some vi)]) (actuals ++ [(ida, Some vi')]).

(** Defines the relation that checks the validity of an "out" port
    map. *)

Inductive validopm (denv cenv : DEnv) (opmap : list assocop) : Prop :=
| ValidOPM :
    forall {formals actuals},
      listopm denv cenv [] [] opmap formals actuals ->
      validopm denv cenv opmap.
    



