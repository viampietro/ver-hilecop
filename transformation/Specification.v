(** * Specification of the HILECOP model-to-text transformation (HM2T) *)

Require Import common.CoqLib.
Require Import common.GlobalTypes.
Require Import common.GlobalFacts.
Require Import common.ListPlus.

Require Import sitpn.Sitpn.
Require Import sitpn.SitpnTypes.
Require Import sitpn.SitpnFacts.
Require Import sitpn.SitpnUtils.
Require Import sitpn.SitpnWellDefined.

Require Import transformation.Sitpn2HVhdlTypes.

Require Import hvhdl.HVhdlCoreLib.
Require Import hvhdl.HVhdlElaborationLib.
Require Import hvhdl.HVhdlHilecopLib.

Require Import transformation.Sitpn2HVhdlUtils.

Include HVhdlSsNotations.

(** Specifies the relation between an input SITPN model and bounding
    function, and an output H-VHDL design and binder resulting from
    the HM2T. *)

Record HM2T_
  (sitpn : Sitpn)
  (b : P sitpn -> nat)
  (d : design)
  (γ : Sitpn2HVhdlBinder sitpn) : Prop :=
  
  MkHM2T_ {

      (** Design [d] has an empty set of generic constants. *)
      emp_gens : (gens d) = [];

      (** There is the same number of conditions in [sitpn] than of
          input ports in [d]. *)
      eq_conds_inports :
      let inports := filter (fun pd : pdecl => if pd then true else false) (ports d) in
      length inports = length (conditions sitpn);

      (** There is the same number of actions and functions in [sitpn]
          than of output ports in [d]. *)
      eq_acts_funs_outports :
      let outports := filter (fun pd : pdecl => if pd then false else true) (ports d) in
      length outports = length (actions sitpn) + length (functions sitpn);

      (** Design d is elaborable in the context of the HILECOP design
          store and given an empty dimensioning function. *)
      d_is_elaborable :
      exists Δ σ__e, EDesign hdstore (NatMap.empty value) d Δ σ__e;

      (** All design instantiation statement in the design’s behavior
          either creates a PDI or a TDI *)
      pdi_or_tdi :
      forall id__c id__e g i o,
        InCs (cs_comp id__c id__e g i o) (beh d) ->
        id__e = place_id \/ id__e = trans_id;
      
      (** The actions and functions processes are the only two
          processes in the design’s behavior. *)
      actions_or_functions : 
      forall id vars stmt,
        InCs (cs_ps id vars stmt) (beh d) ->
        id = actions_ps_id \/ id = functions_ps_id;
      
      (** All the fields of the SITPN-to-H-VHDL binder are bijective
          applications. *)
      bij_binder :
      let is_pdi_id id__c := exists g i o, InCs (cs_comp id__c place_id g i o) (beh d) in
      let is_tdi_id id__c := exists g i o, InCs (cs_comp id__c trans_id g i o) (beh d) in
      let is_op_id id := exists τ, In (pdecl_out id τ) (ports d) in
      let is_ip_id id := exists τ, In (pdecl_in id τ) (ports d) in
      let AFEq af1 af2 :=
        match af1, af2 with
          inl x1, inl x2 | inr x1, inr x2 => P1SigEq x1 x2
        | _, _ => False
        end in                              
      
      IsBijectiveP Peq eq is_pdi_id (p2pdi γ)
      /\ IsBijectiveP Teq eq is_tdi_id (t2tdi γ)
      /\ IsBijectiveP AFEq eq is_op_id (merge_dom (a2out γ) (f2out γ))
      /\ IsBijectiveP Ceq eq is_ip_id (c2in γ);

      (** For all place of the input SITPN model, there exists a
          corresponding place design instance (PDI) identified through
          γ in the behavior of the output design *)
      ex_pdi :
      forall p,
      exists id__p g__p i__p o__p,
        getv Peqdec p (p2pdi γ) = Some id__p
        /\ InCs (cs_comp id__p place_id g__p i__p o__p) (beh d);

      (** For all place of the input SITPN model and its corresponding
          PDI, the generic map of the PDI holds the following associations *)
      pdi_gen_map :
      forall p id__p g__p i__p o__p,
        getv Peqdec p (p2pdi γ) = Some id__p ->
        InCs (cs_comp id__p place_id g__p i__p o__p) (beh d) ->
        g__p = [(ga_ maximal_marking (b p));
              (ga_ Place.input_arcs_number (if inputs_of_p p then 1 else length (inputs_of_p p)));
              (ga_ Place.output_arcs_number (if outputs_of_p p then 1 else length (outputs_of_p p)))
          ];

      (** For all place of the input SITPN model and its corresponding
          PDI, there is an association between the [initial_marking]
          input port and the initial marking of the place in the input
          port map of the PDI *)
      pdi_init_marking :
      forall p id__p g__p i__p o__p,
        getv Peqdec p (p2pdi γ) = Some id__p ->
        InCs (cs_comp id__p place_id g__p i__p o__p) (beh d) ->
        In (ipa_ initial_marking (M0 p)) i__p;

      (** For all place of the SITPN model with no input transition,
          the input port map of the corresponding PDI includes the following
          associations. *)
      pdi_no_input :
      forall p id__p g__p i__p o__p,
        inputs_of_p p = [] ->
        getv Peqdec p (p2pdi γ) = Some id__p ->
        InCs (cs_comp id__p place_id g__p i__p o__p) (beh d) ->
        incl [(ipa_ (input_arcs_weights $[[0]]) 0);
              (ipa_ (input_transitions_fired $[[0]]) false)] i__p;

      (** For all place of the SITPN model with no output transition,
          the input port map and output port map of the corresponding PDI
          includes the following associations *)
      pdi_no_output :
      forall p id__p g__p i__p o__p,
        outputs_of_p p = [] ->
        getv Peqdec p (p2pdi γ) = Some id__p ->
        InCs (cs_comp id__p place_id g__p i__p o__p) (beh d) ->
        incl [(ipa_ (output_arcs_weights $[[0]]) 0);
              (ipa_ (output_arcs_types $[[0]]) basic);
              (ipa_ (output_transitions_fired $[[0]]) false)] i__p
        /\ incl [(opa_simpl output_arcs_valid None);
                 (opa_simpl Place.priority_authorizations None);
                 (opa_simpl reinit_transitions_time None)] o__p;

      (** For all place of the SITPN model with no action, the marked
          output port is left unconnected in the output port map of the
          corresponding PDI. *)
      pdi_no_action:
      forall p id__p g__p i__p o__p,
        acts_of_p p = [] ->
        getv Peqdec p (p2pdi γ) = Some id__p ->
        InCs (cs_comp id__p place_id g__p i__p o__p) (beh d) ->
        In (opa_simpl marked None) o__p;
      
      (** For all transition of the input SITPN model, there exists a
          corresponding TDI identified through γ in the behavior of the output
          design. *)
      ex_tdi :
      forall t,
      exists id__t g__t i__t o__t,
        getv Teqdec t (t2tdi γ) = Some id__t
        /\ InCs (cs_comp id__t trans_id g__t i__t o__t) (beh d);

      (** For all transition of the input SITPN model and its
          corresponding TDI, the generic map of the TDI holds the following
          associations. *)
      tdi_gen_map :
      forall t id__t g__t i__t o__t,
        getv Teqdec t (t2tdi γ) = Some id__t ->
        InCs (cs_comp id__t trans_id g__t i__t o__t) (beh d) ->
        g__t = [(ga_ transition_type (get_trans_type t));
              (ga_ transition_type (get_max_time_counter t));
              (ga_ Transition.input_arcs_number (if inputs_of_t t then 1 else length (inputs_of_t t)));
              (ga_ Transition.input_arcs_number (if conds_of_t t then 1 else length (conds_of_t t)))
          ];

      (** For all transition of the input SITPN model and its
          corresponding TDI, the input port map of the TDI holds the following
          associations. *)
      tdi_init_ipm :
      forall t id__t g__t i__t o__t,
        getv Teqdec t (t2tdi γ) = Some id__t ->
        InCs (cs_comp id__t trans_id g__t i__t o__t) (beh d) ->
        incl (init_tdi_ipm t) i__t;

      (** For all transition of the input SITPN model with no input
          place, the input port map and output port map of the corresponding TDI
          holds the following associations. *)
      tdi_no_input :
      forall t id__t g__t i__t o__t,
        getv Teqdec t (t2tdi γ) = Some id__t ->
        InCs (cs_comp id__t trans_id g__t i__t o__t) (beh d) ->
        (exists id__s, In (sdecl_ id__s tind_boolean) (sigs d)
                     /\ In (ipa_ (reinit_time $[[0]]) (#id__s)) i__t
                     /\ In (opa_simpl fired (Some ($id__s))) o__t)
        /\ incl [(ipa_ (input_arcs_valid $[[0]]) true);
                 (ipa_ (Transition.priority_authorizations $[[0]]) true)] i__t;

      (** For all transition of the input SITPN model with no
          condition, the input port map of the corresponding TDI holds the
          following association. *)
      tdi_no_cond :
      forall t id__t g__t i__t o__t,
        getv Teqdec t (t2tdi γ) = Some id__t ->
        InCs (cs_comp id__t trans_id g__t i__t o__t) (beh d) ->
        In (ipa_ (input_conditions $[[0]]) true) i__t;

      (** For all post arc of the input SITPN model, the TDI and PDI
          corresponding to the source transition and target place of the arc are
          connected as follows. *)
      post_arc_transl :
      forall t p id__t id__p g__t i__t o__t g__p i__p o__p ω,
        post t p = Some ω ->
        getv Peqdec p (p2pdi γ) = Some id__p ->
        InCs (cs_comp id__p place_id g__p i__p o__p) (beh d) ->
        getv Teqdec t (t2tdi γ) = Some id__t ->
        InCs (cs_comp id__t trans_id g__t i__t o__t) (beh d) ->
        exists i,
          0 <= i <= (length (inputs_of_p p) - 1)
          /\ In (ipa_ (input_arcs_weights $[[i]]) ω) i__p
          /\ exists id__s,
            In (sdecl_ id__s tind_boolean) (sigs d)
            /\ In (opa_simpl fired (Some ($id__s))) o__t
            /\ In (ipa_ (input_transitions_fired $[[i]]) (#id__s)) i__p;

      (** For all pre arc of the input SITPN model, the PDI and TDI
          corresponding to the source place and target transition of the arc are
          connected as follows. *)
      pre_arc_transl :
      forall t p id__t id__p g__t i__t o__t g__p i__p o__p ω a,
        pre p t = Some (a, ω) ->
        getv Peqdec p (p2pdi γ) = Some id__p ->
        InCs (cs_comp id__p place_id g__p i__p o__p) (beh d) ->
        getv Teqdec t (t2tdi γ) = Some id__t ->
        InCs (cs_comp id__t trans_id g__t i__t o__t) (beh d) ->
        exists i,
          0 <= i <= (length (outputs_of_p p) - 1)
          /\ incl [(ipa_ (output_arcs_weights $[[i]]) ω);
                   (ipa_ (output_arcs_types $[[i]]) a)] i__p
          /\ exists j id__av id__rt id__frd id__pah,
            0 <= j <= (length (inputs_of_t t) - 1)
            /\ incl [(sdecl_ id__av tind_boolean);
                     (sdecl_ id__rt tind_boolean);
                     (sdecl_ id__frd tind_boolean);
                     (sdecl_ id__pah tind_boolean)] (sigs d)
            /\ In (opa_idx output_arcs_valid i ($id__av)) o__p
            /\ In (ipa_ (input_arcs_valid $[[j]]) (#id__av)) i__t
            /\ In (opa_idx reinit_transitions_time i ($id__rt)) o__p
            /\ In (ipa_ (reinit_time $[[j]]) (#id__rt)) i__t
            /\ In (ipa_ (output_transitions_fired $[[i]]) (#id__frd)) i__p
            /\ In (opa_simpl fired (Some ($id__frd))) o__t
            /\ In (opa_idx Place.priority_authorizations i ($id__frd)) o__p
            /\ (a = test
                \/ a = inhibitor
                \/ AllConflictsSolvedByMutualExcl (coutputs_of_p p) ->
                In (ipa_ (Transition.priority_authorizations $[[j]]) true) i__t)
            /\ (a = basic \/ ~AllConflictsSolvedByMutualExcl (coutputs_of_p p) ->
                In (ipa_ (Transition.priority_authorizations $[[j]]) true) i__t);

      (** For all place of the input SITPN model for which conflicts
          in its output transitions are not solved by mutual
          exclusion, the port indices of the corresponding PDI reflect
          the priority order established between the conflicting
          output transitions. *)
      pr_transl : 
      forall p t t' id__p g__p i__p o__p id__t g__t i__t o__t id__t' g__t' i__t' o__t',
        pr t t' ->
        getv Peqdec p (p2pdi γ) = Some id__p ->
        InCs (cs_comp id__p place_id g__p i__p o__p) (beh d) ->
        getv Teqdec t (t2tdi γ) = Some id__t ->
        InCs (cs_comp id__t trans_id g__t i__t o__t) (beh d) ->
        getv Teqdec t' (t2tdi γ) = Some id__t' ->
        InCs (cs_comp id__t' trans_id g__t' i__t' o__t') (beh d) ->
        forall (i j : N) id__frd id__frd' id__s id__s' n__t n__t' id__out,
          In (opa_simpl fired (Some ($id__frd))) o__t ->
          In (opa_simpl fired (Some ($id__frd'))) o__t' ->
          incl [(ipa_ (output_transitions_fired $[[i]]) (#id__frd));
                (ipa_ (output_transitions_fired $[[j]]) (#id__frd'))] i__p ->
          In (ipa_ n__t (#id__s)) i__t ->
          In (ipa_ n__t' (#id__s')) i__t' ->
          incl [opa_idx id__out i ($id__s); opa_idx id__out j (id__s')] o__p ->
          i < j;

      (** There exists an actions process that assigns a value to the
          output port representing the activation status of the actions
          (referred to as action ports) of the input SITPN model *)
      actions_process :
      exists ss__ra ss__a,
        InCs (cs_ps actions_ps_id [] (Rst ss__ra Else (Falling ss__a))) (beh d)
             
        (** The length of the [ss__ra] and [ss__a] sequences is equal to
            the number of actions of the input SITPN model. *)
        /\ (seq_length ss__ra = length (actions sitpn)
            /\ seq_length ss__a = length (actions sitpn))

        (** During the initialization, all action ports are assigned to
            false by the actions process. *)
        /\ (forall a id__a,
               getv Aeqdec a (a2out γ) = Some id__a ->
               InSs (($id__a) @<== false) ss__ra)

        (** An action port corresponding to an action associated with
            no place is assigned to false during the falling edge
            phase. *)
        /\ (forall a id__a,
               pls_of_a a = [] ->
               getv Aeqdec a (a2out γ) = Some id__a ->
               InSs (($id__a) @<== false) ss__a)
             
        (** Otherwise, the value of the action port is the result of the
            Boolean sum between the marked output port of all PDIs
            representing the places associated with the corresponding
            action. *)
        /\ (forall a id__a,
               pls_of_a a <> [] ->
               getv Aeqdec a (a2out γ) = Some id__a ->
               exists e__or,
                 InSs (($id__a) @<== e__or) ss__a
                 /\ IsBSumExpr e__or (length (pls_of_a a))
                 /\ (forall p id__p g__p i__p o__p,
                        InA Peq p (pls_of_a a) ->
                        getv Peqdec p (p2pdi γ) = Some id__p ->
                        InCs (cs_comp id__p place_id g__p i__p o__p) (beh d) ->
                        exists id__m,
                          In (sdecl_ id__m tind_boolean) (sigs d)
                          /\ InBOpId id__m e__or
                          /\ In (opa_simpl marked (Some ($id__m))) o__p));
      
      (** There exists a functions process that assigns a value to the
          output port representing the execution status of the
          functions (referred to as function ports) of the input SITPN
          model. *)
      functions_process :
      exists ss__rf ss__f,
        InCs (cs_ps functions_ps_id [] (Rst ss__rf Else (Rising ss__f))) (beh d)
        (** The length of the [ss__rf] and [ss__f] sequences is equal to
            the number of functions of the input SITPN model. *)
        /\ (seq_length ss__rf = length (functions sitpn)
            /\ seq_length ss__f = length (functions sitpn))

        (** During the initialization, all function ports are assigned
            to false by the functions process. *)
        /\ (forall f id__f,
               getv Feqdec f (f2out γ) = Some id__f ->
               InSs (($id__f) @<== false) ss__rf)

        (** A function port corresponding to a function associated
            with no place is assigned to false during the rising edge
            phase. *)
        /\ (forall f id__f,
               trs_of_f f = [] ->
               getv Feqdec f (f2out γ) = Some id__f ->
               InSs (($id__f) @<== false) ss__f)
             
        (** Otherwise, the value of the function port is the result of
            the Boolean sum between the [fired] output port of all
            TDIs representing the transitions associated with the
            corresponding function. *)
        /\ (forall f id__f,
               trs_of_f f <> [] ->
               getv Feqdec f (f2out γ) = Some id__f ->
               exists e__or,
                 InSs (($id__f) @<== e__or) ss__f
                 /\ IsBSumExpr e__or (length (trs_of_f f))
                 /\ (forall t id__t g__t i__t o__t,
                        InA Teq t (trs_of_f f) ->
                        getv Teqdec t (t2tdi γ) = Some id__t ->
                        InCs (cs_comp id__t trans_id g__t i__t o__t) (beh d) ->
                        exists id__m,
                          In (sdecl_ id__m tind_boolean) (sigs d)
                          /\ InBOpId id__m e__or
                          /\ In (opa_simpl fired (Some ($id__m))) o__t));
      
      (** For all association between a transition and a condition,
          the input port reflecting the Boolean value of the given condition
          (referred to as a condition port) is connected as follows to the input
          port map of the TDI corresponding to the associated transition *)
      cond_connect :
      forall t id__t g__t i__t o__t c id__c,
        getv Teqdec t (t2tdi γ) = Some id__t ->
        getv Ceqdec c (c2in γ) = Some id__c ->
        InCs (cs_comp id__t trans_id g__t i__t o__t) (beh d) ->
        (has_C t c = one ->
         exists i,
           0 <= i <= length (conds_of_t t) - 1
           /\ In (ipa_ (input_conditions $[[i]]) (#id__c)) i__t)
        /\ (has_C t c = mone ->
            exists i,
              0 <= i <= length (conds_of_t t) - 1
              /\ In (ipa_ (input_conditions $[[i]]) (e_uop uo_not (#id__c))) i__t);
      
    }.

(** Defines the complete specification of the HM2T with error
    cases. *)

Inductive HM2T_spec (sitpn : Sitpn) (b : P sitpn -> nat) :
  option (design * Sitpn2HVhdlBinder sitpn) -> Prop :=

| HM2T_success :
  forall d γ, HM2T_ sitpn b d γ -> HM2T_spec sitpn b (Some (d, γ))
                                             
| HM2T_error :
  ~IsWellDefined sitpn -> HM2T_spec sitpn b None.




