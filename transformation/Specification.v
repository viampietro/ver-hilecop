(** * Specification of the HILECOP model-to-text transformation (HM2T) *)

Require Import common.CoqLib.
Require Import common.GlobalTypes.
Require Import common.GlobalFacts.
Require Import common.ListPlus.

Require Import sitpn.Sitpn.

Require Import transformation.Sitpn2HVhdlTypes.

Require Import hvhdl.HVhdlCoreLib.
Require Import hvhdl.HVhdlElaborationLib.
Require Import hvhdl.HVhdlHilecopLib.


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
      forall (inports : list { id | exists τ, In (pdecl_in id τ) (ports d) }),
        Listing P1SigEq inports ->
        length inports = length (conditions sitpn);

      (** There is the same number of actions and functions in [sitpn]
          than of output ports in [d]. *)
      eq_acts_funs_outports :
      forall (outports : list { id | exists τ, In (pdecl_out id τ) (ports d) }),
        Listing P1SigEq outports ->
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
        
      IsBijectiveP P1SigEq eq is_pdi_id (p2pci γ)
      /\ IsBijectiveP P1SigEq eq is_tdi_id (t2tci γ)
      /\ IsBijectiveP AFEq eq is_op_id (merge_dom (a2out γ) (f2out γ))
      /\ IsBijectiveP P1SigEq eq is_ip_id (c2in γ);

  }.
