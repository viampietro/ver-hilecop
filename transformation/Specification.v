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

Record HM2T_ (sitpn : Sitpn) (b : P sitpn -> nat) (d : design) (γ : Sitpn2HVhdlMap sitpn) : Prop :=
  MkHM2T_ {

      (** Design [d] has an empty set of generic constants. *)
      emp_gens : (gens d) = [];

      (** There is the same number of conditions in [sitpn] than of
          input ports in [d]. *)
      eq_conds_inports :
      forall (inports : list { id | exists τ, In (pdecl_in id τ) (ports d) }),
        Sig_in_List inports ->
        length inports = length (conditions sitpn);

      (** There is the same number of actions and functions in [sitpn]
          than of output ports in [d]. *)
      eq_acts_funs_outports :
      forall (outports : list { id | exists τ, In (pdecl_out id τ) (ports d) }),
        Sig_in_List outports ->
        length outports = length (actions sitpn) + length (functions sitpn);

      (** Design d is elaborable in the context of the HILECOP design
          store and given an empty dimensioning function. *)
      d_is_elaborable :
      exists Δ σ__e, EDesign hdstore (NatMap.empty value) d Δ σ__e
  }.
