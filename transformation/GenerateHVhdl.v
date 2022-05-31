(** * Generation of a H-VHDL top-level design from an SITPN model *)

Require Import common.CoqLib.
Require Import common.GlobalTypes.
Require Import common.ListPlus.
Require Import common.ListDep.
Require Import common.StateAndErrorMonad.
Require Import common.ListMonad.
Require Import String.

Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.Petri.
Require Import hvhdl.HVhdlTypes.

Require Import sitpn.Sitpn.

Require Import transformation.Sitpn2HVhdlTypes.
Require Import transformation.GenerateInfos.
Require Import transformation.GenerateArchitecture.
Require Import transformation.GenerateInterconnections.
Require Import transformation.GeneratePorts.

Open Scope abss_scope.

(** ** Transformation from an SITPN to an H-VHDL design *)

Section Sitpn2HVhdl.

  Variable sitpn : Sitpn.

  (* Macro for the state-and-error monad instantiated with the
     compile-time state.  *)

  Definition CompileTimeState := @Mon (Sitpn2HVhdlState sitpn).
  
  (** ** Generation of an H-VHDL design *)
        
  (** Defines the transformation function that generates an H-VHDL design
      from an SITPN. *)

  Definition generate_design_and_binder : CompileTimeState (design * Sitpn2HVhdlMap sitpn):=
    do s <- Get; Ret ((design_ [] (ports s) (sigs s) (beh s)), (γ s)).
    
  Definition sitpn2hvhdl (b : P sitpn -> nat) :
    (design * Sitpn2HVhdlMap sitpn) + string :=
    RedV 
      ((do _ <- generate_sitpn_infos sitpn;
        do _ <- generate_architecture b;
        do _ <- generate_interconnections;
        do _ <- generate_ports;
        generate_design_and_binder) (InitS2HState sitpn Petri.ffid)).
  
End Sitpn2HVhdl.

Require Import FunInd.

Functional Scheme sitpn2hvhdl_ind := Induction for sitpn2hvhdl Sort Prop.






