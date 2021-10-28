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

Require Import sitpn2hvhdl.Sitpn2HVhdlTypes.
Require Import sitpn2hvhdl.GenerateInfos.
Require Import sitpn2hvhdl.GenerateArchitecture.
Require Import sitpn2hvhdl.GenerateInterconnections.
Require Import sitpn2hvhdl.GeneratePorts.

Open Scope abss_scope.

(** ** Transformation from an SITPN to an H-VHDL design *)

Section Sitpn2HVhdl.

  Variable sitpn : Sitpn.

  (* Proof of decidability for the priority relation of [sitpn].
     Necessary to the [generate_sitpn_infos] function.
   *)
  Variable decpr : forall x y : T sitpn, {x >~ y} + {~x >~ y}.
  
  (* Alias for the state-and-error monad instantiated with the
     compile-time state.  *)

  Definition CompileTimeState := @Mon (Sitpn2HVhdlState sitpn).
  
  (** ** Generation of an H-VHDL design *)
        
  (** Defines the transformation function that generates an H-VHDL design
      from an SITPN. *)

  Definition generate_design_and_binder (id__e id__a : ident) : CompileTimeState (design * Sitpn2HVhdlMap sitpn):=
    do s <- Get; Ret ((design_ id__e id__a [] (ports s) (sigs s) (beh s)), (γ s)).
    
  Definition sitpn_to_hvhdl (id__e id__a : ident) (b : P sitpn -> nat) :
    (design * Sitpn2HVhdlMap sitpn) + string :=
    RedV 
      ((do _ <- generate_sitpn_infos sitpn decpr;
        do _ <- generate_architecture b;
        do _ <- generate_interconnections;
        do _ <- generate_ports;
        generate_design_and_binder id__e id__a) (InitS2HState sitpn Petri.ffid)).
  
End Sitpn2HVhdl.

Require Import FunInd.

Functional Scheme sitpn_to_hvhdl_ind := Induction for sitpn_to_hvhdl Sort Prop.




