(** * Tactics for H-VHDL Design Well-definition *)

Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.WellDefinedDesign.
Require Import hvhdl.WellDefinedDesignFacts.

Ltac build_compids lofcs :=
  lazymatch type of lofcs with
  | list cs => 
    let compids := fresh "compids" in
    let HAreCompIds := fresh "HAreCompIds" in
    destruct (AreCompIds_ex lofcs) as (compids, HAreCompIds)
  | _ => fail "Term" lofcs "is not of type (list cs)"
  end.

Ltac build_pids lofcs :=
  lazymatch type of lofcs with
  | list cs => 
    let pids := fresh "pids" in
    let HArePIds := fresh "HArePIds" in
    destruct (ArePIds_ex lofcs) as (pids, HArePIds)
  | _ => fail "Term" lofcs "is not of type (list cs)"
  end.

