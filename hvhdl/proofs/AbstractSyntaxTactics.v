(** * Tactics for the H-VHDL Abstract Syntax *)

Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.AbstractSyntaxFacts.

Ltac build_lofcs beh :=
  lazymatch type of beh with
  | cs => 
    specialize (flatten_cs_ex beh);
    intros Hflatcs_ex;
    let lofcs := fresh "lofcs" in
    let Hflatcs := fresh "Hflatcs" in
    inversion_clear Hflatcs_ex as (lofcs, Hflatcs)
  | _ => fail "Term" beh "is not of type cs"
  end.
