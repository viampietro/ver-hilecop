(** * Facts about H-VHDL Semantical Domains *)

Require Import common.CoqLib.
Require Import common.ListPlus.
Require Import hvhdl.SemanticalDomains.

Lemma BProd_aofv_false : 
  forall aofv n m,
    (exists i, n <= i < m /\ get_bool_at aofv i = false) ->
    BProd (get_bool_at aofv) (seq n m) false.
Admitted.

