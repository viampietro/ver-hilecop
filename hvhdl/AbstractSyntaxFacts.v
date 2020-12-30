(** * Facts about H-VHDL Abstract Syntax *)

Require Import common.Coqlib.
Require Import hvhdl.AbstractSyntax.

Lemma flatten_cs_ex : forall beh, exists lofcs, FlattenCs beh lofcs.
Proof.
  induction beh.

  (* CASE simple Process *)
  - exists [cs_ps pid sl vars stmt]; auto.

  (* CASE simple Component Instance *)
  - exists [cs_comp compid entid gmap ipmap opmap]; auto.
    
  (* CASE parallel stmts *)
  - lazymatch goal with
    | [ IH1: exists _, _, IH2: exists _, _ |- _ ] =>
      inversion_clear IH1 as (lofcs1, Hflat1);
        inversion_clear IH2 as (lofcs2, Hflat2);
        exists (lofcs1 ++ lofcs2);
        auto
    end.

  (* CASE null *)
  - exists nil; auto.
Qed.
