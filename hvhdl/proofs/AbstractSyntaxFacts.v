(** * Facts about H-VHDL Abstract Syntax *)

Require Import common.CoqLib.
Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.WellDefinedDesign.

(** ** Facts about [InCs] *)

Section InCsFacts.

  Lemma InCs_NoDup_comp_eq :
    forall {cstmt id__c id__e0 g0 i0 o0 id__e1 g1 i1 o1},
      InCs (cs_comp id__c id__e0 g0 i0 o0) cstmt ->
      InCs (cs_comp id__c id__e1 g1 i1 o1) cstmt ->
      NoDup (get_cids cstmt) ->
      cs_comp id__c id__e0 g0 i0 o0 = cs_comp id__c id__e1 g1 i1 o1.
  Proof.    
    induction cstmt; try (solve [inversion 1]).
    destruct 1; destruct 1; reflexivity.
  Admitted.

End InCsFacts.

Lemma flatten_cs_ex : forall beh, exists lofcs, FlattenCs beh lofcs.
Proof.
  induction beh.

  (* CASE simple Process *)
  - exists [cs_ps id__p sl vars stmt]; auto.

  (* CASE simple Component Instance *)
  - exists [cs_comp id__c id__e g i o]; auto.
    
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

(** FlattenCs is a deterministic relation *)

Lemma flatten_cs_determ :
  forall {behavior lofcs },
    FlattenCs behavior lofcs ->
    forall {lofcs'},
    FlattenCs behavior lofcs' ->
    lofcs = lofcs'.
Proof.
  induction 1; only 1 - 6: inversion_clear 1; auto.
  - inversion H1; auto.
  - rewrite (IHFlattenCs l0 H1); reflexivity.
  - inversion_clear H1; rewrite (IHFlattenCs l' H2); reflexivity.
  - rewrite (IHFlattenCs l0 H1); reflexivity.
  - inversion_clear H1; rewrite (IHFlattenCs l' H2); reflexivity.
  - inversion_clear 1 in H H0; auto.
    + inversion H; apply IHFlattenCs2; auto.
    + inversion H; rewrite (IHFlattenCs2 l0 H2); reflexivity.
    + inversion H; rewrite (IHFlattenCs2 l0 H2); reflexivity.
    + rewrite (IHFlattenCs1 l0 H2); rewrite (IHFlattenCs2 l'0 H3); reflexivity.
Defined.

Lemma FoldLCs_ex :
  forall {A : Type} (f : A -> cs -> A) cstmt a, exists res, FoldLCs f cstmt a res.
Proof.
  induction cstmt; intros; try
  (match goal with
   | |- exists _, FoldLCs ?f ?cstmt ?a _ =>
     exists (f a cstmt); constructor
   end).
  destruct (IHcstmt1 a) as (res, FoldLCs1).
  destruct (IHcstmt2 res) as (res', FoldLCs2).
  eexists; econstructor.
  eexact (FoldLCs1). eexact FoldLCs2.
Qed.

Lemma FoldLCs_determ :
  forall {A : Type} {f : A -> cs -> A} {cstmt a res res'},
    FoldLCs f cstmt a res ->
    FoldLCs f cstmt a res' ->
    res = res'.
Proof.
  induction cstmt; try (inversion_clear 1; inversion_clear 1; auto).
  assert (e : a' = a'0) by (eapply IHcstmt1; eauto).
  rewrite e in *; eapply IHcstmt2; eauto.
Qed.


