(** * Tactics for H-VHDL Design Well-definition *)

Require Import common.ListLib.

Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.WellDefinedDesign.
Require Import hvhdl.WellDefinedDesignFacts.
Import HVhdlCsNotations.

Ltac solve_nodup_compids_l :=
  match goal with
  | [ H1: AreCsCompIds ?cs1 ?compids1,
          H2: AreCsCompIds ?cs2 ?compids2,
              H3: AreCsCompIds (?cs1 // ?cs2) ?compids,
                  H4: List.NoDup ?compids
      |- List.NoDup ?compids1 ] =>
    eapply @proj1; eapply nodup_app;
    erewrite AreCsCompIds_determ; eauto;
    eapply AreCsCompIds_app; eauto
  end.

Ltac solve_nodup_compids_r :=
  match goal with
  | [ H1: AreCsCompIds ?cstmt1 ?compids1,
          H2: AreCsCompIds ?cstmt2 ?compids2,
              H3: AreCsCompIds (?cstmt1 // ?cstmt2) ?compids,
                  H4: List.NoDup ?compids
      |- List.NoDup ?compids2 ] =>
    eapply @proj2; eapply nodup_app;
    erewrite AreCsCompIds_determ; eauto;
    eapply AreCsCompIds_app; eauto
  end.

Ltac solve_nodup_compids_app :=
  match goal with
  | [ H1: AreCsCompIds ?cstmt1 ?compids1,
          H2: AreCsCompIds ?cstmt2 ?compids2,
              H3: AreCsCompIds (?cstmt1 // ?cstmt2) ?compids,
                  H4: List.NoDup ?compids
      |- List.NoDup (?compids1 ++ ?compids2) ] =>
    erewrite AreCsCompIds_determ; eauto; apply AreCsCompIds_app; auto
  end.

(** ** Tactics about [DesignHasUniqueIds] Relation *)

Ltac inv_dhasuniqids H :=
  lazymatch type of H with
  | DesignHasUniqueIds _ _ _ _ _ _ =>
    let Hdeclids := fresh "Hdeclids" in
    let Hbehids := fresh "Hbehids" in
    let Hnodupids := fresh "Hnodupids" in
    let Hnodupvars := fresh "Hnodupvars" in
    inversion_clear H as (Hdeclids, (Hbehids, (Hnodupids, Hnodupvars)))
  | _ => fail "Type of" H "is not DesignHasUniqueIds ?d"
  end.
