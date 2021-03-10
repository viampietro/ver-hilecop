(** * Facts about Sitpn Information Generation Functions *)

Require Import common.CoqLib.
Require Import common.GlobalFacts.
Require Import common.StateAndErrorMonad.
Require Import common.StateAndErrorMonadTactics.
Require Import common.ListDep.
Require Import common.ListMonad.
Require Import common.ListMonadFacts.
Require Import common.ListMonadTactics.
Require Import common.ListPlus.

Require Import sitpn.dp.Sitpn.
Require Import sitpn.dp.SitpnFacts.

Require Import sitpn2hvhdl.Sitpn2HVhdl.
Require Import sitpn2hvhdl.GenerateInfosInvs.

(** ** Facts about Transition Information Generation *)

Section TInfos.
  
End TInfos.

(** ** Facts about Place Information Generation *)

Section PInfos.
  
End PInfos.

(** ** Facts about Generation of Interpretation Information *)

Section InterprInfos.

End InterprInfos.

(** ** Facts about Checking of Sitpn Well-definition *)

Section CheckWDSitpn.

  
End CheckWDSitpn.

(** ** Facts about Dependently-typed Lists Generation *)

Lemma tmap_aux_sil :
  forall {A state : Type} {Q : A -> Prop}
         {lofAs : list A}
         {lofSigs1 : list { a | Q a}}
         {InlofAs2Sigs : forall a : A, List.In a lofAs -> {x | Q x}}
         {s : state} {lofSigs2 s'},
    tmap_aux (fun p s => Ret p s) lofAs lofSigs1 InlofAs2Sigs s = OK lofSigs2 s' ->
    (forall x, List.In (proj1_sig x) lofAs \/ InA seq x lofSigs1) ->
    (forall a (InlofAs : List.In a lofAs), a = proj1_sig (InlofAs2Sigs a InlofAs)) ->
    (forall a (InlofAs : List.In a lofAs), ~InA seq (InlofAs2Sigs a InlofAs) lofSigs1) ->
    List.NoDup lofAs ->
    NoDupA seq lofSigs1 ->
    Sig_in_List lofSigs2.
Proof.
  induction lofAs; intros *; intros e; minv e.

  - split; [ firstorder | auto ].
  - intros or_InlofAs_InlofSigs eq_proj1 nInA_lofSigs NoDup_lofAs NoDupA_lofSigs;
      eapply IHlofAs; eauto with setoidl.
    (* CASE [In (proj1_sig x) lofAs] or [InA x (lofSigs1 ++ (InlofAs2Sigs a))] *)
    + intros x; specialize (or_InlofAs_InlofSigs x);
        inversion_clear or_InlofAs_InlofSigs as [In_lofAs | InA_lofSigs].
      (* SUBCASE [a = proj1_sig x \/ In (proj1_sig x) lofAs] *)
      -- inversion_clear In_lofAs as [eq_a_proj1 | In_proj1_lofAs].
         ++ right; erewrite (InA_app_iff seq lofSigs1); right.
            eapply InA_cons_hd; specialize (eq_proj1 a (in_eq a lofAs)).
            transitivity a; auto.
         ++ auto.
      -- right; erewrite (InA_app_iff seq lofSigs1); left; auto.
    (* CASE [x ∈ lofAs ⇒ x ∉ (lofSigs ++ (InlofAs2Sigs a))] *)
    + intros *; erewrite InA_app_iff.
      inversion_clear 1 as [InA_lofSigs | InA_singl].
      -- unfold in_T_in_sublist_T in InA_lofSigs.
         eapply nInA_lofSigs; eauto.
      -- inversion_clear InA_singl as [e1 e2 seq_ | e1 e2 InAnil]; [ | inversion InAnil].
         unfold in_T_in_sublist_T in seq_.
         assert (e : a = a0) by (transitivity (proj1_sig (InlofAs2Sigs a (in_eq a lofAs)));
                                 [ eapply eq_proj1 | rewrite <- seq_; symmetry; eapply eq_proj1 ]).
         clear seq_; rewrite <- e in InlofAs; inversion NoDup_lofAs; contradiction.
    (* NoDup lofAs *)
    + inversion NoDup_lofAs; assumption.
    (* NoDupA (lofSigs1 ++ [InlofAs2Sigs a]) *)
    + eapply NoDupA_app; eauto.
      apply NoDupA_singleton.
      intros x InA_lofSigs; inversion_clear 1 as [e1 e2 seq_ | e1 e2 InAnil]; [ | inversion InAnil].
      apply (nInA_lofSigs a (in_eq a lofAs)).
      eapply InA_eqA; eauto with typeclass_instances.
Qed.

(** ** Facts about Sitpn Information Generation Function *)

Lemma gen_sitpn_infos_sil_lofPs :
  forall {sitpn decpr s v s'},
    generate_sitpn_infos sitpn decpr s = OK v s' ->
    List.NoDup (places sitpn) ->
    Sig_in_List (lofPs s').
Proof.
  intros until s'; intros e; monadInv e; intros.
  rewrite <- (gen_finfos_inv_lofPs EQ15); clear EQ15.
  rewrite <- (gen_ainfos_inv_lofPs EQ13); clear EQ13.
  rewrite <- (gen_cinfos_inv_lofPs EQ12); clear EQ12.
  rewrite <- (gen_pinfos_inv_lofPs EQ11); clear EQ11.
  rewrite <- (gen_tinfos_inv_lofPs EQ10); clear EQ10.
  rewrite <- (check_wd_sitpn_inv_eq_state EQ9); clear EQ9.
  do 5 (match goal with
        | [ H: ?F _ _ = OK _ ?st1 |- Sig_in_List (lofPs ?st1) ] =>
          minv H; simpl; auto; clear H
        end).
  eapply tmap_aux_sil; eauto;
    [intros p; left; exact (proj2_sig p) | inversion 1].
Qed.

Lemma gen_sitpn_infos_sil_lofTs :
  forall {sitpn decpr s v s'},
    generate_sitpn_infos sitpn decpr s = OK v s' ->
    List.NoDup (transitions sitpn) ->
    Sig_in_List (lofTs s').
Proof.
  intros *; intros e; monadInv e; intros.
  rewrite <- (gen_finfos_inv_lofTs EQ15); clear EQ15.
  rewrite <- (gen_ainfos_inv_lofTs EQ13); clear EQ13.
  rewrite <- (gen_cinfos_inv_lofTs EQ12); clear EQ12.
  rewrite <- (gen_pinfos_inv_lofTs EQ11); clear EQ11.
  rewrite <- (gen_tinfos_inv_lofTs EQ10); clear EQ10.
  rewrite <- (check_wd_sitpn_inv_eq_state EQ9); clear EQ9.
  do 4 (match goal with
        | [ H: ?F _ _ = OK _ ?st1 |- Sig_in_List (lofTs ?st1) ] =>
          minv H; simpl; auto; clear H
        end).
  eapply tmap_aux_sil; eauto;
    [intros t; left; exact (proj2_sig t) | inversion 1].
Qed.
