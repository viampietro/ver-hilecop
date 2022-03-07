(** * Facts about Well-defined H-VHDL Designs *)

Require Import common.CoqLib.
Require Import common.proofs.CoqTactics.
Require Import common.InAndNoDup.
Require Import common.proofs.ListPlusFacts.
Require Import common.proofs.ListPlusTactics.

Require Import hvhdl.WellDefinedDesign.
Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.proofs.AbstractSyntaxFacts.

Open Scope abss_scope.
Import HVhdlCsNotations.

(** ** Facts about [AreCsCompIds]  *)

Lemma AreCsCompIds_determ :
  forall cstmt compids compids',
    AreCsCompIds cstmt compids ->
    AreCsCompIds cstmt compids' ->
    compids = compids'.
Proof. intros *; eapply FoldLCs_determ. Qed.

Lemma AreCsCompIds_ex : forall cstmt, exists compids, AreCsCompIds cstmt compids.
Proof. intros; eapply FoldLCs_ex. Qed.

Lemma AreCsCompIds_app1 :
  forall cstmt compids',
    let comp2id :=
        fun (cids : list HVhdlTypes.ident) (cstmt0 : cs) =>
          match cstmt0 with
          | cs_comp id _ _ _ _ => cids ++ [id]
          | _ => cids
          end in
    AreCsCompIds cstmt compids' ->
    forall compids, FoldLCs comp2id cstmt compids (compids ++ compids').
Proof.
  induction cstmt; intros; inversion H;
    try ((rewrite app_nil_r; constructor) || (rewrite app_nil_l; constructor)).
  destruct (AreCsCompIds_ex cstmt2) as (compids2, AreCsCompIds2).
  constructor 4 with (a' := compids ++ a').
  eapply IHcstmt1; eauto.
  erewrite @FoldLCs_determ with (res := compids') (res' := a' ++ compids2); eauto.
  rewrite app_assoc; apply IHcstmt2 with (compids := compids ++ a'); auto.
Qed. 

Lemma AreCsCompIds_app :
  forall cstmt cstmt' compids compids',
    AreCsCompIds cstmt compids ->
    AreCsCompIds cstmt' compids' ->
    AreCsCompIds (cs_par cstmt cstmt') (compids ++ compids').
Proof.
  intros; econstructor. eexact H.
  apply AreCsCompIds_app1; auto.
Qed.

Lemma AreCsCompIds_eq_app :
  forall cstmt cstmt' compids compids' compids'',
    AreCsCompIds cstmt compids ->
    AreCsCompIds cstmt' compids' ->
    AreCsCompIds (cstmt // cstmt') compids'' ->
    compids'' = compids ++ compids'.
Proof.
  intros; eapply AreCsCompIds_determ; eauto.
  eapply AreCsCompIds_app; eauto.
Qed.

Lemma AreCsCompIds_compid_iff :
  forall {behavior compids},
    AreCsCompIds behavior compids ->
    (forall id__c, List.In id__c compids -> exists id__e gm ipm opm, InCs (cs_comp id__c id__e gm ipm opm) behavior)
    /\ (forall id__c id__e gm ipm opm, InCs (cs_comp id__c id__e gm ipm opm) behavior -> List.In id__c compids).
Proof.
  induction behavior; inversion 1; (try inversion_clear 1); split;
    tryif (solve [inversion_clear 1]) then (inversion_clear 1) else auto.

  (* CASE behavior = comp(...) *)
  - rewrite app_nil_l; inversion_clear 1;
      [ try subst; exists id__e, g, i, o; reflexivity | contradiction ].
  - rewrite app_nil_l; inversion_clear 1; constructor; reflexivity.

  (* CASE behavior = beh1 || beh2 *)
  - rename a' into compids1.
    destruct (AreCsCompIds_ex behavior2) as (compids2, AreCsCompIds2).
    erewrite AreCsCompIds_eq_app with (compids'' := compids) (compids := compids1); eauto.
    intros id__c In_app; destruct_in_app_or.
    + edestruct IHbehavior1 with (compids := compids1) as ((id__e, (gm, (ipm, (opm, InCs_beh1)))), _); eauto.
      do 4 eexists; simpl; left; eexact InCs_beh1.
    + edestruct IHbehavior2 with (compids := compids2) as ((id__e, (gm, (ipm, (opm, InCs_beh2)))), _); eauto.
      do 4 eexists; simpl; right; eexact InCs_beh2.
  - rename a' into compids1.
    destruct (AreCsCompIds_ex behavior2) as (compids2, AreCsCompIds2).
    erewrite AreCsCompIds_eq_app with (compids'' := compids) (compids := compids1); eauto.
    simpl; inversion_clear 1.
    + eapply in_or_app; left; eapply IHbehavior1 with (compids := compids1); eauto.
    + eapply in_or_app; right; eapply IHbehavior2 with (compids := compids2); eauto.
Qed.

Lemma AreCsCompIds_ex_app :
  forall {cstmt1 cstmt2 compids},
    AreCsCompIds (cstmt1 // cstmt2) compids ->
    exists compids1 compids2,
      AreCsCompIds cstmt1 compids1 /\
      AreCsCompIds cstmt2 compids2 /\ 
      compids = compids1 ++ compids2.
Proof.
  do 3 intro.
  destruct (AreCsCompIds_ex cstmt1) as (compids1, AreCsCompIds1).
  destruct (AreCsCompIds_ex cstmt2) as (compids2, AreCsCompIds2).
  exists compids1, compids2.
  split_and; try (solve [assumption]).
  eapply AreCsCompIds_eq_app; eauto.
Qed.

(** ** Facts about [ArePortIds] Relation *)

Lemma ports_in_portids :
  forall {id τ ports portids},
    (List.In (pdecl_in id τ) ports \/ List.In (pdecl_out id τ) ports) ->
    ArePortIds ports portids ->
    List.In id portids.
Proof.
  inversion 1; intros;
    lazymatch goal with
    | [ H: List.In ?p _ |- _ ] =>
      change id with ((fun pd : pdecl =>
                         match pd with
                         | pdecl_in id _ | pdecl_out id _ => id
                         end) p);
        eapply Map_in; eauto
    end.
Qed.

(** ** Facts about [AreSigIds] Relation *)

Lemma sigs_in_sigids :
  forall {id τ sigs sigids},
    List.In (sdecl_ id τ) sigs ->
    AreSigIds sigs sigids ->
    List.In id sigids.
Proof.
  intros;
    lazymatch goal with
    | [ H: List.In ?s _ |- _ ] =>
      change id with ((fun sd : sdecl =>
                         match sd with
                         | sdecl_ id _ => id
                         end) s);
        eapply Map_in; eauto
    end.
Qed.

