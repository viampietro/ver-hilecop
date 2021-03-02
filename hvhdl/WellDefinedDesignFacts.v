(** * Facts about Well-defined H-VHDL Designs *)

Require Import common.Coqlib.
Require Import common.InAndNoDup.
Require Import common.ListPlusFacts.
Require Import common.ListPlusTactics.

Require Import hvhdl.WellDefinedDesign.
Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.AbstractSyntaxFacts.

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
    AreCsCompIds (cs_par cstmt cstmt') compids'' ->
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
      [try subst; exists entid, gmap, ipmap, opmap; reflexivity | contradiction ].
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

Lemma comp_in_compids :
  forall {lofcs compids id__c id__e gm ipm opm},
    AreCompIds lofcs compids ->
    List.In (cs_comp id__c id__e gm ipm opm) lofcs ->
    List.In id__c compids.
Proof.
  induction 1.
  - contradiction.
  - inversion_clear 1.
    + lazymatch goal with
      | [ Heq: _ = _, Hfoldl: ListPlus.FoldL _ _ _ _ |- _ ] =>
        rewrite Heq in Hfoldl; simpl in Hfoldl; eapply FoldL_in_acc; eauto
      end.
      intros *; intros Hin;
        lazymatch goal with
        | |- List.In _ ((fun _ => _) _ ?b) =>
          case b; intros; (assumption || apply (in_appl Hin))
        end.
    + apply IHFoldL; auto.
Defined.

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

(** ** Facts about [HasUniqueIds] Relation *)

Ltac inv_hasuniqids H :=
  lazymatch type of H with
  | HasUniqueIds _ =>
    let genids := fresh "genids" in
    let portids := fresh "portids" in
    let sigids := fresh "sigids" in
    let lofcs := fresh "lofcs" in
    let compids := fresh "compids" in
    let pids := fresh "pids" in
    let Hdeclids := fresh "Hdeclids" in
    let Hbehids := fresh "Hbehids" in
    let Hnodupids := fresh "Hnodupids" in
    let Hnodupvars := fresh "Hnodupvars" in
    inversion_clear H as (genids,
                          (portids,
                           (sigids,
                            (lofcs,
                             (compids,
                              (pids,
                               (Hdeclids, (Hbehids, (Hnodupids, Hnodupvars)))))))))
  | _ => fail "Type of" H "is not HasUniqueIds ?d"
  end.
