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

Lemma ArePIds_ex : forall lofcs, exists pids, ArePIds lofcs pids.
Admitted.

Lemma ps_in_pids :
  forall {lofcs pids id__p sl vars body},
    ArePIds lofcs pids ->
    List.In (cs_ps id__p sl vars body) lofcs ->
    List.In id__p pids.
Proof.
  induction 1.
  - contradiction.
  - inversion_clear 1.
    + lazymatch goal with
      | [ Heq: _ = _, Hfoldl: ListPlus.FoldL _ _ _ _ |- _ ] =>
        rewrite Heq in Hfoldl; simpl in Hfoldl; eapply FoldL_in_acc; eauto
      end.
      -- apply in_last.
      -- intros *; intros Hin;
           lazymatch goal with
           | |- List.In _ ((fun _ => _) _ ?b) =>
             case b; intros; (assumption || apply (in_appl Hin))
           end.
    + apply IHFoldL; auto.
Defined.


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
      -- apply in_last.
      -- intros *; intros Hin;
           lazymatch goal with
           | |- List.In _ ((fun _ => _) _ ?b) =>
             case b; intros; (assumption || apply (in_appl Hin))
           end.
    + apply IHFoldL; auto.
Defined.

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

Lemma is_unique_port_id_ps : 
  forall d lofcs id τ,
    HasUniqueIds d ->
    FlattenCs (behavior d) lofcs ->
    (List.In (pdecl_in id τ) (ports d) \/ List.In (pdecl_out id τ) (ports d)) ->
    ~ (exists sl vars body, List.In (cs_ps id sl vars body) lofcs).
Proof.
  intros *; intros Huniqids Hflat Hin_ports Hex.
  inversion_clear Hex as (sl, (vars, (body, Hin_ps))).
  inv_hasuniqids Huniqids.

  (* [id ∈ portids] *)
  specialize (ports_in_portids Hin_ports (proj1 (proj2 Hdeclids))) as Hin_portids.

  (* [id ∈ pids] *)
  rewrite <- (flatten_cs_determ Hflat (proj1 Hbehids)) in Hbehids.
  specialize (ps_in_pids (proj2 (proj2 Hbehids)) Hin_ps) as Hin_pids.

  (* Gets [id ∉ pids], then contradiction. *)
  red_nodup Hnodupids.
  rewrite (app_assoc genids portids (sigids ++ compids ++ pids)) in H1.
  specialize (nodup_app_not_in (genids ++ portids) (sigids ++ compids ++ pids) H1 id (in_appr Hin_portids)) as Hnot_in_pids.
  do 2 (apply not_app_in, proj2 in Hnot_in_pids).
  contradiction.
Qed.

Lemma is_unique_port_id_comps : 
  forall d lofcs id τ,
    HasUniqueIds d ->
    FlattenCs (behavior d) lofcs ->
    (List.In (pdecl_in id τ) (ports d) \/ List.In (pdecl_out id τ) (ports d)) ->
    ~ (exists id__e gmap ipmap opmap, List.In (cs_comp id id__e gmap ipmap opmap) lofcs).
Proof.
  intros *; intros Huniqids Hflat Hin_ports Hex.
  inversion_clear Hex as (id__e, (gm, (ipm, (opm, Hin_comps)))).
  inv_hasuniqids Huniqids.

  (* [id ∈ portids] *)
  specialize (ports_in_portids Hin_ports (proj1 (proj2 Hdeclids))) as Hin_portids.

  (* [id ∈ compids] *)
  rewrite <- (flatten_cs_determ Hflat (proj1 Hbehids)) in Hbehids.
  specialize (comp_in_compids (proj1 (proj2 Hbehids)) Hin_comps) as Hin_compids.

  (* Gets [id ∉ pids], then contradiction. *)
  red_nodup Hnodupids.
  rewrite (app_assoc genids portids (sigids ++ compids ++ pids)) in H1.
  specialize (nodup_app_not_in (genids ++ portids) (sigids ++ compids ++ pids) H1 id (in_appr Hin_portids)) as Hnot_in_compids.
  apply not_app_in, proj2, not_app_in, proj1 in Hnot_in_compids.
  contradiction.  
Qed.

Lemma is_unique_port_id_sigs : 
  forall d id τ,
    HasUniqueIds d ->
    (List.In (pdecl_in id τ) (ports d) \/ List.In (pdecl_out id τ) (ports d)) ->
    ~ (exists τ, List.In (sdecl_ id τ) (AbstractSyntax.sigs d)).
Proof.
  intros *; intros Huniqids Hin_ports Hex.
  inversion_clear Hex as (τ', Hin_sigs).
  inv_hasuniqids Huniqids.

  (* [id ∈ portids] *)
  specialize (ports_in_portids Hin_ports (proj1 (proj2 Hdeclids))) as Hin_portids.

  (* [id ∈ sigids] *)
  specialize (sigs_in_sigids Hin_sigs (proj2 (proj2 Hdeclids))) as Hin_sigids.

  (* Gets [id ∉ pids], then contradiction. *)
  red_nodup Hnodupids.
  lazymatch goal with
  | [ Hnodup: NoDup _ |- _ ] =>
    rewrite (app_assoc genids portids (sigids ++ compids ++ pids)) in Hnodup;
      specialize (nodup_app_not_in (genids ++ portids) (sigids ++ compids ++ pids) Hnodup id (in_appr Hin_portids)) as Hnot_in_sigids
  end.
  apply not_app_in, proj1 in Hnot_in_sigids.
  contradiction.    
Qed.
