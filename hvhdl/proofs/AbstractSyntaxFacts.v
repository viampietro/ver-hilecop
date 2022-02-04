(** * Facts about H-VHDL Abstract Syntax *)

Require Import common.CoqLib.
Require Import common.ListLib.

Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.WellDefinedDesign.
Require Import hvhdl.HVhdlTypes.

(** ** Facts about [FoldLCs] and [foldl_cs] *)

Section FoldLCsFacts.

  Functional Scheme foldl_cs_ind := Induction for foldl_cs Sort Prop.
  
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

  Lemma foldl_cs_build_list_by_app_In :
    forall {A : Type} {f : list A -> cs -> list A},
      (forall lofAs1 a,
        exists lofAs2, f lofAs1 a = lofAs1 ++ lofAs2) ->
      forall {cstmt} {lofAs} a, In a lofAs -> In a (foldl_cs f cstmt lofAs).
  Proof.
    intros A f ex_app cstmt lofAs.
    functional induction (foldl_cs f cstmt lofAs) using foldl_cs_ind; cbn.
    1, 2, 4: (match goal with
              | |- forall (_ : _), _ -> In _ (_ ?acc ?cstmt)  =>
                  destruct (ex_app acc cstmt) as [ acc1 f_app ];
                  rewrite f_app; auto
              end).
    auto.
  Qed.

  Lemma foldl_cs_build_list_by_app_nil :
    forall {A : Type} {f : list A -> cs -> list A} {g : cs -> list A},
      (forall lofAs1 a, f lofAs1 a = lofAs1 ++ g a) ->
      forall {cstmt} {lofAs}, foldl_cs f cstmt lofAs = lofAs ++ foldl_cs f cstmt [].
  Proof.
    intros A f g ex_app.
    induction cstmt; cbn; intros lofAs.
    1, 2, 4: match goal with
             | |- ?f ?acc ?cstmt = ?acc ++ ?f [] ?cstmt  =>
                 rewrite (ex_app acc cstmt); rewrite (ex_app [] cstmt); auto
             end.
    rewrite (IHcstmt1 lofAs).
    rewrite (IHcstmt2 (lofAs ++ foldl_cs f cstmt1 [])).
    rewrite (IHcstmt2 (foldl_cs f cstmt1 [])).
    rewrite app_assoc; reflexivity.
  Qed.
    
End FoldLCsFacts.

(** ** Facts about [get_cids] *)

Section GetCIdsFacts.

  Lemma get_cids_InCs :
    forall cstmt id__c id__e g i o, InCs (cs_comp id__c id__e g i o) cstmt -> In id__c (get_cids cstmt).
  Proof.
    unfold get_cids.
    set (build_cids := (fun (cids : list HVhdlTypes.ident) (cstmt : cs) => match cstmt with
                                                                           | cs_comp id _ _ _ _ => cids ++ [id]
                                                                           | _ => cids
                                                                           end)).
    intros cstmt.
    functional induction (foldl_cs build_cids cstmt []) using foldl_cs_ind;
    try (solve [inversion_clear 1]).

    (* CASE [cstmt = cs_comp] *)
    - inversion_clear 1; cbn; auto.

    (* CASE [cs_comp ∈ cstmt1 || cstmt2] *)
    - inversion_clear 1 as [ InCs0 | InCs1 ].
      (* SUBCASE [cs_comp ∈ cstmt1] *)
      + eapply foldl_cs_build_list_by_app_In; eauto; destruct a; cbn.
        1, 3, 4: (exists []; eapply app_nil_end).
        exists [id__c0]; reflexivity.
      + eauto.
  Qed.
  
  Lemma get_cids_app:
    forall cstmt1 cstmt2 : cs, get_cids (cs_par cstmt1 cstmt2) = get_cids cstmt1 ++ get_cids cstmt2.
  Proof.
    unfold get_cids.
    set (build_cids := (fun (cids : list HVhdlTypes.ident) (cstmt : cs) => match cstmt with
                                                                           | cs_comp id _ _ _ _ => cids ++ [id]
                                                                           | _ => cids
                                                                           end)).
    cbn; intros *.
    erewrite @foldl_cs_build_list_by_app_nil with (lofAs := foldl_cs build_cids cstmt1 [])
                                                  (g := fun cstmt => match cstmt with
                                                                     | cs_comp id _ _ _ _ => [id]
                                                                     | _ => []
                                                                     end).
    reflexivity.
    destruct a; cbn.
    1, 3, 4: (eapply app_nil_end).
    reflexivity.
  Qed.
  
  Lemma get_cids_In_ex:
    forall (cstmt : cs) (id__c : ident),
      In id__c (get_cids cstmt) ->
      exists (id__e : ident) (g : genmap) (i : inputmap) (o : outputmap), InCs (cs_comp id__c id__e g i o) cstmt.
  Proof.
    induction cstmt; try (solve [inversion_clear 1]).
    inversion_clear 1 as [ eq_idc | False_ ];
      [ subst; exists id__e, g, i, o; reflexivity | destruct False_ ].
    rewrite get_cids_app.
    intros id__c In_app; edestruct in_app_or as [ In1 | In2 ]; eauto;
      [ edestruct IHcstmt1 as [ id__e [ g [ i [ o InCs1 ] ] ] ]
      | edestruct IHcstmt2 as [ id__e [ g [ i [ o InCs2 ] ] ] ] ];
      eauto; do 4 eexists; [ left | right ]; eauto.
  Qed.
  
End GetCIdsFacts.

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

    inversion_clear 1 as [ InCs0 | InCs0 ];
      inversion_clear 1 as [ InCs1 | InCs1 ]; intros NoDup_par;
      [ eapply IHcstmt1; eauto | | | eapply IHcstmt2; eauto ].

    (* CASE [c0, c1 ∈ cstmt1] and CASE [c0, c1 ∈ cstmt2]. *)
    1,4 : (rewrite get_cids_app in NoDup_par; eauto with nodup).

    (* CASE [c0 ∈ cstmt1] and [c1 ∈ cstmt2], and CASE [c0 ∈ cstmt2]
       and [c1 ∈ cstmt1]. Contradicts NoDup in the two cases. *)
    1, 2: (elimtype False;
           rewrite get_cids_app in NoDup_par;
           eapply nodup_app_not_in; eauto; eapply get_cids_InCs; eauto).    
  Qed.

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




