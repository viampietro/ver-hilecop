(** * Facts about H-VHDL Environment *)

Require Import common.CoqLib.
Require Import common.CoqTactics.
Require Import common.NatSet.

Require Import common.NatMap.
Require Import common.NatMapTactics.
Require Import common.NatSet.

Require Import hvhdl.HVhdlTypes.
Require Import hvhdl.Environment.
Require Import hvhdl.SemanticalDomains.

(** ** Facts about [EqualDom] equivalence *)

Lemma EqualDom_add_1 :
  forall {A : Type} {k} {e : A} {m},
    NatMap.In k m ->
    EqualDom m (NatMap.add k e m).
Proof.
  split; intros.
  destruct (Nat.eq_dec k k0); try subst.
  exists e; apply NatMap.add_1; auto.
  rewrite add_in_iff; right; auto.
  destruct (Nat.eq_dec k k0); try subst; auto.
  erewrite add_in_iff in *; firstorder.
Qed.

(** ** Facts about [merge_natmap] *)

Ltac simpl_merge_map :=
  unfold merge_natmap;
  unfold fold;
  unfold Raw.fold;
  unfold flip;
  try (progress simpl).

Lemma merge_natmap_id_notin_set :
  forall {A : Type} (s : list ident) (m1 m2 : IdMap A) (k : ident) (a : A),
    let f := fun m k1 =>
               match find k1 m1 with
               | Some a1 => NatMap.add k1 a1 m
               | _ => m
               end
    in
    ~InA Logic.eq k s ->
    MapsTo k a m2 ->
    MapsTo k a (fold_left f s m2).
Proof.
  induction s.

  (* BASE CASE *)
  - simpl; auto.

  (* IND. CASE *)
  - simpl; intros.
    eapply IHs; eauto.
    destruct (find (elt:=A) a m1); auto.
    eapply NatMap.add_2; eauto.
Qed.

Lemma merge_natmap_id_notin_set_2 :
  forall {A : Type} {s m1 m2 k} {x y : A},
    let f := fun m k1 => match find k1 m1 with
                         | Some a1 => NatMap.add k1 a1 m
                         | _ => m
                         end
    in
    ~InA Logic.eq k s ->
    MapsTo k x m2 ->
    MapsTo k y (fold_left f s m2) ->
    x = y.
Proof.
  induction s.

  (* BASE CASE *)
  - simpl; intros; eapply MapsTo_fun; eauto.

  (* IND. CASE *)
  - simpl; intros.
    eapply IHs with (m2 := match find (elt:=A) a m1 with
            | Some a1 => NatMap.add a a1 m2
            | None => m2
                           end);
      eauto.
    destruct (find (elt:=A) a m1); auto.
    eapply NatMap.add_2; eauto.
Qed.

Lemma merge_natmap_notin_m1 :
  forall {A : Type} {s m1 m2 k} {a : A},
    let f := fun m k1 => match find k1 m1 with
                         | Some a1 => NatMap.add k1 a1 m
                         | _ => m
                         end
    in
    ~NatMap.In k m1 ->
    MapsTo k a (fold_left f s m2) ->
    NatMap.In k m2.
Proof.
  induction s; simpl; intros.
  (* BASE CASE *)
  - exists a; auto.
  (* IND. CASE *)
  - case_eq (find (elt:=A) a m1).
    (* find = Some x *)
    intros x e.
    erewrite <- add_neq_in_iff with (x := a) (e := x); eauto.
    rewrite e in *; eapply IHs; eauto.
    intros e1; try subst.
    match goal with
    | [ H: ~NatMap.In _ _ |- _ ] =>
      apply H; exists x; eapply find_2; eauto
    end.    
    (* find = None *)
    intros e; rewrite e in *; eapply IHs; eauto.
Qed.

Lemma merge_natmap_EqualDom_1 :
  forall {A: Type} {s m1 m2 m3},
    EqualDom m3 m1 ->
    EqualDom m3 m2 ->
    EqualDom m1 (@merge_natmap A s m2 m3).
Proof.
  destruct s; induction this0.
  (* BASE CASE *)
  - simpl_merge_map; intros; firstorder. 
  (* IND. CASE *)
  - simpl_merge_map; intros; case_eq (find (elt:=A) a m2); intros; eapply IHthis0; eauto.
    rewrite <- H; symmetry; eapply EqualDom_add_1; eauto.
    rewrite (H0 a); exists a0; eapply find_2; eauto.
    rewrite <- H0; symmetry; eapply EqualDom_add_1; eauto.
    rewrite (H0 a); exists a0; eapply find_2; eauto.
    Unshelve.
    inversion_clear is_ok0; auto.
    inversion_clear is_ok0; auto.
Qed.

Lemma merge_natmap_compl_1 :
  forall {A : Type} s m1 m2 k (a : A),
    NatSet.In k s ->
    MapsTo k a m1 ->
    MapsTo k a (merge_natmap s m1 m2).
Proof.
  destruct s; induction this0.
  (* BASE CASE *)
  - inversion 1.
  (* IND. CASE *)
  - intros; unfold merge_natmap; unfold fold; unfold Raw.fold; unfold flip.
    simpl.
    inversion_clear H; try subst.
    (* k = a *)
    + erewrite find_1; eauto.
      eapply merge_natmap_id_notin_set; eauto.
      inversion_clear is_ok0; auto.
      eapply NatMap.add_1; eauto.
    (* use ind. hyp. *)
    + eapply IHthis0; eauto.
      Unshelve.
      inversion_clear is_ok0; auto.
Qed.

Lemma merge_natmap_compl_2 :
  forall {A : Type} s m1 m2 k (a : A),
    ~NatSet.In k s ->
    MapsTo k a m2 ->
    MapsTo k a (merge_natmap s m1 m2).
Proof.
  unfold merge_natmap; unfold fold; unfold Raw.fold; unfold flip.
  intros; eapply merge_natmap_id_notin_set; eauto.
Qed.

Lemma merge_natmap_sound_1 :
  forall {A : Type} s m1 m2 k (a : A),
    NatSet.In k s ->
    EqualDom m1 m2 ->
    MapsTo k a (merge_natmap s m1 m2) ->
    MapsTo k a m1.
Proof.
  destruct s; induction this0.
  (* BASE CASE *)
  - inversion 1.
  (* IND. CASE *)
  - simpl_merge_map; inversion_clear 1; try subst.
    (* CASE k = a *)
    + case_eq (find (elt:=A) a m1). 
      (* find = Some a *)
      intros x e EqualDom_m1m2 MapsTo_foldl.
      erewrite <- @merge_natmap_id_notin_set_2 with (k := a) (x := x) (y := a0); eauto;
        [ eapply find_2; eauto | inversion is_ok0; auto | eapply NatMap.add_1; eauto].
      (* find = None *)
      intros e EqualDom_m1m2 MapsTo_foldl.
      assert (NatMap.In a m2) by (eapply merge_natmap_notin_m1; eauto;
                                  erewrite not_find_in_iff; eauto).
      assert (~NatMap.In a m1) by (erewrite not_find_in_iff; eauto).
      assert (NatMap.In a m1) by (unfold EqualDom in EqualDom_m1m2; erewrite EqualDom_m1m2; eauto).
      contradiction.

    (* CASE use ind. hyp. *)
    + intros EqualDom_m1m2 MapsTo_foldl;
        eapply IHthis0 with (m2 := match find (elt:=A) a m1 with
                                   | Some a1 => NatMap.add a a1 m2
                                   | None => m2 end);
        eauto.
      case_eq (find (elt:=A) a m1); auto.
      intros x e; split; erewrite add_in_iff.
      right; unfold EqualDom in EqualDom_m1m2; erewrite <- EqualDom_m1m2; assumption.
      inversion_clear 1; [ try subst | unfold EqualDom in EqualDom_m1m2; erewrite EqualDom_m1m2; assumption].
      exists x; eapply find_2; assumption.
      Unshelve. inversion_clear is_ok0; auto.
Qed.

Lemma merge_natmap_sound_2 :
  forall {A : Type} s m1 m2 k (a : A),
    ~NatSet.In k s ->
    EqualDom m1 m2 ->
    MapsTo k a (merge_natmap s m1 m2) ->
    MapsTo k a m2.
Proof.
  destruct s; induction this0.
  (* BASE CASE *)
  - simpl_merge_map; auto.
  (* IND. CASE *)
  - simpl_merge_map; do 5 intro; intros EqualDom_m1m2; intros.
    case_eq (find (elt:=A) a m1). 
    (* find = Some a *)
    intros x e; rewrite e in *.
    eapply NatMap.add_3 with (x := a) (e' := x).
    intro; try subst; apply H; auto with set.
    eapply IHthis0; eauto.
    intro; apply H; eapply InA_cons_tl; auto.
    erewrite EqualDom_m1m2.
    eapply EqualDom_add_1.
    unfold  EqualDom in EqualDom_m1m2.
    erewrite <- EqualDom_m1m2.
    exists x; eapply find_2; eauto.
    (* find = None *)
    intros e; rewrite e in *.
    eapply IHthis0; eauto.
    intro; apply H; eapply InA_cons_tl; auto.
    Unshelve. inversion_clear is_ok0; auto.
    inversion_clear is_ok0; auto.
Qed.

Lemma merge_sstore_compl_1 :
  forall {id v σ__o σ σ'},
    In id (events σ) ->
    MapsTo id v (sigstore σ) ->
    MapsTo id v (merge_sstore σ__o σ σ').
Proof.
  unfold merge_sstore; intros.
  eapply merge_natmap_compl_1; eauto.
Qed.

Lemma merge_sstore_compl_2 :
  forall {id v σ__o σ σ'},
    ~In id (events σ) ->
    In id (events σ') ->
    MapsTo id v (sigstore σ') ->
    MapsTo id v (merge_sstore σ__o σ σ').
Proof.
  unfold merge_sstore; intros.
  eapply merge_natmap_compl_2; eauto.
  eapply merge_natmap_compl_1; eauto.
Qed.

Lemma merge_sstore_compl_3 :
  forall {id v σ__o σ σ'},
    ~In id (events σ U events σ') ->
    MapsTo id v (sigstore σ__o) ->
    MapsTo id v (merge_sstore σ__o σ σ').
Proof.
  intros; eapply merge_natmap_compl_2; eauto.
  eapply proj1; eapply not_in_union_2; eauto.
  eapply merge_natmap_compl_2; eauto.
  eapply proj2; eapply not_in_union_2; eauto.
Qed.

Lemma merge_sstore_sound_1 :
  forall {id v σ__o σ σ'},
    EqualDom (sigstore σ__o) (sigstore σ) ->
    EqualDom (sigstore σ__o) (sigstore σ') ->
    In id (events σ) ->
    MapsTo id v (merge_sstore σ__o σ σ') ->
    MapsTo id v (sigstore σ).
Proof.
  intros; eapply merge_natmap_sound_1; eauto.
  eapply merge_natmap_EqualDom_1; eauto.
Qed.

Lemma merge_sstore_sound_2 :
  forall {id v σ__o σ σ'},
    EqualDom (sigstore σ__o) (sigstore σ) ->
    EqualDom (sigstore σ__o) (sigstore σ') ->
    In id (events σ') ->
    ~In id (events σ) ->
    MapsTo id v (merge_sstore σ__o σ σ') ->
    MapsTo id v (sigstore σ').
Proof.
  intros; eapply merge_natmap_sound_1 with (m2 := (sigstore σ__o)); eauto.
  symmetry; auto.
  eapply merge_natmap_sound_2; eauto.
  eapply merge_natmap_EqualDom_1; eauto.
Qed.

Lemma merge_sstore_sound_3 :
  forall {id v σ__o σ σ'},
    EqualDom (sigstore σ__o) (sigstore σ) ->
    EqualDom (sigstore σ__o) (sigstore σ') ->
    ~In id (events σ U events σ') ->
    MapsTo id v (merge_sstore σ__o σ σ') ->
    MapsTo id v (sigstore σ__o).
Proof.
  unfold merge_sstore; intros.
  eapply merge_natmap_sound_2 with (s := events σ') (m1 := sigstore σ'); eauto.
  eapply not_in_union_2; eauto.
  symmetry; assumption.
  eapply merge_natmap_sound_2 with (s := events σ) (m1 := sigstore σ); eauto.
  eapply not_in_union_2 with (s := events σ) (s' := events σ'); eauto.
  eapply merge_natmap_EqualDom_1; eauto.
Qed.

Lemma merge_cstore_compl_1 :
  forall {id v σ__o σ σ'},
    In id (events σ) ->
    MapsTo id v (compstore σ) ->
    MapsTo id v (merge_cstore σ__o σ σ').
Proof.
  intros; eapply merge_natmap_compl_1; eauto.
Qed.

Lemma merge_cstore_compl_2 :
  forall {id v σ__o σ σ'},
    ~In id (events σ) ->
    In id (events σ') ->
    MapsTo id v (compstore σ') ->
    MapsTo id v (merge_cstore σ__o σ σ').
Proof.
  intros; eapply merge_natmap_compl_2; eauto.
  eapply merge_natmap_compl_1; eauto.
Qed.

Lemma merge_cstore_compl_3 :
  forall {id v σ__o σ σ'},
    ~In id (events σ U events σ') ->
    MapsTo id v (compstore σ__o) ->
    MapsTo id v (merge_cstore σ__o σ σ').
Proof.
  intros; eapply merge_natmap_compl_2; eauto.
  eapply proj1; eapply not_in_union_2; eauto.
  eapply merge_natmap_compl_2; eauto.
  eapply proj2; eapply not_in_union_2; eauto.
Qed.

Lemma merge_cstore_sound_1 :
  forall {id v σ__o σ σ'},
    EqualDom (compstore σ__o) (compstore σ) ->
    EqualDom (compstore σ__o) (compstore σ') ->
    In id (events σ) ->
    MapsTo id v (merge_cstore σ__o σ σ') ->
    MapsTo id v (compstore σ).
Proof.
  intros; eapply merge_natmap_sound_1; eauto.
  eapply merge_natmap_EqualDom_1; eauto.
Qed.

Lemma merge_cstore_sound_2 :
  forall {id v σ__o σ σ'},
    EqualDom (compstore σ__o) (compstore σ) ->
    EqualDom (compstore σ__o) (compstore σ') ->
    In id (events σ') ->
    ~In id (events σ) ->
    MapsTo id v (merge_cstore σ__o σ σ') ->
    MapsTo id v (compstore σ').
Proof.
  unfold merge_sstore; intros.
  eapply merge_natmap_sound_1 with (m2 := (compstore σ__o)); eauto.
  symmetry; auto.
  eapply merge_natmap_sound_2; eauto.
  eapply merge_natmap_EqualDom_1; eauto.
Qed.

Lemma merge_cstore_sound_3 :
  forall {id v σ__o σ σ'},
    EqualDom (compstore σ__o) (compstore σ) ->
    EqualDom (compstore σ__o) (compstore σ') ->
    ~In id (events σ U events σ') ->
    MapsTo id v (merge_cstore σ__o σ σ') ->
    MapsTo id v (compstore σ__o).
Proof.
  unfold merge_sstore; intros.
  eapply merge_natmap_sound_2 with (s := events σ') (m1 := compstore σ'); eauto.
  eapply not_in_union_2; eauto.
  symmetry; assumption.
  eapply merge_natmap_sound_2 with (s := events σ) (m1 := compstore σ); eauto.
  eapply not_in_union_2 with (s := events σ) (s' := events σ'); eauto.
  eapply merge_natmap_EqualDom_1; eauto.
Qed.

(** ** Facts about the [IsMergedDState] relation *)

Ltac decompose_IMDS :=
  match goal with
  | [ H: IsMergedDState _ _ _ _ |- _ ] =>
    unfold IsMergedDState in H; decompose [and] H; clear H
  end.

Lemma IsMergedDState_comm :
  forall {σ__o σ σ' σ__m},
    IsMergedDState σ__o σ σ' σ__m <->
    IsMergedDState σ__o σ' σ σ__m.
Proof.
  split; intros; decompose_IMDS;
    let rec solve_imds :=
        match goal with
        | |- IsMergedDState _ _ _ _ => split; solve_imds
        | |- _ /\ _ => split; [solve_imds | solve_imds]
        | |- _ -> _ -> ~NatSet.In _ (_ U _) -> _ <-> _ =>
          intros;
            match goal with
            | [ H: _ -> _ -> ~NatSet.In _ _ -> _ <-> MapsTo _ _ (?f _), H': ~NatSet.In _ _ |- _ <-> MapsTo _ _ (?f _) ] =>
              apply H; auto; do 1 intro; apply H';
                match goal with
                | [ H'': NatSet.In _ (_ U _) |- _ ] =>
                  rewrite union_spec in H''; inversion H''; rewrite union_spec; [right; assumption | left; assumption]
                end
            end
        | |- Equal _ (events ?σ U events ?σ') =>
          transitivity (events σ' U events σ); auto with set
        | _ => firstorder
        end in solve_imds.
Qed.

Lemma IsMergedDState_ex :
  forall {σ__o σ σ'},
    EqualDom (sigstore σ__o) (sigstore σ) ->
    EqualDom (sigstore σ__o) (sigstore σ') ->
    EqualDom (compstore σ__o) (compstore σ) ->
    EqualDom (compstore σ__o) (compstore σ') ->
    Equal (inter (events σ) (events σ')) {[]} -> 
    exists σ__m, IsMergedDState σ__o σ σ' σ__m.
Proof.
  unfold IsMergedDState; intros.
  exists (MkDState (merge_sstore σ__o σ σ') (merge_cstore σ__o σ σ') (events σ U events σ')).
  simpl; split_and; (auto || (try reflexivity)).
  - eapply merge_natmap_EqualDom_1; symmetry;
      eapply merge_natmap_EqualDom_1; (eauto || reflexivity).
  - eapply merge_natmap_EqualDom_1; symmetry;
      eapply merge_natmap_EqualDom_1; (eauto || reflexivity).
  - split; [eapply merge_sstore_compl_1; eauto | eapply merge_sstore_sound_1; eauto].
  - split; [ eapply merge_sstore_compl_2; eauto; eapply inter_empty_2; eauto
           | eapply merge_sstore_sound_2; eauto; eapply inter_empty_2; eauto].
  - split; [ eapply merge_sstore_compl_3; eauto | eapply merge_sstore_sound_3; eauto].
  - split; [ eapply merge_cstore_compl_1; eauto | eapply merge_cstore_sound_1; eauto].
  - split; [ eapply merge_cstore_compl_2; eauto; eapply inter_empty_2; eauto
           | eapply merge_cstore_sound_2; eauto; eapply inter_empty_2; eauto ].
  - split; [ eapply merge_cstore_compl_3; eauto | eapply merge_cstore_sound_3; eauto ].
Qed.

Lemma IsMergedDState_assoc_1 :
  forall {σ σ0 σ1 σ2 σ12 σ01 σ012},
    IsMergedDState σ σ1 σ2 σ12 ->
    IsMergedDState σ σ0 σ12 σ012 ->
    IsMergedDState σ σ0 σ1 σ01 ->
    IsMergedDState σ σ01 σ2 σ012.
Proof.
  intros;
    do 3 decompose_IMDS;
    let rec solve_imds :=
        match goal with
        | |- IsMergedDState _ _ _ _ => split; solve_imds
        | |- _ /\ _ => split; [solve_imds | solve_imds]
        | |- Equal _ (events ?σ U events ?σ') => 
          match goal with
          | [ H: Equal ?ev012 (_ U ?ev12), H': Equal ?ev01 _, H'': Equal ?ev12 _
              |- Equal ?ev012 (?ev01 U _) ] =>
            rewrite H; rewrite H'; rewrite H''; auto with set
          end
        | _ => auto
        end in solve_imds.

        (* [∀ id ∈ (events σ01) -> (sigstore σ01) (id) = (sigstore σ012) (id)] *)
        - intros;
            match goal with
            | [ H: Equal (events ?σ) (_ U _), H': NatSet.In _ (_ ?σ) |- MapsTo _ _ (_ ?σ) <-> _ ] =>
              rewrite H, union_spec in H'; inversion H'
            end.

          (* CASE [id ∈ (events σ0)] *)
          transitivity (MapsTo id v (sigstore σ0)); rw_mapsto.
          
          (* CASE [id ∈ (events σ1) ] *)
          transitivity (MapsTo id v (sigstore σ1)); [rw_mapsto | auto].
          transitivity (MapsTo id v (sigstore σ12)); rw_mapsto;
            match goal with
            | [ H: Equal (events ?σ12) _ |- NatSet.In _ (events ?σ12) ] =>
              rewrite H; auto with set
            end.

        (* [∀ id ∈ (events σ2) -> (sigstore σ2) (id) = (sigstore σ012) (id)] *)
        - intros;
            transitivity (MapsTo id v (sigstore σ12)); rw_mapsto;
              match goal with
              | [ H: Equal (events ?σ12) _ |- NatSet.In _ (events ?σ12) ] =>
                rewrite H; auto with set
              end.

        (* [∀ id ∉ (events σ01) U (events σ2) -> (sigstore σ) (id) = (sigstore σ012) (id)] *)
        - intros id v; intros; rw_mapsto.
          match goal with
          | [ H: Equal (events ?σ12) _, H': Equal (events ?σ01) _, H'': ~NatSet.In _ (events ?σ01 U _)
              |- ~NatSet.In _ (_ U events ?σ12) ] =>
            rewrite H' in H''; rewrite H; erewrite <- union_assoc; eauto
          end.

        (* [∀ id ∈ (events σ01) -> (compstore σ01) (id) = (compstore σ012) (id)] *)
        - intros id v; intros;
            match goal with
            | [ H: Equal (events ?σ) (_ U _), H': NatSet.In _ (_ ?σ) |- MapsTo _ _ (_ ?σ) <-> _ ] =>
              rewrite H, union_spec in H'; inversion H'
            end.

          (* CASE [id ∈ (events σ0)] *)
          transitivity (MapsTo id v (compstore σ0)); rw_mapsto.
          
          (* CASE [id ∈ (events σ1) ] *)
          transitivity (MapsTo id v (compstore σ1)); [rw_mapsto | auto].
          transitivity (MapsTo id v (compstore σ12)); rw_mapsto;
            match goal with
            | [ H: Equal (events ?σ12) _ |- NatSet.In _ (events ?σ12) ] =>
              rewrite H; auto with set
            end.

        (* [∀ id ∈ (events σ2) -> (compstore σ2) (id) = (compstore σ012) (id)] *)
        - intros id v; intros;
            transitivity (MapsTo id v (compstore σ12)); rw_mapsto;
              match goal with
              | [ H: Equal (events ?σ12) _ |- NatSet.In _ (events ?σ12) ] =>
                rewrite H; auto with set
              end.

        (* [∀ id ∉ (events σ01) U (events σ2) -> (compstore σ) (id) = (compstore σ012) (id)] *)
        - intros id v; intros; rw_mapsto.
          match goal with
          | [ H: Equal (events ?σ12) _, H': Equal (events ?σ01) _, H'': ~NatSet.In _ (events ?σ01 U _)
              |- ~NatSet.In _ (_ U events ?σ12) ] =>
            rewrite H' in H''; rewrite H; erewrite <- union_assoc; eauto
          end.
Qed.

Lemma IsMergedDState_assoc_2 :
  forall {σ σ0 σ1 σ2 σ12 σ01 σ012},
    IsMergedDState σ σ0 σ1 σ01 ->
    IsMergedDState σ σ01 σ2 σ012 ->
    IsMergedDState σ σ1 σ2 σ12 ->
    IsMergedDState σ σ0 σ12 σ012.
Proof.
  intros;
    do 3 decompose_IMDS;
    let rec solve_imds :=
        match goal with
        | |- IsMergedDState _ _ _ _ => split; solve_imds
        | |- _ /\ _ => split; [solve_imds | solve_imds]
        | |- Equal _ (events ?σ U events ?σ') =>
          match goal with
          | [ H: Equal ?ev012 (?ev01 U _), H': Equal ?ev01 _, H'': Equal ?ev12 _
              |- Equal ?ev012 (_ U ?ev12) ] =>
            rewrite H; rewrite H'; rewrite H''; auto with set
          end
        | _ => auto
        end in solve_imds.

        (* [∀ id ∈ (events σ0) -> (sigstore σ0) (id) = (sigstore σ012) (id)] *)
        - intros;
            transitivity (MapsTo id v (sigstore σ01)); rw_mapsto;
              match goal with
              | [ H: Equal (events ?σ01) _ |- NatSet.In _ (events ?σ01) ] =>
                rewrite H; auto with set
              end.
        
        (* [∀ id ∈ (events σ12) -> (sigstore σ12) (id) = (sigstore σ012) (id)] *)
        - intros;
          match goal with
          | [ H: Equal (events ?σ) (_ U _), H': NatSet.In _ (_ ?σ) |- MapsTo _ _ (_ ?σ) <-> _ ] =>
            rewrite H, union_spec in H'; inversion H'
          end.

          (* CASE [id ∈ (events σ1)] *)
          transitivity (MapsTo id v (sigstore σ1)); [ rw_mapsto | auto].
          transitivity (MapsTo id v (sigstore σ01)); rw_mapsto;
            match goal with
            | [ H: Equal (events ?σ12) _ |- NatSet.In _ (events ?σ12) ] =>
              rewrite H; auto with set
            end.
          
          (* CASE [id ∈ (events σ2) ] *)
          transitivity (MapsTo id v (sigstore σ2)); rw_mapsto.
          
        (* [∀ id ∉ (events σ0) U (events σ12) -> (sigstore σ) (id) = (sigstore σ012) (id)] *)
        - intros id v; intros; rw_mapsto.
          match goal with
          | [ H: Equal (events ?σ01) _, H': Equal (events ?σ12) _, H'': ~NatSet.In _ (_ U events ?σ12)
              |- ~NatSet.In _ (events ?σ01 U _) ] =>
            rewrite H' in H''; rewrite H; erewrite union_assoc; eauto
          end.

        (* [∀ id ∈ (events σ0) -> (compstore σ0) (id) = (compstore σ012) (id)] *)
        - intros id v; intros;
            transitivity (MapsTo id v (compstore σ01)); rw_mapsto;
              match goal with
              | [ H: Equal (events ?σ01) _ |- NatSet.In _ (events ?σ01) ] =>
                rewrite H; auto with set
              end.
          
        (* [∀ id ∈ (events σ12) -> (compstore σ12) (id) = (compstore σ012) (id)] *)
        - intros id v; intros;
            match goal with
            | [ H: Equal (events ?σ) (_ U _), H': NatSet.In _ (_ ?σ) |- MapsTo _ _ (_ ?σ) <-> _ ] =>
              rewrite H, union_spec in H'; inversion H'
            end.

          (* CASE [id ∈ (events σ1)] *)
          transitivity (MapsTo id v (compstore σ1)); [ rw_mapsto | auto].
          transitivity (MapsTo id v (compstore σ01)); rw_mapsto;
            match goal with
            | [ H: Equal (events ?σ12) _ |- NatSet.In _ (events ?σ12) ] =>
              rewrite H; auto with set
            end.
          
          (* CASE [id ∈ (events σ2) ] *)
          transitivity (MapsTo id v (compstore σ2)); rw_mapsto.
          
        (* [∀ id ∉ (events σ0) U (events σ12) -> (compstore σ) (id) = (compstore σ012) (id)] *)
        - intros id v; intros; rw_mapsto.
          match goal with
          | [ H: Equal (events ?σ01) _, H': Equal (events ?σ12) _, H'': ~NatSet.In _ (_ U events ?σ12)
              |- ~NatSet.In _ (events ?σ01 U _) ] =>
            rewrite H' in H''; rewrite H; erewrite union_assoc; eauto
          end.
Qed.

