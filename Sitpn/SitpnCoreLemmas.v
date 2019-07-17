(* Import Sitpn material. *)

Require Import Hilecop.Sitpn.Sitpn.
Require Import Hilecop.Sitpn.SitpnTokenPlayer.
Require Import Hilecop.Sitpn.SitpnSemantics.

(* Import Sitpn tactics, and misc. lemmas. *)

Require Import Hilecop.Sitpn.SitpnTactics.
Require Import Hilecop.Utils.HilecopLemmas.
Require Import Hilecop.Utils.HilecopTactics.

(* Import tertium non datur axiom. *)

Require Import Classical_Prop.

Set Implicit Arguments.

(** * Sitpn Core Lemmas. *)

(** ** Lemmas on the Sitpn structure. *)

Section SitpnLemmas.
  
  (** For all well-defined Sitpn, If a Place p ∈ neighbourhood of Trans t, then 
      p ∈ (flatten_lneighbours sitpn.(lneighbours)). *)

  Lemma in_neigh_in_flatten :
    forall (sitpn : Sitpn) (t : Trans) (p : Place),
      IsWellDefinedSitpn sitpn ->
      In t (transs sitpn) ->
      In p (flatten_neighbours (lneighbours sitpn t)) ->
      In p (flatten_lneighbours sitpn (transs sitpn)).
  Proof.
    intros sitpn;
      functional induction (flatten_lneighbours sitpn (transs sitpn))
                 using flatten_lneighbours_ind;
      intros t' p Hwell_def_sitpn Hin_t_transs Hin_p_flatn.

    (* BASE CASE. *)
    - inversion Hin_t_transs.

    (* GENERAL CASE *)
    - inversion_clear Hin_t_transs as [Heq_tt' | Hin_t'_tl].

      (* Case t = t' *)
      + rewrite Heq_tt'; apply in_or_app; left; assumption.

      (* Case t' ∈ tl *)
      + apply in_or_app; right.
        apply (IHl0 t' p Hwell_def_sitpn Hin_t'_tl Hin_p_flatn).
  Qed.
  
End SitpnLemmas.

(** ** Lemmas on [get_value] function. *)

Section GetValueLemmas.

  Variable A B : Type.

  Lemma get_value_correct :
    forall (eq_dec : forall (x y : A), {x = y} + {x <> y})
           (key : A)
           (l : list (A * B))
           (value : B),
      get_value eq_dec key l = Some value ->
      In (key, value) l.
  Proof.
    intros eq_dec key l;
      functional induction (get_value eq_dec key l) using get_value_ind;
      intros v Hfun.

    (* BASE CASE. *)
    - inversion Hfun.

    (* CASE key is in head couple. *)
    - injection Hfun as Heq_v; rewrite Heq_v; apply in_eq.

    (* CASE key is not in head couple. *)
    - apply in_cons; apply IHo; assumption.
  Qed.
  
  Lemma get_value_complete :
    forall (eq_dec : forall (x y : A), {x = y} + {x <> y})
           (key : A)
           (l : list (A * B))
           (value : B),
      NoDup (fst (split l)) ->
      In (key, value) l ->
      get_value eq_dec key l = Some value.
  Proof.
    intros eq_dec key l;
      functional induction (get_value eq_dec key l) using get_value_ind;
      intros v Hnodup_fs_l Hin_kv_l.

    (* BASE CASE *)
    - inversion Hin_kv_l.

    (* CASE key is in head couple. *)
    - rewrite fst_split_cons_app in Hnodup_fs_l; simpl in Hnodup_fs_l.
      apply NoDup_cons_iff in Hnodup_fs_l.

      (* Two cases, (key, v) = (key, value) or (key, v) ∈ tl. *)
      inversion_clear Hin_kv_l as [Heq_kv | Hin_kv_tl].

      (* Case (key, v) = (key, value) *)
      + injection Heq_kv as Heq_v; rewrite Heq_v; reflexivity.

      (* Case (key, v) ∈ tl *)
      + apply proj1 in Hnodup_fs_l.
        apply in_fst_split in Hin_kv_tl; contradiction.

    (* CASE key not in head couple. *)
    - apply IHo.
      + rewrite fst_split_cons_app in Hnodup_fs_l; simpl in Hnodup_fs_l.
        apply NoDup_cons_iff in Hnodup_fs_l.
        apply proj2 in Hnodup_fs_l; assumption.
      + inversion_clear Hin_kv_l as [Heq_kv_xv | Hin_kv_tl].
        -- injection Heq_kv_xv as Heq_xk Heq_vv; contradiction.
        -- assumption.
  Qed.

  (** No error lemma for get_value. *)

  Lemma get_value_no_error :
    forall (eq_dec : forall (x y : A), {x = y} + {x <> y})
           (key : A)
           (l : list (A * B)),
      In key (fst (split l)) ->
      exists value : B, get_value eq_dec key l = Some value.
  Proof.
    intros eq_dec key l Hin_k_fsl.
    induction l.
    - simpl in Hin_k_fsl; inversion Hin_k_fsl.
    - dependent induction a; simpl; case (eq_dec a key).
      + intro; exists b; reflexivity.
      + intro Heq_false; rewrite fst_split_cons_app in Hin_k_fsl.
        simpl in Hin_k_fsl.
        inversion_clear Hin_k_fsl as [Heq_ak | Hin_k_tl].
        -- contradiction.
        -- apply (IHl Hin_k_tl).
  Qed.
  
End GetValueLemmas.

(** ** Lemmas on map_check functions. *)

Section MapCheckFunctions.

  (*! Map Check Pre functions. !*)
  
  (** Correctness proof for [check_pre]. *)

  Lemma check_pre_correct :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (p : Place)
           (t : Trans)
           (n : nat),
      IsWellDefinedSitpn sitpn ->
      (places sitpn) = (fst (split marking)) ->
      In (p, n) marking ->
      check_pre sitpn marking p t = Some true ->
      (pre sitpn t p) <= n.
  Proof.
    intros sitpn marking p t;
      functional induction (check_pre sitpn marking p t) using check_pre_ind;
      intros n Hwel_def_sitpn Heq_pls_fsm Hin_m Hfun.
    
    (* GENERAL CASE, all went well. *)
    - apply get_value_correct in e.
      
      (* Proves that ∀ (p, n), (p, nboftokens) ∈ marking ⇒ n = nboftokens. *)
      explode_well_defined_sitpn.
      unfold NoDupPlaces in Hnodup_places.
      assert (Hnodup_fs_m := Hnodup_places).
      rewrite Heq_pls_fsm in Hnodup_fs_m.
      assert (Heq_pp : fst (p, n) = fst (p, nboftokens)) by (simpl; reflexivity).

      specialize (nodup_same_pair
                    marking Hnodup_fs_m (p, n) (p, nboftokens)
                    Hin_m e Heq_pp) as Heq_nnb.
      injection Heq_nnb as Heq_nnb.
      rewrite <- Heq_nnb in Hfun; injection Hfun as Hfun.
      apply (leb_complete (pre sitpn t p) n Hfun).

    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** Completeness proof for [check_pre]. *)

  Lemma check_pre_complete :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (p : Place)
           (t : Trans)
           (n : nat),
      IsWellDefinedSitpn sitpn ->
      (places sitpn) = fst (split marking) ->
      In (p, n) marking ->
      (pre sitpn t p) <= n ->
      check_pre sitpn marking p t = Some true.
  Proof.
    intros sitpn marking p t n Hwell_def_sitpn Heq_pls_fsm Hin_m Hspec.
    unfold check_pre.
    
    (* Builds the condition NoDup (fst (split marking)). 
       Necessary to apply get_value_complete. *)
    explode_well_defined_sitpn.
    unfold NoDupPlaces in Hnodup_places.
    assert (Hnodup_fs_m := Hnodup_places).
    rewrite Heq_pls_fsm in Hnodup_fs_m.

    (* Specializes get_value_complete. *)
    specialize (get_value_complete Nat.eq_dec p marking n Hnodup_fs_m Hin_m) as Hget_m.
    rewrite Hget_m.
    apply leb_correct in Hspec; rewrite Hspec; reflexivity.
  Qed.

  (* No error lemma for check_pre. *)

  Lemma check_pre_no_error :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (p : Place)
           (t : Trans),
      In p (fst (split marking)) ->
      exists b : bool,
        check_pre sitpn marking p t = Some b.
  Proof.
    intros sitpn marking p t Hin_fs.
    unfold check_pre.
    specialize (get_value_no_error Nat.eq_dec p marking Hin_fs) as Hget_m_ex.
    inversion_clear Hget_m_ex as (nboftokens & Hget_m).
    rewrite Hget_m; exists (pre sitpn t p <=? nboftokens).
    reflexivity.
  Qed.
  
  (** ∀ sitpn, marking, pre_places, t, b,
      map_check_pre_aux sitpn marking pre_places t b = Some true ⇒
      b = true.
   *)
  Lemma map_check_pre_aux_true_if_true :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (pre_places : list Place)
           (t : Trans)
           (b : bool),
      map_check_pre_aux sitpn marking pre_places t b = Some true ->
      b = true.
  Proof.
    intros sitpn marking pre_places t b;
      functional induction (map_check_pre_aux sitpn marking pre_places t b)
                 using map_check_pre_aux_ind;
      intros.
    - injection H; auto.
    - apply IHo in H; apply andb_prop in H; elim H; auto.
    - inversion H.
  Qed.

  (** Correctness proof for map_check_pre_aux. *)

  Lemma map_check_pre_aux_correct :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (pre_places : list Place)
           (t : Trans)
           (b : bool),
      IsWellDefinedSitpn sitpn ->
      (places sitpn) = fst (split marking) ->
      incl pre_places (pre_pl (lneighbours sitpn t)) ->
      map_check_pre_aux sitpn marking pre_places t b = Some true ->
      forall (p : Place) (n : nat),
        In p pre_places -> In (p, n) marking -> (pre sitpn t p) <= n.
  Proof.
    intros sitpn marking pre_places t b;
      functional induction (map_check_pre_aux sitpn marking pre_places t b)
                 using map_check_pre_aux_ind;
      intros Hwell_def_sitpn Heq_pls_fsm Hincl_pre_pl
             Hfun p' n Hin_pre_pl Hin_m.
    
    (* BASE CASE *)
    - inversion Hin_pre_pl.

    (* INDUCTION CASE *)
    - inversion Hin_pre_pl as [Heq_pp' | Hin_p'_tail].
      + apply map_check_pre_aux_true_if_true in Hfun.
        apply andb_prop in Hfun; apply proj1 in Hfun.
        rewrite Heq_pp' in e0; rewrite Hfun in e0.
        apply (check_pre_correct
                 marking p' t n
                 Hwell_def_sitpn Heq_pls_fsm Hin_m e0).
      + apply incl_cons_inv in Hincl_pre_pl.
        apply (IHo Hwell_def_sitpn Heq_pls_fsm Hincl_pre_pl
                   Hfun p' n Hin_p'_tail Hin_m).

    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** Completeness proof for map_check_pre_aux. *)

  Lemma map_check_pre_aux_complete :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (pre_places : list Place)
           (t : Trans),
      IsWellDefinedSitpn sitpn ->
      In t (transs sitpn) ->
      (places sitpn) = fst (split marking) ->
      incl pre_places (pre_pl (lneighbours sitpn t)) ->
      (forall (p : Place) (n : nat),
          In p pre_places -> In (p, n) marking -> (pre sitpn t p) <= n) ->
      map_check_pre_aux sitpn marking pre_places t true = Some true.
  Proof.
    intros sitpn marking pre_places t;
      functional induction (map_check_pre_aux sitpn marking pre_places t true)
                 using map_check_pre_aux_ind;
      intros Hwell_def_sitpn Hin_t_transs Heq_pls_fsm Hincl_pre_pl Hspec.

    (* BASE CASE *)
    - reflexivity.

    (* GENERAL CASE *)
    - (* Strategy: build ∃ x, (p, x) ∈ marking to apply check_pre_complete. *)

      (* Builds p ∈ (flatten_neighbours (lneighbours sitpn t)) 
         to specialize in_neigh_in_flatten. *)
      assert (Hin_pre_pl : In p (p :: tail)) by apply in_eq.
      specialize (Hincl_pre_pl p Hin_pre_pl) as Hin_pre_pl_t.
      assert (Hin_flat : In p (flatten_neighbours (lneighbours sitpn t)))
        by (unfold flatten_neighbours; apply in_or_app; left; assumption).

      (* Specializes in_neigh_in_flatten. *)
      specialize (in_neigh_in_flatten t p
                    Hwell_def_sitpn Hin_t_transs Hin_flat) as Hin_flat_lneigh.

      (* Builds (p, x) ∈ marking *)
      explode_well_defined_sitpn.
      unfold NoUnknownPlaceInNeighbours in Hunk_pl_neigh.
      unfold incl in Hunk_pl_neigh.
      apply (Hunk_pl_neigh p) in Hin_flat_lneigh.
      rewrite Heq_pls_fsm in Hin_flat_lneigh.
      specialize (in_fst_split_in_pair p marking Hin_flat_lneigh) as Hin_m.
      inversion Hin_m as (x & Hin_m').

      (* Builds pre sitpn t p <= x *)
      specialize (Hspec p x Hin_pre_pl Hin_m') as Hpre_le.
      
      (* Applies check_pre_complete, then the induction hypothesis. *)
      specialize (check_pre_complete marking p t
                    Hwell_def_sitpn Heq_pls_fsm Hin_m' Hpre_le) as Hcheck_pre.
      
      (* Use b = true to rewrite the goal and apply the induction hypothesis. *)
      rewrite Hcheck_pre in e0; injection e0 as Heq_btrue.
      rewrite <- Heq_btrue in IHo; rewrite andb_comm in IHo; rewrite andb_true_r in IHo.
      rewrite <- Heq_btrue; rewrite andb_comm; rewrite andb_true_r.
      
      (* Builds hypotheses and then applies IHo. *)
      apply incl_cons_inv in Hincl_pre_pl.
      assert (Hspec' : forall (p : Place) (n : nat),
                 In p tail -> In (p, n) marking -> pre sitpn t p <= n)
        by (intros p0 n Hin_tail;
            apply in_cons with (a := p) in Hin_tail;
            apply (Hspec p0 n Hin_tail)).
      apply (IHo Hwell_def_sitpn Hin_t_transs Heq_pls_fsm Hincl_pre_pl Hspec').
      
    (* ERROR CASE, then contradiction. *)
    - assert (Hin_pre_pl : In p (p :: tail)) by apply in_eq.
      specialize (Hincl_pre_pl p Hin_pre_pl) as Hin_pre_pl_t.
      assert (Hin_flat : In p (flatten_neighbours (lneighbours sitpn t)))
        by (unfold flatten_neighbours; apply in_or_app; left; assumption).

      (* Builds p ∈ fst (split marking) to specialize check_pre_no_error. *)
      specialize (in_neigh_in_flatten t p Hwell_def_sitpn Hin_t_transs Hin_flat)
        as Hin_flat_lneigh.      
      explode_well_defined_sitpn.
      unfold NoUnknownPlaceInNeighbours in Hunk_pl_neigh.
      unfold incl in Hunk_pl_neigh.
      specialize (Hunk_pl_neigh p Hin_flat_lneigh) as Hin_p_fsm.
      rewrite Heq_pls_fsm in Hin_p_fsm.
      
      (* Applies check_pre_no_error. *)
      specialize (check_pre_no_error sitpn marking p t Hin_p_fsm)
        as Hcheck_pre_noerr.
      inversion_clear Hcheck_pre_noerr as (b & Hcheck_pre_some).

      (* Then, shows a contradiction. *)
      rewrite e0 in Hcheck_pre_some; inversion Hcheck_pre_some.
  Qed.

  (** No error lemma for map_check_pre_aux. *)

  Lemma map_check_pre_aux_no_error :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans)
           (pre_places : list Place)
           (check_result : bool),
      incl pre_places (fst (split marking)) ->
      exists b : bool,
        map_check_pre_aux sitpn marking pre_places t check_result = Some b.
  Proof.
    intros sitpn marking t; induction pre_places; intros check_result Hincl_prepl.

    (* BASE CASE *)
    - simpl; exists check_result; reflexivity.

    (* INDUCTION CASE *)
    - simpl.
      assert (Hin_a_fs: In a (a :: pre_places)) by apply in_eq.
      apply (Hincl_prepl a) in Hin_a_fs.
      specialize (check_pre_no_error sitpn marking a t Hin_a_fs) as Hcheck_pre_ex.
      inversion_clear Hcheck_pre_ex as (b & Hcheck_pre).
      rewrite Hcheck_pre.
      apply incl_cons_inv in Hincl_prepl.
      apply (IHpre_places (b && check_result) Hincl_prepl).
  Qed.
  
  (** Correctness proof for map_check_pre. *)

  Lemma map_check_pre_correct :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans),
      IsWellDefinedSitpn sitpn ->
      (places sitpn) =  fst (split marking) ->
      In t (transs sitpn) ->
      map_check_pre sitpn marking (pre_pl (lneighbours sitpn t)) t = Some true ->
      forall (p : Place) (n : nat), In (p, n) marking -> (pre sitpn t p) <= n.
  Proof.
    intros sitpn marking t;
      functional induction (map_check_pre sitpn marking (pre_pl (lneighbours sitpn t)) t)
                 using map_check_pre_ind;
      intros Hwell_def_sitpn Heq_pl_fsm Hin_t_transs Hfun p n Hin_m.

    assert (Hincl_refl : incl (pre_pl (lneighbours sitpn t)) (pre_pl (lneighbours sitpn t)))
      by apply incl_refl.

    (* Proof in two stages. *)
    assert (Hvee_in_pre_pl := classic (In p (pre_pl (lneighbours sitpn t)))).
    inversion Hvee_in_pre_pl as [Hin_pre_pl | Hnotin_pre_pl]; clear Hvee_in_pre_pl.
    
    (* First stage, p ∈ pre_places, then we apply map_check_pre_aux_correct. *)
    - apply (map_check_pre_aux_correct
               marking t true Hwell_def_sitpn Heq_pl_fsm
               Hincl_refl Hfun p n Hin_pre_pl Hin_m).
      
    (* Second stage, p ∉ pre_places, then (pre sitpn t p) = 0 *)
    - explode_well_defined_sitpn.
      unfold AreWellDefinedPreEdges in Hwell_def_pre.
      specialize (Hwell_def_pre t p Hin_t_transs) as Hw_pre.
      apply proj2 in Hw_pre.
      specialize (Hw_pre Hnotin_pre_pl) as Hw_pre; rewrite Hw_pre; apply Peano.le_0_n.
  Qed.
  
  (** Completeness proof for map_check_pre. *)

  Lemma map_check_pre_complete :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans),
      IsWellDefinedSitpn sitpn ->
      (places sitpn) =  fst (split marking) ->
      In t (transs sitpn) ->
      (forall (p : Place) (n : nat), In (p, n) marking -> (pre sitpn t p) <= n) ->
      map_check_pre sitpn marking (pre_pl (lneighbours sitpn t)) t = Some true.
  Proof.
    intros sitpn marking t;
      functional induction (map_check_pre sitpn marking (pre_pl (lneighbours sitpn t)) t)
                 using map_check_pre_ind;
      intros Hwell_def_sitpn Heq_pl_fsm Hin_t_transs Hspec.
    
    (* Hypothesis : incl (pre_pl neighbours_of_t) (pre_pl neighbours_of_t) 
       for map_check_pre_aux_complete. *)
    assert (Hincl_refl: incl (pre_pl (lneighbours sitpn t)) (pre_pl (lneighbours sitpn t)))
      by apply incl_refl.

    (* Builds ∀ p,n, p ∈ pre_places -> (p, n) ∈ marking -> pre sitpn t p <= n 
       to apply map_check_pre_aux_complete. *)
    assert (Hspec_check_pre :
              forall (p : Place) (n : nat),
                In p (pre_pl (lneighbours sitpn t)) -> In (p, n) marking -> pre sitpn t p <= n) 
      by (intros p n Hin_pre_pl Hin_m; apply (Hspec p n Hin_m)).
      
    (* Apply map_check_pre_aux_complete. *)
    apply (map_check_pre_aux_complete
             marking t Hwell_def_sitpn Hin_t_transs
             Heq_pl_fsm Hincl_refl Hspec_check_pre).    
  Qed.

  (** No error lemma for map_check_pre. *)

  Lemma map_check_pre_no_error :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans)
           (pre_places : list Place),
      incl pre_places (fst (split marking)) ->
      exists b : bool,
        map_check_pre sitpn marking pre_places t = Some b.
  Proof.
    intros sitpn marking t pre_places Hincl_prepl.
    unfold map_check_pre.
    apply (map_check_pre_aux_no_error sitpn marking t true Hincl_prepl).
  Qed.

  (*! Map Check Test functions. !*)
  
  (** Correctness proof for [check_test]. *)

  Lemma check_test_correct :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (p : Place)
           (t : Trans)
           (n : nat),
      IsWellDefinedSitpn sitpn ->
      (places sitpn) = (fst (split marking)) ->
      In (p, n) marking ->
      check_test sitpn marking p t = Some true ->
      (test sitpn t p) <= n.
  Proof.
    intros sitpn marking p t;
      functional induction (check_test sitpn marking p t) using check_test_ind;
      intros n Hwel_def_sitpn Heq_pls_fsm Hin_m Hfun.
    
    (* GENERAL CASE, all went well. *)
    - apply get_value_correct in e.
      
      (* Proves that ∀ (p, n), (p, nboftokens) ∈ marking ⇒ n = nboftokens. *)
      explode_well_defined_sitpn.
      unfold NoDupPlaces in Hnodup_places.
      assert (Hnodup_fs_m := Hnodup_places).
      rewrite Heq_pls_fsm in Hnodup_fs_m.
      assert (Heq_pp : fst (p, n) = fst (p, nboftokens)) by (simpl; reflexivity).

      specialize (nodup_same_pair
                    marking Hnodup_fs_m (p, n) (p, nboftokens)
                    Hin_m e Heq_pp) as Heq_nnb.
      injection Heq_nnb as Heq_nnb.
      rewrite <- Heq_nnb in Hfun; injection Hfun as Hfun.
      apply (leb_complete (test sitpn t p) n Hfun).

    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** Completeness proof for [check_test]. *)

  Lemma check_test_complete :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (p : Place)
           (t : Trans)
           (n : nat),
      IsWellDefinedSitpn sitpn ->
      (places sitpn) = fst (split marking) ->
      In (p, n) marking ->
      (test sitpn t p) <= n ->
      check_test sitpn marking p t = Some true.
  Proof.
    intros sitpn marking p t n Hwell_def_sitpn Heq_pls_fsm Hin_m Hspec.
    unfold check_test.
    
    (* Builds the condition NoDup (fst (split marking)). 
       Necessary to apply get_value_complete. *)
    explode_well_defined_sitpn.
    unfold NoDupPlaces in Hnodup_places.
    assert (Hnodup_fs_m := Hnodup_places).
    rewrite Heq_pls_fsm in Hnodup_fs_m.

    (* Specializes get_value_complete. *)
    specialize (get_value_complete Nat.eq_dec p marking n Hnodup_fs_m Hin_m) as Hget_m.
    rewrite Hget_m.
    apply leb_correct in Hspec; rewrite Hspec; reflexivity.
  Qed.

  (* No error lemma for check_test. *)

  Lemma check_test_no_error :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (p : Place)
           (t : Trans),
      In p (fst (split marking)) ->
      exists b : bool,
        check_test sitpn marking p t = Some b.
  Proof.
    intros sitpn marking p t Hin_fs.
    unfold check_test.
    specialize (get_value_no_error Nat.eq_dec p marking Hin_fs) as Hget_m_ex.
    inversion_clear Hget_m_ex as (nboftokens & Hget_m).
    rewrite Hget_m; exists (test sitpn t p <=? nboftokens).
    reflexivity.
  Qed.
  
  (** ∀ sitpn, marking, test_places, t, b,
      map_check_test_aux sitpn marking test_places t b = Some true ⇒
      b = true.
   *)
  Lemma map_check_test_aux_true_if_true :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (test_places : list Place)
           (t : Trans)
           (b : bool),
      map_check_test_aux sitpn marking test_places t b = Some true ->
      b = true.
  Proof.
    intros sitpn marking test_places t b;
      functional induction (map_check_test_aux sitpn marking test_places t b)
                 using map_check_test_aux_ind;
      intros.
    - injection H; auto.
    - apply IHo in H; apply andb_prop in H; elim H; auto.
    - inversion H.
  Qed.

  (** Correctness proof for map_check_test_aux. *)

  Lemma map_check_test_aux_correct :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (test_places : list Place)
           (t : Trans)
           (b : bool),
      IsWellDefinedSitpn sitpn ->
      (places sitpn) = fst (split marking) ->
      incl test_places (test_pl (lneighbours sitpn t)) ->
      map_check_test_aux sitpn marking test_places t b = Some true ->
      forall (p : Place) (n : nat),
        In p test_places -> In (p, n) marking -> (test sitpn t p) <= n.
  Proof.
    intros sitpn marking test_places t b;
      functional induction (map_check_test_aux sitpn marking test_places t b)
                 using map_check_test_aux_ind;
      intros Hwell_def_sitpn Heq_pls_fsm Hincl_test_pl
             Hfun p' n Hin_test_pl Hin_m.
    
    (* BASE CASE *)
    - inversion Hin_test_pl.

    (* INDUCTION CASE *)
    - inversion Hin_test_pl as [Heq_pp' | Hin_p'_tail].
      + apply map_check_test_aux_true_if_true in Hfun.
        apply andb_prop in Hfun; apply proj1 in Hfun.
        rewrite Heq_pp' in e0; rewrite Hfun in e0.
        apply (check_test_correct
                 marking p' t n
                 Hwell_def_sitpn Heq_pls_fsm Hin_m e0).
      + apply incl_cons_inv in Hincl_test_pl.
        apply (IHo Hwell_def_sitpn Heq_pls_fsm Hincl_test_pl
                   Hfun p' n Hin_p'_tail Hin_m).

    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** Completeness proof for map_check_test_aux. *)

  Lemma map_check_test_aux_complete :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (test_places : list Place)
           (t : Trans),
      IsWellDefinedSitpn sitpn ->
      In t (transs sitpn) ->
      (places sitpn) = fst (split marking) ->
      incl test_places (test_pl (lneighbours sitpn t)) ->
      (forall (p : Place) (n : nat),
          In p test_places -> In (p, n) marking -> (test sitpn t p) <= n) ->
      map_check_test_aux sitpn marking test_places t true = Some true.
  Proof.
    intros sitpn marking test_places t;
      functional induction (map_check_test_aux sitpn marking test_places t true)
                 using map_check_test_aux_ind;
      intros Hwell_def_sitpn Hin_t_transs Heq_pls_fsm Hincl_test_pl Hspec.

    (* BASE CASE *)
    - reflexivity.

    (* GENERAL CASE *)
    - (* Strategy: build ∃ x, (p, x) ∈ marking to apply check_test_complete. *)

      (* Builds p ∈ (flatten_neighbours (lneighbours sitpn t)) 
         to specialize in_neigh_in_flatten. *)
      assert (Hin_test_pl : In p (p :: tail)) by apply in_eq.
      specialize (Hincl_test_pl p Hin_test_pl) as Hin_test_pl_t.
      assert (Hin_flat : In p (flatten_neighbours (lneighbours sitpn t)))
        by (unfold flatten_neighbours;
            apply in_or_app; right;
            apply in_or_app; left; assumption).

      (* Specializes in_neigh_in_flatten. *)
      specialize (in_neigh_in_flatten t p
                    Hwell_def_sitpn Hin_t_transs Hin_flat) as Hin_flat_lneigh.

      (* Builds (p, x) ∈ marking *)
      explode_well_defined_sitpn.
      unfold NoUnknownPlaceInNeighbours in Hunk_pl_neigh.
      unfold incl in Hunk_pl_neigh.
      apply (Hunk_pl_neigh p) in Hin_flat_lneigh.
      rewrite Heq_pls_fsm in Hin_flat_lneigh.
      specialize (in_fst_split_in_pair p marking Hin_flat_lneigh) as Hin_m.
      inversion Hin_m as (x & Hin_m').

      (* Builds test sitpn t p <= x *)
      specialize (Hspec p x Hin_test_pl Hin_m') as Htest_le.
      
      (* Applies check_test_complete, then the induction hypothesis. *)
      specialize (check_test_complete marking p t
                    Hwell_def_sitpn Heq_pls_fsm Hin_m' Htest_le) as Hcheck_test.
      
      (* Use b = true to rewrite the goal and apply the induction hypothesis. *)
      rewrite Hcheck_test in e0; injection e0 as Heq_btrue.
      rewrite <- Heq_btrue in IHo; rewrite andb_comm in IHo; rewrite andb_true_r in IHo.
      rewrite <- Heq_btrue; rewrite andb_comm; rewrite andb_true_r.
      
      (* Builds hypotheses and then applies IHo. *)
      apply incl_cons_inv in Hincl_test_pl.
      assert (Hspec' : forall (p : Place) (n : nat),
                 In p tail -> In (p, n) marking -> test sitpn t p <= n)
        by (intros p0 n Hin_tail;
            apply in_cons with (a := p) in Hin_tail;
            apply (Hspec p0 n Hin_tail)).
      apply (IHo Hwell_def_sitpn Hin_t_transs Heq_pls_fsm Hincl_test_pl Hspec').
      
    (* ERROR CASE, then contradiction. *)
    - assert (Hin_test_pl : In p (p :: tail)) by apply in_eq.
      specialize (Hincl_test_pl p Hin_test_pl) as Hin_test_pl_t.
      assert (Hin_flat : In p (flatten_neighbours (lneighbours sitpn t)))
        by (unfold flatten_neighbours;
            apply in_or_app; right;
            apply in_or_app; left; assumption).

      (* Builds p ∈ fst (split marking) to specialize check_test_no_error. *)
      specialize (in_neigh_in_flatten t p Hwell_def_sitpn Hin_t_transs Hin_flat)
        as Hin_flat_lneigh.      
      explode_well_defined_sitpn.
      unfold NoUnknownPlaceInNeighbours in Hunk_pl_neigh.
      unfold incl in Hunk_pl_neigh.
      specialize (Hunk_pl_neigh p Hin_flat_lneigh) as Hin_p_fsm.
      rewrite Heq_pls_fsm in Hin_p_fsm.
      
      (* Applies check_test_no_error. *)
      specialize (check_test_no_error sitpn marking p t Hin_p_fsm)
        as Hcheck_test_noerr.
      inversion_clear Hcheck_test_noerr as (b & Hcheck_test_some).

      (* Then, shows a contradiction. *)
      rewrite e0 in Hcheck_test_some; inversion Hcheck_test_some.
  Qed.

  (** No error lemma for map_check_test_aux. *)

  Lemma map_check_test_aux_no_error :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans)
           (test_places : list Place)
           (check_result : bool),
      incl test_places (fst (split marking)) ->
      exists b : bool,
        map_check_test_aux sitpn marking test_places t check_result = Some b.
  Proof.
    intros sitpn marking t; induction test_places; intros check_result Hincl_testpl.

    (* BASE CASE *)
    - simpl; exists check_result; reflexivity.

    (* INDUCTION CASE *)
    - simpl.
      assert (Hin_a_fs: In a (a :: test_places)) by apply in_eq.
      apply (Hincl_testpl a) in Hin_a_fs.
      specialize (check_test_no_error sitpn marking a t Hin_a_fs) as Hcheck_test_ex.
      inversion_clear Hcheck_test_ex as (b & Hcheck_test).
      rewrite Hcheck_test.
      apply incl_cons_inv in Hincl_testpl.
      apply (IHtest_places (b && check_result) Hincl_testpl).
  Qed.
  
  (** Correctness proof for map_check_test. *)

  Lemma map_check_test_correct :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans),
      IsWellDefinedSitpn sitpn ->
      (places sitpn) =  fst (split marking) ->
      In t (transs sitpn) ->
      map_check_test sitpn marking (test_pl (lneighbours sitpn t)) t = Some true ->
      forall (p : Place) (n : nat), In (p, n) marking -> (test sitpn t p) <= n.
  Proof.
    intros sitpn marking t;
      functional induction (map_check_test sitpn marking (test_pl (lneighbours sitpn t)) t)
                 using map_check_test_ind;
      intros Hwell_def_sitpn Heq_pl_fsm Hin_t_transs Hfun p n Hin_m.

    assert (Hincl_refl : incl (test_pl (lneighbours sitpn t)) (test_pl (lneighbours sitpn t)))
      by apply incl_refl.

    (* Proof in two stages. *)
    assert (Hvee_in_test_pl := classic (In p (test_pl (lneighbours sitpn t)))).
    inversion Hvee_in_test_pl as [Hin_test_pl | Hnotin_test_pl]; clear Hvee_in_test_pl.
    
    (* First stage, p ∈ test_places, then we apply map_check_test_aux_correct. *)
    - apply (map_check_test_aux_correct
               marking t true Hwell_def_sitpn Heq_pl_fsm
               Hincl_refl Hfun p n Hin_test_pl Hin_m).
      
    (* Second stage, p ∉ test_places, then (test sitpn t p) = 0 *)
    - explode_well_defined_sitpn.
      unfold AreWellDefinedTestEdges in Hwell_def_test.
      specialize (Hwell_def_test t p Hin_t_transs) as Hw_test.
      apply proj2 in Hw_test.
      specialize (Hw_test Hnotin_test_pl) as Hw_test; rewrite Hw_test; apply Peano.le_0_n.
  Qed.
  
  (** Completeness proof for map_check_test. *)

  Lemma map_check_test_complete :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans),
      IsWellDefinedSitpn sitpn ->
      (places sitpn) =  fst (split marking) ->
      In t (transs sitpn) ->
      (forall (p : Place) (n : nat), In (p, n) marking -> (test sitpn t p) <= n) ->
      map_check_test sitpn marking (test_pl (lneighbours sitpn t)) t = Some true.
  Proof.
    intros sitpn marking t;
      functional induction (map_check_test sitpn marking (test_pl (lneighbours sitpn t)) t)
                 using map_check_test_ind;
      intros Hwell_def_sitpn Heq_pl_fsm Hin_t_transs Hspec.
    
    (* Hypothesis : incl (test_pl neighbours_of_t) (test_pl neighbours_of_t) 
       for map_check_test_aux_complete. *)
    assert (Hincl_refl: incl (test_pl (lneighbours sitpn t)) (test_pl (lneighbours sitpn t)))
      by apply incl_refl.

    (* Builds ∀ p,n, p ∈ test_places -> (p, n) ∈ marking -> test sitpn t p <= n 
       to apply map_check_test_aux_complete. *)
    assert (Hspec_check_test :
              forall (p : Place) (n : nat),
                In p (test_pl (lneighbours sitpn t)) -> In (p, n) marking -> test sitpn t p <= n) 
      by (intros p n Hin_test_pl Hin_m; apply (Hspec p n Hin_m)).
      
    (* Apply map_check_test_aux_complete. *)
    apply (map_check_test_aux_complete
             marking t Hwell_def_sitpn Hin_t_transs
             Heq_pl_fsm Hincl_refl Hspec_check_test).    
  Qed.

  (** No error lemma for map_check_test. *)

  Lemma map_check_test_no_error :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans)
           (test_places : list Place),
      incl test_places (fst (split marking)) ->
      exists b : bool,
        map_check_test sitpn marking test_places t = Some b.
  Proof.
    intros sitpn marking t test_places Hincl_testpl.
    unfold map_check_test.
    apply (map_check_test_aux_no_error sitpn marking t true Hincl_testpl).
  Qed.

  (*! Map Check Inhib functions. !*)
  
  (** Correctness proof for [check_inhib]. *)

  Lemma check_inhib_correct :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (p : Place)
           (t : Trans)
           (n : nat),
      IsWellDefinedSitpn sitpn ->
      (places sitpn) = (fst (split marking)) ->
      In (p, n) marking ->
      check_inhib sitpn marking p t = Some true ->
      (inhib sitpn t p) > n \/ (inhib sitpn t p) = 0.
  Proof.
    intros sitpn marking p t;
      functional induction (check_inhib sitpn marking p t) using check_inhib_ind;
      intros n Hwel_def_sitpn Heq_pls_fsm Hin_m Hfun.
    
    (* GENERAL CASE, all went well. *)
    - apply get_value_correct in e.
      
      (* Proves that ∀ (p, n), (p, nboftokens) ∈ marking ⇒ n = nboftokens. *)
      explode_well_defined_sitpn.
      unfold NoDupPlaces in Hnodup_places.
      assert (Hnodup_fs_m := Hnodup_places).
      rewrite Heq_pls_fsm in Hnodup_fs_m.
      assert (Heq_pp : fst (p, n) = fst (p, nboftokens)) by (simpl; reflexivity).

      specialize (nodup_same_pair
                    marking Hnodup_fs_m (p, n) (p, nboftokens)
                    Hin_m e Heq_pp) as Heq_nnb.
      injection Heq_nnb as Heq_nnb.
      rewrite <- Heq_nnb in Hfun; injection Hfun as Hfun.
      apply orb_prop in Hfun.
      
      (* First case: n < (inhib spn t p), second case: (inhib spn t p) = 0 *)
      inversion Hfun as [Hinhib_lt | Hinhib_eq_0].
      + left; apply Nat.ltb_lt; assumption.
      + right; apply Nat.eqb_eq; assumption.
      
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** Completeness proof for [check_inhib]. *)

  Lemma check_inhib_complete :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (p : Place)
           (t : Trans)
           (n : nat),
      IsWellDefinedSitpn sitpn ->
      (places sitpn) = fst (split marking) ->
      In (p, n) marking ->
      (inhib sitpn t p) > n \/ (inhib sitpn t p) = 0 ->
      check_inhib sitpn marking p t = Some true.
  Proof.
    intros sitpn marking p t n Hwell_def_sitpn Heq_pls_fsm Hin_m Hspec.
    unfold check_inhib.
    
    (* Builds the condition NoDup (fst (split marking)). 
       Necessary to apply get_value_complete. *)
    explode_well_defined_sitpn.
    unfold NoDupPlaces in Hnodup_places.
    assert (Hnodup_fs_m := Hnodup_places).
    rewrite Heq_pls_fsm in Hnodup_fs_m.

    (* Specializes get_value_complete. *)
    specialize (get_value_complete Nat.eq_dec p marking n Hnodup_fs_m Hin_m) as Hget_m.
    rewrite Hget_m; inversion Hspec as [Hinhib_lt | Hinhib_eq_0].
    - apply Nat.ltb_lt in Hinhib_lt; rewrite Hinhib_lt.
      rewrite orb_true_l; reflexivity.
    - apply Nat.eqb_eq in Hinhib_eq_0; rewrite Hinhib_eq_0.
      rewrite orb_comm; rewrite orb_true_l; reflexivity.
  Qed.

  (* No error lemma for check_inhib. *)

  Lemma check_inhib_no_error :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (p : Place)
           (t : Trans),
      In p (fst (split marking)) ->
      exists b : bool,
        check_inhib sitpn marking p t = Some b.
  Proof.
    intros sitpn marking p t Hin_fs.
    unfold check_inhib.
    specialize (get_value_no_error Nat.eq_dec p marking Hin_fs) as Hget_v_ex.
    inversion_clear Hget_v_ex as (nboftokens & Hget_v).
    rewrite Hget_v; exists ((nboftokens <? inhib sitpn t p) || (inhib sitpn t p =? 0)).
    reflexivity.
  Qed.
  
  (** ∀ sitpn, marking, inhib_places, t, b,
      map_check_inhib_aux sitpn marking inhib_places t b = Some true ⇒
      b = true.
   *)
  Lemma map_check_inhib_aux_true_if_true :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (inhib_places : list Place)
           (t : Trans)
           (b : bool),
      map_check_inhib_aux sitpn marking inhib_places t b = Some true ->
      b = true.
  Proof.
    intros sitpn marking inhib_places t b;
      functional induction (map_check_inhib_aux sitpn marking inhib_places t b)
                 using map_check_inhib_aux_ind;
      intros.
    - injection H; auto.
    - apply IHo in H; apply andb_prop in H; elim H; auto.
    - inversion H.
  Qed.

  (** Correctness proof for map_check_inhib_aux. *)

  Lemma map_check_inhib_aux_correct :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (inhib_places : list Place)
           (t : Trans)
           (b : bool),
      IsWellDefinedSitpn sitpn ->
      (places sitpn) = fst (split marking) ->
      incl inhib_places (inhib_pl (lneighbours sitpn t)) ->
      map_check_inhib_aux sitpn marking inhib_places t b = Some true ->
      forall (p : Place) (n : nat),
        In p inhib_places ->
        In (p, n) marking ->
        (inhib sitpn t p) > n \/ (inhib sitpn t p) = 0.
  Proof.
    intros sitpn marking inhib_places t b;
      functional induction (map_check_inhib_aux sitpn marking inhib_places t b)
                 using map_check_inhib_aux_ind;
      intros Hwell_def_sitpn Heq_pls_fsm Hincl_inhib_pl
             Hfun p' n Hin_inhib_pl Hin_m.
    
    (* BASE CASE *)
    - inversion Hin_inhib_pl.

    (* INDUCTION CASE *)
    - inversion Hin_inhib_pl as [Heq_pp' | Hin_p'_tail].
      + apply map_check_inhib_aux_true_if_true in Hfun.
        apply andb_prop in Hfun; apply proj1 in Hfun.
        rewrite Heq_pp' in e0; rewrite Hfun in e0.
        apply (check_inhib_correct
                 marking p' t n
                 Hwell_def_sitpn Heq_pls_fsm Hin_m e0).
      + apply incl_cons_inv in Hincl_inhib_pl.
        apply (IHo Hwell_def_sitpn Heq_pls_fsm Hincl_inhib_pl
                   Hfun p' n Hin_p'_tail Hin_m).

    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** Completeness proof for map_check_inhib_aux. *)

  Lemma map_check_inhib_aux_complete :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (inhib_places : list Place)
           (t : Trans),
      IsWellDefinedSitpn sitpn ->
      In t (transs sitpn) ->
      (places sitpn) = fst (split marking) ->
      incl inhib_places (inhib_pl (lneighbours sitpn t)) ->
      (forall (p : Place) (n : nat),
          In p inhib_places ->
          In (p, n) marking ->
          (inhib sitpn t p) > n \/ (inhib sitpn t p) = 0) ->
      map_check_inhib_aux sitpn marking inhib_places t true = Some true.
  Proof.
    intros sitpn marking inhib_places t;
      functional induction (map_check_inhib_aux sitpn marking inhib_places t true)
                 using map_check_inhib_aux_ind;
      intros Hwell_def_sitpn Hin_t_transs Heq_pls_fsm Hincl_inhib_pl Hspec.

    (* BASE CASE *)
    - reflexivity.

    (* GENERAL CASE *)
    - (* Strategy: build ∃ x, (p, x) ∈ marking to apply check_inhib_complete. *)

      (* Builds p ∈ (flatten_neighbours (lneighbours sitpn t)) 
         to specialize in_neigh_in_flatten. *)
      assert (Hin_inhib_pl : In p (p :: tail)) by apply in_eq.
      specialize (Hincl_inhib_pl p Hin_inhib_pl) as Hin_inhib_pl_t.
      assert (Hin_flat : In p (flatten_neighbours (lneighbours sitpn t)))
        by (unfold flatten_neighbours;
            do 2 (apply in_or_app; right);
            apply in_or_app; left; assumption).

      (* Specializes in_neigh_in_flatten. *)
      specialize (in_neigh_in_flatten t p
                    Hwell_def_sitpn Hin_t_transs Hin_flat) as Hin_flat_lneigh.

      (* Builds (p, x) ∈ marking *)
      explode_well_defined_sitpn.
      unfold NoUnknownPlaceInNeighbours in Hunk_pl_neigh.
      unfold incl in Hunk_pl_neigh.
      apply (Hunk_pl_neigh p) in Hin_flat_lneigh.
      rewrite Heq_pls_fsm in Hin_flat_lneigh.
      specialize (in_fst_split_in_pair p marking Hin_flat_lneigh) as Hin_m.
      inversion Hin_m as (x & Hin_m').

      (* Builds inhib sitpn t p <= x *)
      specialize (Hspec p x Hin_inhib_pl Hin_m') as Hinhib_le.
      
      (* Applies check_inhib_complete, then the induction hypothesis. *)
      specialize (check_inhib_complete marking p t
                    Hwell_def_sitpn Heq_pls_fsm Hin_m' Hinhib_le) as Hcheck_inhib.
      
      (* Use b = true to rewrite the goal and apply the induction hypothesis. *)
      rewrite Hcheck_inhib in e0; injection e0 as Heq_btrue.
      rewrite <- Heq_btrue in IHo; rewrite andb_comm in IHo; rewrite andb_true_r in IHo.
      rewrite <- Heq_btrue; rewrite andb_comm; rewrite andb_true_r.
      
      (* Builds hypotheses and then applies IHo. *)
      apply incl_cons_inv in Hincl_inhib_pl.
      assert (Hspec' : forall (p : Place) (n : nat),
                 In p tail ->
                 In (p, n) marking ->
                 inhib sitpn t p > n \/ inhib sitpn t p = 0)
        by (intros p0 n Hin_tail;
            apply in_cons with (a := p) in Hin_tail;
            apply (Hspec p0 n Hin_tail)).
      apply (IHo Hwell_def_sitpn Hin_t_transs Heq_pls_fsm Hincl_inhib_pl Hspec').
      
    (* ERROR CASE, then contradiction. *)
    - assert (Hin_inhib_pl : In p (p :: tail)) by apply in_eq.
      specialize (Hincl_inhib_pl p Hin_inhib_pl) as Hin_inhib_pl_t.
      assert (Hin_flat : In p (flatten_neighbours (lneighbours sitpn t)))
        by (unfold flatten_neighbours;
            do 2 (apply in_or_app; right);
            apply in_or_app; left; assumption).

      (* Builds p ∈ fst (split marking) to specialize check_inhib_no_error. *)
      specialize (in_neigh_in_flatten t p Hwell_def_sitpn Hin_t_transs Hin_flat)
        as Hin_flat_lneigh.      
      explode_well_defined_sitpn.
      unfold NoUnknownPlaceInNeighbours in Hunk_pl_neigh.
      unfold incl in Hunk_pl_neigh.
      specialize (Hunk_pl_neigh p Hin_flat_lneigh) as Hin_p_fsm.
      rewrite Heq_pls_fsm in Hin_p_fsm.
      
      (* Applies check_inhib_no_error. *)
      specialize (check_inhib_no_error sitpn marking p t Hin_p_fsm)
        as Hcheck_inhib_noerr.
      inversion_clear Hcheck_inhib_noerr as (b & Hcheck_inhib_some).

      (* Then, shows a contradiction. *)
      rewrite e0 in Hcheck_inhib_some; inversion Hcheck_inhib_some.
  Qed.

  (** No error lemma for map_check_inhib_aux. *)

  Lemma map_check_inhib_aux_no_error :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans)
           (inhib_places : list Place)
           (check_result : bool),
      incl inhib_places (fst (split marking)) ->
      exists b : bool,
        map_check_inhib_aux sitpn marking inhib_places t check_result = Some b.
  Proof.
    intros sitpn marking t; induction inhib_places; intros check_result Hincl_inhibpl.

    (* BASE CASE *)
    - simpl; exists check_result; reflexivity.

    (* INDUCTION CASE *)
    - simpl.
      assert (Hin_a_fs: In a (a :: inhib_places)) by apply in_eq.
      apply (Hincl_inhibpl a) in Hin_a_fs.
      specialize (check_inhib_no_error sitpn marking a t Hin_a_fs) as Hcheck_inhib_ex.
      inversion_clear Hcheck_inhib_ex as (b & Hcheck_inhib).
      rewrite Hcheck_inhib.
      apply incl_cons_inv in Hincl_inhibpl.
      apply (IHinhib_places (b && check_result) Hincl_inhibpl).
  Qed.
  
  (** Correctness proof for map_check_inhib. *)

  Lemma map_check_inhib_correct :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans),
      IsWellDefinedSitpn sitpn ->
      (places sitpn) =  fst (split marking) ->
      In t (transs sitpn) ->
      map_check_inhib sitpn marking (inhib_pl (lneighbours sitpn t)) t = Some true ->
      forall (p : Place) (n : nat),
        In (p, n) marking -> (inhib sitpn t p) > n \/ (inhib sitpn t p) = 0.
  Proof.
    intros sitpn marking t;
      functional induction (map_check_inhib sitpn marking (inhib_pl (lneighbours sitpn t)) t)
                 using map_check_inhib_ind;
      intros Hwell_def_sitpn Heq_pl_fsm Hin_t_transs Hfun p n Hin_m.

    assert (Hincl_refl : incl (inhib_pl (lneighbours sitpn t)) (inhib_pl (lneighbours sitpn t)))
      by apply incl_refl.

    (* Proof in two stages. *)
    assert (Hvee_in_inhib_pl := classic (In p (inhib_pl (lneighbours sitpn t)))).
    inversion Hvee_in_inhib_pl as [Hin_inhib_pl | Hnotin_inhib_pl]; clear Hvee_in_inhib_pl.
    
    (* First stage, p ∈ inhib_places, then we apply map_check_inhib_aux_correct. *)
    - apply (map_check_inhib_aux_correct
               marking t true Hwell_def_sitpn Heq_pl_fsm
               Hincl_refl Hfun p n Hin_inhib_pl Hin_m).
      
    (* Second stage, p ∉ inhib_places, then (inhib sitpn t p) = 0 *)
    - explode_well_defined_sitpn.
      unfold AreWellDefinedInhibEdges in Hwell_def_inhib.
      specialize (Hwell_def_inhib t p Hin_t_transs) as Hw_inhib.
      apply proj2 in Hw_inhib.
      specialize (Hw_inhib Hnotin_inhib_pl) as Hw_inhib;
        rewrite Hw_inhib; right; reflexivity.
  Qed.
  
  (** Completeness proof for map_check_inhib. *)

  Lemma map_check_inhib_complete :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans),
      IsWellDefinedSitpn sitpn ->
      (places sitpn) =  fst (split marking) ->
      In t (transs sitpn) ->
      (forall (p : Place) (n : nat),
          In (p, n) marking -> (inhib sitpn t p) > n \/ (inhib sitpn t p) = 0) ->
      map_check_inhib sitpn marking (inhib_pl (lneighbours sitpn t)) t = Some true.
  Proof.
    intros sitpn marking t;
      functional induction (map_check_inhib sitpn marking (inhib_pl (lneighbours sitpn t)) t)
                 using map_check_inhib_ind;
      intros Hwell_def_sitpn Heq_pl_fsm Hin_t_transs Hspec.
    
    (* Hypothesis : incl (inhib_pl neighbours_of_t) (inhib_pl neighbours_of_t) 
       for map_check_inhib_aux_complete. *)
    assert (Hincl_refl: incl (inhib_pl (lneighbours sitpn t)) (inhib_pl (lneighbours sitpn t)))
      by apply incl_refl.

    (* Builds ∀ p,n, p ∈ inhib_places -> (p, n) ∈ marking -> inhib sitpn t p <= n 
       to apply map_check_inhib_aux_complete. *)
    assert (Hspec_check_inhib :
              forall (p : Place) (n : nat),
                In p (inhib_pl (lneighbours sitpn t)) ->
                In (p, n) marking ->
                inhib sitpn t p > n \/ inhib sitpn t p = 0) 
      by (intros p n Hin_inhib_pl Hin_m; apply (Hspec p n Hin_m)).
      
    (* Apply map_check_inhib_aux_complete. *)
    apply (map_check_inhib_aux_complete
             marking t Hwell_def_sitpn Hin_t_transs
             Heq_pl_fsm Hincl_refl Hspec_check_inhib).    
  Qed.

  (** No error lemma for map_check_inhib. *)

  Lemma map_check_inhib_no_error :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans)
           (inhib_places : list Place),
      incl inhib_places (fst (split marking)) ->
      exists b : bool,
        map_check_inhib sitpn marking inhib_places t = Some b.
  Proof.
    intros sitpn marking t inhib_places Hincl_inhibpl.
    unfold map_check_inhib.
    apply (map_check_inhib_aux_no_error sitpn marking t true Hincl_inhibpl).
  Qed.
  
End MapCheckFunctions.

(** ** Lemmas on [is_sensitized] function and its spec. *)

Section IsSensitized.

  (** Correctness proof for is_sensitized and IsSensitized *)

  Theorem is_sensitized_correct :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans),
      IsWellDefinedSitpn sitpn ->
      (places sitpn) = fst (split marking) ->
      In t (transs sitpn) -> 
      is_sensitized sitpn marking (lneighbours sitpn t) t = Some true ->
      IsSensitized sitpn marking t.
  Proof.
    intros sitpn marking t;
      functional induction (is_sensitized sitpn marking (lneighbours sitpn t) t)
                 using is_sensitized_ind;
      intros Hwell_def_sitpn Heq_pl_fsm Hin_t_transs Hfun.
    
    (* GENERAL CASE *)
    - injection Hfun; intro Heq_check.
      apply andb_prop in Heq_check; elim Heq_check; intros Heq_check' Heq_inhib.
      apply andb_prop in Heq_check'; elim Heq_check'; intros Heq_pre Heq_test.

      (* Determines ∀ (p, n) ∈ marking, (pre sitpn t p) <= n *)
      rewrite Heq_pre in e.
      specialize (map_check_pre_correct
                    marking t 
                    Hwell_def_sitpn Heq_pl_fsm Hin_t_transs e)
        as Hmap_pre.

      (* Determines ∀ (p, n) ∈ marking, (test sitpn t p) <= n *)
      rewrite Heq_test in e0.
      specialize (map_check_test_correct
                    marking t
                    Hwell_def_sitpn Heq_pl_fsm Hin_t_transs e0)
        as Hmap_test.
      
      (* Determines ∀ (p, n) ∈ marking, n < (inhib sitpn t p) ∨ (inhib sitpn t p) = 0 *)
      rewrite Heq_inhib in e1.
      specialize (map_check_inhib_correct
                    marking t
                    Hwell_def_sitpn Heq_pl_fsm Hin_t_transs e1)
        as Hmap_inhib.

      (* Unfolds IsSensitized and applies all previous lemmas. *)
      unfold IsSensitized; intros p n Hin_m.
      split;
        [apply (Hmap_pre p n Hin_m)
        | split; [ apply (Hmap_test p n Hin_m) |
                   apply (Hmap_inhib p n Hin_m) ]].

    (* ERROR CASES *)
    - inversion Hfun.
    - inversion Hfun.
    - inversion Hfun.
  Qed.

  (** Completeness proof for is_sensitized and IsSensitized *)

  Theorem is_sensitized_complete :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans),
      IsWellDefinedSitpn sitpn ->
      (places sitpn) = fst (split marking) ->
      In t (transs sitpn) ->
      IsSensitized sitpn marking t ->
      is_sensitized sitpn marking (lneighbours sitpn t) t = Some true.
  Proof.
    intros sitpn marking t;
      functional induction (is_sensitized sitpn marking (lneighbours sitpn t) t)
                 using is_sensitized_ind;
      intros Hwell_defined_sitpn Heq_pl_fsm Hin_t_transs Hspec;
      unfold IsSensitized in Hspec;
      
      (* Builds ∀ (p,n) ∈ marking, (pre sitpn t p) ≤ n, 
         then applies map_check_pre_complete.
       *)
      assert (Hmap_check_pre :
                forall (p : Place) (n : nat), In (p, n) marking -> pre sitpn t p <= n) by
          (intros p n Hin_m; generalize (Hspec p n Hin_m) as Hend; intro; elim Hend; auto);
      generalize (map_check_pre_complete marking t
                                         Hwell_defined_sitpn
                                         Heq_pl_fsm
                                         Hin_t_transs
                                         Hmap_check_pre) as Hmap_check_pre';
      intro;
      (* Builds ∀ (p,n) ∈ marking, (test sitpn t p) ≤ n, 
         then applies map_check_test_complete.
       *)
      assert (Hmap_check_test :
                forall (p : Place) (n : nat), In (p, n) marking -> test sitpn t p <= n)
        by (intros p n Hin_m;
            generalize (Hspec p n Hin_m) as Hend;
            intro; decompose [and] Hend; auto);
      generalize (map_check_test_complete marking t
                                          Hwell_defined_sitpn
                                          Heq_pl_fsm
                                          Hin_t_transs
                                          Hmap_check_test) as Hmap_check_test';
      intro;
      (* Builds ∀ (p,n) ∈ marking, (inhib sitpn t p) ≤ n, 
         then applies map_check_inhib_complete.
       *)
      assert (Hmap_check_inhib :
                forall (p : Place) (n : nat),
                  In (p, n) marking -> (n < (inhib sitpn t p) \/ (inhib sitpn t p) = 0))
        by (intros p n Hin_m;
            generalize (Hspec p n Hin_m) as Hend;
            intro; decompose [and] Hend; auto);
      generalize (map_check_inhib_complete marking t
                                           Hwell_defined_sitpn
                                           Heq_pl_fsm
                                           Hin_t_transs
                                           Hmap_check_inhib) as Hmap_check_inhib';
      intro.

    (* General case, all went well. 
       Using IsSensitized to prove that all the map_check functions
       return true. *)
    (* Rewrites the results of map_check functions, then reflexivity. *)
    - rewrite Hmap_check_pre' in e;
        rewrite Hmap_check_test' in e0;
        rewrite Hmap_check_inhib' in e1.
      injection e as e_check_pre_value;
        injection e0 as e_check_test_value;
        injection e1 as e_check_inhib_value.
      rewrite <- e_check_inhib_value;
        rewrite <- e_check_pre_value;
        rewrite <- e_check_test_value.
      do 2 rewrite andb_true_r; reflexivity.
      
    (* CASE map_check_inhib returns None, impossible regarding the hypotheses. *)
    - rewrite Hmap_check_inhib' in e1; inversion e1.
      
    (* CASE map_check_test returns None, impossible regarding the hypotheses. *)
    - rewrite Hmap_check_test' in e0; inversion e0.
      
    (* CASE map_check_pre returns None, impossible regarding the hypotheses. *)
    - rewrite Hmap_check_pre' in e; inversion e.
  Qed.

  (** No error lemma for is_sensitized. *)

  Theorem is_sensitized_no_error :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans),
      incl (flatten_neighbours (lneighbours sitpn t)) (fst (split marking)) ->
      exists b : bool,
        is_sensitized sitpn marking (lneighbours sitpn t) t = Some b.
  Proof.
    intros sitpn marking t Hincl_flat.
    unfold is_sensitized.

    (* Prepares hypotheses to apply no error lemmas. *)
    assert (Hincl_prepl : incl (pre_pl (lneighbours sitpn t)) (fst (split marking))).
    {
      intros p Hin_prepl.
      apply or_introl
        with (B := In p ((test_pl (lneighbours sitpn t))
                           ++ (inhib_pl (lneighbours sitpn t))
                           ++ (post_pl (lneighbours sitpn t))))
        in Hin_prepl.
      apply in_or_app in Hin_prepl.
      apply (Hincl_flat p Hin_prepl).      
    }

    assert (Hincl_testpl : incl (test_pl (lneighbours sitpn t)) (fst (split marking))).
    {
      intros p Hin_testpl.
      apply or_intror
        with (A := In p (pre_pl (lneighbours sitpn t)))
        in Hin_testpl.
      apply in_or_app in Hin_testpl.
      apply or_introl
        with (B := In p ((inhib_pl (lneighbours sitpn t)) ++ (post_pl (lneighbours sitpn t))))
        in Hin_testpl.
      apply in_or_app in Hin_testpl.
      rewrite <- app_assoc in Hin_testpl.
      apply (Hincl_flat p Hin_testpl).      
    }

    assert (Hincl_inhibpl : incl (inhib_pl (lneighbours sitpn t)) (fst (split marking))).
    {
      intros p Hin_inhibpl.
      apply or_intror
        with (A := In p ((pre_pl (lneighbours sitpn t)) ++ (test_pl (lneighbours sitpn t))))
        in Hin_inhibpl.
      apply in_or_app in Hin_inhibpl.
      apply or_introl
        with (B := In p (post_pl (lneighbours sitpn t)))
        in Hin_inhibpl.
      apply in_or_app in Hin_inhibpl.
      do 2 (rewrite <- app_assoc in Hin_inhibpl).
      apply (Hincl_flat p Hin_inhibpl).      
    }

    specialize (map_check_pre_no_error sitpn marking t Hincl_prepl)
      as Hmap_check_pre_ex.

    specialize (map_check_test_no_error sitpn marking t Hincl_testpl)
      as Hmap_check_test_ex.

    specialize (map_check_inhib_no_error sitpn marking t Hincl_inhibpl)
      as Hmap_check_inhib_ex.

    inversion_clear Hmap_check_pre_ex as (check_pre_result & Hmap_check_pre).
    inversion_clear Hmap_check_test_ex as (check_test_result & Hmap_check_test).
    inversion_clear Hmap_check_inhib_ex as (check_inhib_result & Hmap_check_inhib).

    rewrite Hmap_check_pre, Hmap_check_test, Hmap_check_inhib.

    exists (check_pre_result && check_test_result && check_inhib_result); reflexivity.

  Qed.

  (** Conjunction of correction and completeness for is_sensitized. *)

  Theorem is_sensitized_iff :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans),
      IsWellDefinedSitpn sitpn ->
      (places sitpn) = fst (split marking) -> 
      In t (transs sitpn) ->
      is_sensitized sitpn marking (lneighbours sitpn t) t = Some true <->
      IsSensitized sitpn marking t.
  Proof.
    intros sitpn marking t Hwell_def_sitpn Heq_pl_fsm Hin_t_transs.
    split;
      [ intro Hfun;
        apply (is_sensitized_correct marking t
                                     Hwell_def_sitpn Heq_pl_fsm
                                     Hin_t_transs Hfun)
      | intro Hspec;
        apply (is_sensitized_complete Hwell_def_sitpn Heq_pl_fsm
                                      Hin_t_transs Hspec) ].
  Qed.

  (** Conjunction of correction and completeness for ~is_sensitized. *)

  Theorem not_is_sensitized_iff :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans),
      IsWellDefinedSitpn sitpn ->
      (places sitpn) = fst (split marking) -> 
      In t (transs sitpn) ->
      is_sensitized sitpn marking (lneighbours sitpn t) t = Some false <->
      ~IsSensitized sitpn marking t.
  Proof.
    intros sitpn marking t Hwell_def_sitpn Heq_pl_fsm Hin_t_transs.
    split.
    
    - intros Hfun Hspec;
        rewrite <- (is_sensitized_iff marking t
                                      Hwell_def_sitpn Heq_pl_fsm Hin_t_transs)
        in Hspec.
      rewrite Hfun in Hspec; inversion Hspec.

    - intro Hspec; case_eq (is_sensitized sitpn marking (lneighbours sitpn t) t).
      + dependent induction b.
        -- intros His_sens_fun.
           rewrite <- (is_sensitized_iff marking t
                                         Hwell_def_sitpn Heq_pl_fsm Hin_t_transs)
             in Hspec.
           contradiction.
        -- intros; reflexivity.
      + intros Hsens_fun.
        
        (* Specializes is_sensitized_no_error to solve the subgoal. *)
        explode_well_defined_sitpn.
        unfold NoUnknownPlaceInNeighbours in Hunk_pl_neigh.
        assert (Hincl_flat_lneigh : incl (flatten_neighbours (lneighbours sitpn t))
                                         (flatten_lneighbours sitpn (transs sitpn))).
        {
          intros p Hin_p_flat;
            apply (in_neigh_in_flatten t p Hwell_def_sitpn Hin_t_transs Hin_p_flat).
        }
        specialize (incl_tran Hincl_flat_lneigh Hunk_pl_neigh) as Hincl_fl_m.
        rewrite Heq_pl_fsm in Hincl_fl_m.

        specialize (is_sensitized_no_error sitpn marking t Hincl_fl_m)
          as Hsens_ex.
        inversion_clear Hsens_ex as (b & Hsens).
        rewrite Hsens_fun in Hsens; inversion Hsens.
  Qed.
  
End IsSensitized.

(** ** Lemmas about [in_list] function. *)

Section InList.

  Variable A : Type.
  
  Lemma in_list_correct :
    forall (eq_dec : forall x y : A, {x = y} + {x <> y})
           (l : list A)
           (a : A),
      in_list eq_dec l a = true -> In a l.
  Proof.
    intros eq_dec l a;
      functional induction (in_list eq_dec l a) using in_list_ind;
      intros Hfun.

    (* BASE CASE *)
    - inversion Hfun.

    (* CASE hd. *)
    - apply in_eq.

    (* CASE not hd. *)
    - apply in_cons.
      apply (IHb Hfun).
  Qed.

  Lemma not_in_list_correct :
    forall (eq_dec : forall x y : A, {x = y} + {x <> y})
           (l : list A)
           (a : A),
      in_list eq_dec l a = false -> ~In a l.
  Proof.
    intros eq_dec l a;
      functional induction (in_list eq_dec l a) using in_list_ind;
      intros Hfun.

    (* BASE CASE *)
    - intros Hin_nil; inversion Hin_nil.

    (* CASE hd. *)
    - inversion Hfun.

    (* CASE not hd. *)
    - rewrite not_in_cons.
      split; [auto | apply (IHb Hfun)].
  Qed.
      
End InList.

(** * Lemmas about [has_entered_time_window] and its spec. *)

Section HasEnteredTimeWindow.

  (** Correctness lemma for [has_entered_time_window]. *)
  Lemma has_entered_time_window_correct :
    forall (sitpn : Sitpn)
           (d_intervals : list (Trans * DynamicTimeInterval))
           (t : Trans),
      has_entered_time_window sitpn d_intervals t = Some true ->
      HasEnteredTimeWindow sitpn d_intervals t.
  Proof.
    intros sitpn d_intervals t;
      functional induction (has_entered_time_window sitpn d_intervals t)
                 using has_entered_time_window_ind;
      intro Hfun;
      unfold HasEnteredTimeWindow.

    (* CASE s_intervals = Some itval ∧ get_value t d_intervals = Some active min = 0. *)
    - right; exists _x0; apply (get_value_correct Nat.eq_dec t d_intervals e0). 

    (* CASE s_intervals = Some itval ∧ get_value t d_intervals = Some active min <> 0. *)
    - injection Hfun as Hfun; inversion Hfun.

    (* CASE s_intervals = Some itval ∧ get_value t d_intervals = blocked *)
    - injection Hfun as Hfun; inversion Hfun.

    (* ERROR CASE, get_value = None. *)
    - inversion Hfun.

    (* CASE s_intervals = None *)
    - left; assumption.
  Qed.

  (** Correctness lemma for has_entered_time_window = Some false. *)

  Lemma not_has_entered_time_window_correct :
    forall (sitpn : Sitpn)
           (d_intervals : list (Trans * DynamicTimeInterval))
           (t : Trans),
      NoDup (fst (split d_intervals)) ->
      has_entered_time_window sitpn d_intervals t = Some false ->
      ~HasEnteredTimeWindow sitpn d_intervals t.
  Proof.
    intros sitpn d_intervals t;
      functional induction (has_entered_time_window sitpn d_intervals t)
                 using has_entered_time_window_ind;
      intros Hnodup_fs_ditvals Hfun;
      unfold HasEnteredTimeWindow.

    (* CASE s_intervals = Some itval ∧ get_value t d_intervals = Some active min = 0. *)
    - injection Hfun as Heq_true_false; inversion Heq_true_false.

    (* CASE s_intervals = Some itval ∧ get_value t d_intervals = Some active min <> 0. *)
    - intro Hhas_entered_vee.
      inversion_clear Hhas_entered_vee as [Hs_itvals_none | Hex_active_0].

      (* Case s_intervals = None then contradiction. *)
      + rewrite e in Hs_itvals_none; inversion Hs_itvals_none.

      (* Case (t, active 0) ∈ ditvals, impossible as NoDup (fs ditvals) *)
      + specialize (get_value_correct Nat.eq_dec t d_intervals e0) as Hin_t_actS_ditvals.
        inversion_clear Hex_active_0 as (up_bound & Hin_t_act0_ditvals).

        contradiction_with_nodup_same_pair d_intervals
                                           (t, active {| min_t := S _x1; max_t := _x0 |})
                                           (t, active {| min_t := 0; max_t := up_bound |})
                                           Hin_t_actS_ditvals
                                           Hin_t_act0_ditvals.
                
    (* CASE s_intervals = Some itval ∧ get_value t d_intervals = blocked *)
    - intro Hhas_entered_vee.
      inversion_clear Hhas_entered_vee as [Hs_itvals_none | Hex_active_0].

      (* Case s_intervals = None then contradiction. *)
      + rewrite e in Hs_itvals_none; inversion Hs_itvals_none.

      (* Case (t, active 0) ∈ ditvals, impossible as NoDup (fs ditvals) *)
      + specialize (get_value_correct Nat.eq_dec t d_intervals e0) as Hin_t_actS_ditvals.
        inversion_clear Hex_active_0 as (up_bound & Hin_t_act0_ditvals).
        
        contradiction_with_nodup_same_pair d_intervals
                                           (t, blocked)
                                           (t, active {| min_t := 0; max_t := up_bound |})
                                           Hin_t_actS_ditvals
                                           Hin_t_act0_ditvals.
                
    (* ERROR CASE, get_value = None. *)
    - inversion Hfun.

    (* CASE s_intervals = None *)
    - injection Hfun as Hfun; inversion Hfun.
  Qed.
    
End HasEnteredTimeWindow.

(** * Lemmas about [are_all_conditions_true] and its spec. *)

Section AreAllConditionsTrue.

  Lemma are_all_conditions_true_correct :
    forall (sitpn : Sitpn)
           (cond_values : list (Condition * bool))
           (t : Trans),
      are_all_conditions_true sitpn cond_values t = true ->
      forall c : Condition,
        In c (fst (split cond_values)) ->
        has_condition sitpn t c = true ->
        In (c, true) cond_values.
  Proof.
    intros sitpn cond_values t;
      functional induction (are_all_conditions_true sitpn cond_values t)
                 using are_all_conditions_true_ind;
      intros Hfun c' Hin_fs_condv Hhas_cond.

    (* BASE CASE, cond_values = []. *)
    - inversion Hin_fs_condv.

    (* CASE has_condition = true and b = true. *)
    - rewrite fst_split_cons_app in Hin_fs_condv; simpl in Hin_fs_condv.
      inversion_clear Hin_fs_condv as [Heq_cc' | Hin_c'_tl].

      (* Case c = c'. *)
      + rewrite <- Heq_cc'; apply in_eq.

      (* Case c' ∈ tl *)
      + apply in_cons; apply (IHb Hfun c' Hin_c'_tl Hhas_cond).

    (* CASE has_condition = true and b = false *)
    - inversion Hfun.

    (* CASE has_condition = false *)
    - rewrite fst_split_cons_app in Hin_fs_condv; simpl in Hin_fs_condv.
      inversion_clear Hin_fs_condv as [Heq_cc' | Hin_c'_tl].

      (* Case c = c'. *)
      + rewrite <- Heq_cc' in Hhas_cond; rewrite e1 in Hhas_cond; inversion Hhas_cond.

      (* Case c' ∈ tl *)
      + apply in_cons; apply (IHb Hfun c' Hin_c'_tl Hhas_cond).
  Qed.

  (** Correctness lemma for are_all_conditions_true = false. *)
  
  Lemma not_are_all_conditions_true_correct :
    forall (sitpn : Sitpn)
           (cond_values : list (Condition * bool))
           (t : Trans),
      are_all_conditions_true sitpn cond_values t = false ->
      exists c : Condition,
        In c (fst (split cond_values)) /\
        has_condition sitpn t c = true /\
        In (c, false) cond_values.
  Proof.
    intros sitpn cond_values t;
      functional induction (are_all_conditions_true sitpn cond_values t)
                 using are_all_conditions_true_ind;
      intro Hfun;
      
      (* CASE b = true or has_cond c = false. *)
      (specialize (IHb Hfun) as Hex_cond;
       inversion_clear Hex_cond as (cond & Hw_cond);
       
       (* Instantiates c and prove each part of the conjunction. *)
       exists cond;
       repeat split; [apply proj1 in Hw_cond; rewrite fst_split_cons_app; apply in_cons; auto |
                      apply proj2 in Hw_cond; apply proj1 in Hw_cond; auto |
                      do 2 (apply proj2 in Hw_cond); apply in_cons; auto ])

       (* CASE has_cond c = true ∧ b = false *)
      || (exists c; repeat split; [rewrite fst_split_cons_app; apply in_eq | auto | apply in_eq ])

      (* BASE CASE *)
      || inversion Hfun.
  Qed.
  
End AreAllConditionsTrue.

(** * Lemmas about [sitpn_is_firable] and its spec. *)

Section SitpnIsFirable.

  (** A transition t is firable at state s' if it is
      firable at state s and if s and s' have same
      marking, dynamic intervals, and condition values,
      and conversely. *)

  Lemma sitpn_is_firable_iff_eq :
    forall (sitpn : Sitpn)
           (s s' : SitpnState)
           (t : Trans),
      (marking s) = (marking s') ->
      (d_intervals s) = (d_intervals s') ->
      (cond_values s) = (cond_values s') ->
      SitpnIsFirable sitpn s t <-> SitpnIsFirable sitpn s' t.
  Proof.
    intros sitpn s s' t Heq_m Heq_ditvals Heq_condv;
      split;
      intro His_fira;
      unfold SitpnIsFirable in *;
      rewrite <- Heq_ditvals, <- Heq_condv, <- Heq_m
      || rewrite Heq_ditvals, Heq_condv, Heq_m;                                      
      assumption.
  Qed.

  (** Correctness lemma for sitpn_is_firable. *)
  
  Lemma sitpn_is_firable_correct :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (t : Trans),
      IsWellDefinedSitpn sitpn ->
      IsWellDefinedSitpnState sitpn s ->
      In t (transs sitpn) ->
      sitpn_is_firable sitpn s (lneighbours sitpn t) t = Some true ->
      SitpnIsFirable sitpn s t.
  Proof.
    intros sitpn s t Hwell_def_sitpn Hwell_def_s
           Hin_t_transs Hfun;
      functional induction (sitpn_is_firable sitpn s (lneighbours sitpn t) t)
                 using sitpn_is_firable_ind;
      unfold SitpnIsFirable;

    (* GENERAL CASE, all went well. 

       We need to apply correctness lemmas is_sensitized,
       has_entered_time_window and are_all_conditions_true. *)
      (
        (* Builds premises and specializes is_sensitized_correct
         to get IsSensitized. *)
        explode_well_defined_sitpn_state Hwell_def_s;
        specialize (is_sensitized_correct (marking s) t Hwell_def_sitpn
                                          Hwf_state_marking Hin_t_transs e)
          as His_sens;

        (* Builds premises and specializes has_entered_time_window
         to get HasEnteredTimeWindow. *)
        specialize (has_entered_time_window_correct sitpn (d_intervals s) t e1)
          as Hhas_entered_time;

        (* Builds premises and specializes are_all_conditions_true 
         to get HasReachedAllConditions. *)
        injection Hfun as Hare_all_cond;
        specialize (are_all_conditions_true_correct sitpn (cond_values s) t Hare_all_cond)
          as Hhas_reached_all_cond;
        rewrite <- Hwf_state_condv in Hhas_reached_all_cond;

        (* Applies conjunctions of lemmas. *)
        apply (conj His_sens (conj Hhas_entered_time Hhas_reached_all_cond))
      )
        
      (* CASES true = false *)
      || (injection Hfun as Hfun; inversion Hfun) 

      (* ERROR CASES *)
      || inversion Hfun.      
  Qed.

  Lemma not_sitpn_is_firable_correct :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (t : Trans),
      IsWellDefinedSitpn sitpn ->
      IsWellDefinedSitpnState sitpn s ->
      In t (transs sitpn) ->
      sitpn_is_firable sitpn s (lneighbours sitpn t) t = Some false ->
      ~SitpnIsFirable sitpn s t.
  Proof.
    intros sitpn s t Hwell_def_sitpn Hwell_def_s Hin_t_transs;
      functional induction (sitpn_is_firable sitpn s (lneighbours sitpn t) t)
                 using sitpn_is_firable_ind;
      intros Hfun His_firable;
      unfold SitpnIsFirable in His_firable.

    (* CASE are_all_conditions_true = false. 
       
       Show that it is in contradiction with HasReacheAllConditions
       in SitpnIsFirable. *)
    
    - injection Hfun as Hare_all_cond_false.
      
      (* Gets ~HasReachedAllConditions, i.e: 
         ∃c, c ∈ conditions ∧ C(t, c) ∧ (c, false) ∈ cond_values. *)
      specialize (not_are_all_conditions_true_correct sitpn (cond_values s) t Hare_all_cond_false)
        as Hex_cond_false.

      (* Creates (c, false) ∈ cond_values has an independent hyp. in
         the context. *)
      inversion_clear Hex_cond_false as (c & Hcond_false).
      explode_well_defined_sitpn_state Hwell_def_s.
      rewrite <- Hwf_state_condv in Hcond_false.
      inversion_clear Hcond_false as (Hin_c_conds & Hw_cond_false);
        inversion_clear Hw_cond_false as (Hhas_cond_true & Hcond_false).

      (* Specializes HasReacheAllConditions in SitpnIsFirable to get
         (c, true) ∈ cond_values in the context. *)
      do 2 (apply proj2 in His_firable).
      unfold HasReachedAllConditions in His_firable.
      specialize (His_firable c Hin_c_conds Hhas_cond_true) as Hcond_true.

      (* Shows contradiction with (c, true) ∈ cond_values and
         (c, false) ∈ cond_values and NoDup (fs cond_values). *)
      explode_well_defined_sitpn.
      assert (Hnodup_condv := Hnodup_cond).
      unfold NoDupConditions in Hnodup_condv.
      rewrite Hwf_state_condv in Hnodup_condv.
      assert (Heq_fs_c : fst (c, true) = fst (c, false)) by auto.
      specialize (nodup_same_pair (cond_values s) Hnodup_condv (c, true) (c, false)
                                  Hcond_true Hcond_false Heq_fs_c)
        as Heq_pair_c.
      injection Heq_pair_c as Heq_true_false; inversion Heq_true_false.
      
    (* CASE has_entered_window = false. 
       
       Show that it is in contradiction with HasEnteredTimeWindow
       in SitpnIsFirable. *)
    - explode_well_defined_sitpn_state Hwell_def_s.
      specialize (not_has_entered_time_window_correct Hnodup_state_ditvals e1)
        as Hnot_has_entered.
      apply proj2 in His_firable; apply proj1 in His_firable.
      contradiction.

    (* ERROR CASE, has_entered_time_window = None *)
    - inversion Hfun.

    (* CASE is_sensitized = false. *)
    - (* Builds premises and specializes is_sensitized_correct
         to get IsSensitized. *)
        explode_well_defined_sitpn_state Hwell_def_s;
        specialize (not_is_sensitized_iff (marking s) t Hwell_def_sitpn
                                          Hwf_state_marking Hin_t_transs)
          as His_sens_eq.
        rewrite His_sens_eq in e.
        apply proj1 in His_firable.
        contradiction.

    (* ERROR CASE, is_sensitized = None *)
    - inversion Hfun.
  Qed.

End SitpnIsFirable.

(** * Lemmas on [modify_m] and its spec. *)

Section ModifyM.
  
  (** Correctness proof for [modify_m]. 
      
      Needed in update_marking_pre_aux_correct. *)
    Lemma modify_m_correct :
    forall (marking : list (Place * nat))
           (p : Place)
           (op : nat -> nat -> nat)
           (nboftokens : nat)
           (final_marking : list (Place * nat)),
      NoDup (fst (split marking)) ->
      modify_m marking p op nboftokens = Some final_marking ->
      forall n : nat, In (p, n) marking -> In (p, op n nboftokens) final_marking.
  Proof.
    intros marking p op nboftokens;
      functional induction (modify_m marking p op nboftokens) using modify_m_ind;
      intros final_marking Hnodup Hfun n' Hin_n'_m.
    
    (* ERROR CASE *)
    - inversion Hfun.
    
    (* INDUCTION CASE *)

    (* CASE p = hd. *)
    - inversion_clear Hin_n'_m as [Heq_pn'_p'n | Hin_pn'_tl].

      (* Case (p, n') = (p', n) *)
      + injection Heq_pn'_p'n as Heq_p'p Heqnn'.
        rewrite <- Heqnn';
          injection Hfun as Hfun;
          rewrite <- Hfun;
          apply in_eq.

      (* Case (p, n') ∈ tl *)
      + rewrite fst_split_cons_app in Hnodup.
        simpl in Hnodup.
        deduce_nodup_hd_not_in.
        apply in_fst_split in Hin_pn'_tl.
        rewrite (beq_nat_true p' p e1) in Hnot_in_tl.
        contradiction.

    (* CASE p <> hd ∧ rec = Some m'. *)
    - inversion_clear Hin_n'_m as [Heq_pn'_p'n | Hin_pn'_tl].

      (* Case (p, n') = (p', n) *)
      + injection Heq_pn'_p'n as Heq_p'p Heqnn'.
        apply beq_nat_false in e1.
        contradiction.

      (* Case (p, n') ∈ tl *)
      + rewrite fst_split_cons_app in Hnodup;
          simpl in Hnodup;
          rewrite NoDup_cons_iff in Hnodup;
          apply proj2 in Hnodup.
        injection Hfun as Hfun;
          rewrite <- Hfun;
          apply in_cons.
        apply (IHo m' Hnodup e2 n' Hin_pn'_tl). 

    (* ERROR CASE, rec = None *)
    - inversion Hfun.    
  Qed.

  Lemma modify_m_in_if_diff :
    forall (marking : list (Place * nat))
           (p : Place)
           (op : nat -> nat -> nat)
           (nboftokens : nat)
           (final_marking : list (Place * nat)),
      modify_m marking p op nboftokens = Some final_marking ->
      forall (p' : Place) (n : nat), p <> p' -> In (p', n) marking <-> In (p', n) final_marking.
  Proof.
    intros marking p op nboftokens;
      functional induction (modify_m marking p op nboftokens) using modify_m_ind;
      intros final_marking Hfun p'' n' Hdiff_pp.

    (* ERROR CASE *)
    - inversion Hfun.
    
    (* CASE p = hd *)
    - injection Hfun as Hfun.
      apply not_eq_sym in Hdiff_pp.
      specialize (fst_diff_pair_diff p'' p Hdiff_pp n' n) as Hdiff_nn0.
      specialize (fst_diff_pair_diff p'' p Hdiff_pp n' (op n nboftokens)) as Hdiff_nnb.
      split.
      
      + intros Hin_p''n'.
        inversion_clear Hin_p''n' as [Heq_p''n'_p'n | Hin_tl].

        -- symmetry in Heq_p''n'_p'n.
           rewrite (beq_nat_true p' p e1) in Heq_p''n'_p'n.
           contradiction.

        -- rewrite <- Hfun; apply in_cons; assumption.

      + intros Hin_p''n'_fm.
        rewrite <- Hfun in Hin_p''n'_fm.

        inversion_clear Hin_p''n'_fm as [Heq_p''n'_pop | Hin_tl].

        -- symmetry in Heq_p''n'_pop; contradiction.
        -- apply in_cons; assumption.

    (* CASE p <> hd ∧ rec = Some m' *)
    - injection Hfun as Hfun.
      split.

      + intros Hin_p''n'.
        inversion_clear Hin_p''n' as [Heq_p''n'_p'n | Hin_tl].

        -- rewrite <- Hfun;
             rewrite <- Heq_p''n'_p'n;
             apply in_eq.

        -- specialize (IHo m' e2 p'' n' Hdiff_pp)
            as Heq.
           rewrite <- Hfun; apply in_cons.
           rewrite <- Heq.
           assumption.
           
      + intros Hin_p''n'.
        rewrite <- Hfun in Hin_p''n'.
        inversion_clear Hin_p''n' as [Heq_p''n'_p'n | Hin_tl].

        -- rewrite <- Heq_p''n'_p'n;
             apply in_eq.

        -- specialize (IHo m' e2 p'' n' Hdiff_pp)
            as Heq.
           apply in_cons.
           rewrite Heq.
           assumption.
           
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** Proves that modify_m preserves the structure of the marking m
      passed as argument. *)
  
  Lemma modify_m_same_struct :
    forall (m : list (Place * nat))
           (p : Place)
           (op : nat -> nat -> nat)
           (nboftokens : nat)
           (m' : list (Place * nat)),
      modify_m m p op nboftokens = Some m' ->
      fst (split m) = fst (split m').
  Proof.
    intros m p op nboftokens;
      functional induction (modify_m m p op nboftokens)
                 using modify_m_ind;
      intros fm Hfun.

    (* ERROR CASE *)
    - inversion Hfun.

    (* CASE p = hd *)
    - rewrite (beq_nat_true p' p e1);
        injection Hfun as Hfun;
        rewrite <- Hfun.
      rewrite fst_split_cons_app;
        symmetry;
        rewrite fst_split_cons_app.
      simpl; reflexivity.

    (* CASE p <> hd ∧ rec = Some m' *)
    - injection Hfun as Hfun;
        rewrite <- Hfun.
      rewrite fst_split_cons_app;
        symmetry;
        rewrite fst_split_cons_app;
        simpl;
        specialize (IHo m' e2) as Heq_fs;
        rewrite Heq_fs;
        reflexivity.

    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** No error lemma for modify_m. *)

  Lemma modify_m_no_error :
    forall (m : list (Place * nat))
           (p : Place)
           (op : nat -> nat -> nat)
           (nboftokens : nat),
      In p (fst (split m)) ->
      exists m' : list (Place * nat),
        modify_m m p op nboftokens = Some m'.
  Proof.
    intros m p op nboftokens;
      functional induction (modify_m m p op nboftokens)
                 using modify_m_ind;
      intros Hin_p_fs.

    (* BASE CASE *)
    - simpl in Hin_p_fs; inversion Hin_p_fs.

    (* CASE p = hd *)
    - exists ((p, op n nboftokens) :: tl); reflexivity.


    (* CASE p <> hd ∧ rec = Some m' *)
    - exists ((p', n) :: m'); reflexivity.

    (* CASE p <> hd ∧ rec = None *)
    - rewrite fst_split_cons_app in Hin_p_fs; simpl in Hin_p_fs.
      inversion_clear Hin_p_fs as [Heq_p'p | Hin_p_fs_tl].

      + apply beq_nat_false in e1; contradiction.
      + specialize (IHo Hin_p_fs_tl) as Hex_modif.
        inversion_clear Hex_modif as (m' & Hmodif).
        rewrite e2 in Hmodif; inversion Hmodif.
  Qed.
  
End ModifyM.

(** Lemmas on update_marking_pre and update_marking_post functions, and  
 *  their mapped versions. *)

Section SitpnUpdateMarking.

  (** [update_marking_pre_aux] preserves marking structure. *)
  
  Lemma update_marking_pre_aux_same_marking :
    forall (sitpn : Sitpn)
           (m : list (Place * nat))
           (t : Trans)
           (pre_places : list Place)
           (m' : list (Place * nat)),
      update_marking_pre_aux sitpn m t pre_places = Some m' ->
       fst (split m) = fst (split m').
  Proof.
    intros sitpn m t pre_places;
      functional induction (update_marking_pre_aux sitpn m t pre_places)
                 using update_marking_pre_aux_ind;
      intros fm Hfun.
    (* BASE CASE *)
    - injection Hfun as Hfun; rewrite Hfun; reflexivity.
      
    (* GENERAL CASE *)
    - apply modify_m_same_struct in e0.
      specialize (IHo fm Hfun) as Hsame_struct.
      unfold MarkingHaveSameStruct in *.
      transitivity (fst (split m')); [assumption | assumption].
      
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** [update_marking_pre] preserves marking structure. *)
  
  Lemma update_marking_pre_same_marking :
    forall (sitpn : Sitpn)
           (m : list (Place * nat))
           (t : Trans)
           (m' : list (Place * nat)),
      update_marking_pre sitpn m (lneighbours sitpn t) t = Some m' ->
      fst (split m) = fst (split m').
  Proof.
    intros sitpn m t;
      functional induction (update_marking_pre sitpn m (lneighbours sitpn t) t) using update_marking_pre_ind;
      intros m' Hfun;
      unfold update_marking_pre in Hfun;
      apply update_marking_pre_aux_same_marking in Hfun;
      assumption.
  Qed.

  (** Needed to prove update_marking_pre_aux_correct. *)

  Lemma update_marking_pre_aux_not_in_pre_places :
    forall (sitpn : Sitpn)
           (m : list (Place * nat))
           (t : Trans)
           (pre_places : list Place)
           (m' : list (Place * nat)),
      update_marking_pre_aux sitpn m t pre_places = Some m' ->
      forall (p : Place),
        ~In p pre_places ->
        forall (n : nat), In (p, n) m <-> In (p, n) m'.
  Proof.
    intros sitpn m t pre_places;
      functional induction (update_marking_pre_aux sitpn m t pre_places)
                 using update_marking_pre_aux_ind;
      intros fm Hfun p' Hnot_in_pre n.
    (* BASE CASE *)
    - injection Hfun as Hfun.
      rewrite Hfun; reflexivity.
    (* GENERAL CASE *)
    - apply not_in_cons in Hnot_in_pre.
      elim Hnot_in_pre; intros Hdiff_pp' Hnot_in_tl.
      apply not_eq_sym in Hdiff_pp'.
      specialize (modify_m_in_if_diff
                    marking Nat.sub (pre sitpn t p)
                    e0 n Hdiff_pp') as Hequiv.
      rewrite Hequiv.
      apply (IHo fm Hfun p' Hnot_in_tl n).
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** Correctness proof for [update_marking_pre_aux].
    Express the structure of the returned [m'] regarding the structure
    of [m]. 

    Needed to prove update_marking_pre_correct. *)

  Lemma update_marking_pre_aux_correct :
    forall (sitpn : Sitpn)
           (m : list (Place * nat))
           (t : Trans)
           (pre_places : list Place)
           (m' : list (Place * nat)),
      IsWellDefinedSitpn sitpn ->
      NoDup (fst (split m)) ->
      NoDup pre_places ->
      incl pre_places (pre_pl (lneighbours sitpn t)) ->
      update_marking_pre_aux sitpn m t pre_places = Some m' ->
      forall (p : Place) (n : nat),
        In p pre_places ->
        In (p, n) m ->
        In (p, n - (pre sitpn t p)) m'.
  Proof.
    intros sitpn m t pre_places;
      functional induction (update_marking_pre_aux sitpn m t pre_places)
                 using update_marking_pre_aux_ind;
      intros fm Hwell_def_sitpn Hnodup_m
             Hnodup_pre_pl Hincl_pre_pl Hfun p' n Hin_pre_pl Hin_resid.
    
    (* BASE CASE, pre_places = []. *)
    - inversion Hin_pre_pl.
      
    (* GENERAL CASE *)
    - inversion Hin_pre_pl as [Heq_pp' | Hin_p'_tail].

      (* First subcase, p = p'. *)
      + rewrite <- Heq_pp' in Hin_pre_pl.
        rewrite <- Heq_pp' in Hin_resid.
        specialize (modify_m_correct
                      marking p Nat.sub (pre sitpn t p)
                      Hnodup_m e0 n Hin_resid) as Hin_resid'.
        apply NoDup_cons_iff in Hnodup_pre_pl.
        elim Hnodup_pre_pl; intros Hnot_in_tl Hnodup_tl.
        rewrite Heq_pp' in Hnot_in_tl.
        specialize (update_marking_pre_aux_not_in_pre_places
                      sitpn m' t tail
                      Hfun p' Hnot_in_tl (n - pre sitpn t p)) as Hin_equiv'.
        rewrite Heq_pp' in Hin_resid'.
        rewrite Heq_pp' in Hin_equiv'.
        rewrite Hin_equiv' in Hin_resid'; assumption.

      (* Second subcase, In p' tail, then apply induction hypothesis. *)
      (* But we need to show NoDup (fst (split residual')) first. *)
      + specialize (modify_m_same_struct
                      marking p Nat.sub  (pre sitpn t p) e0)
          as Hsame_struct.
        unfold MarkingHaveSameStruct in Hsame_struct.
        rewrite Hsame_struct in Hnodup_m.

        (* Builds the other hypotheses, needed to specialize IHo. *)
        apply NoDup_cons_iff in Hnodup_pre_pl;
          elim Hnodup_pre_pl;
          intros Hnot_in_tl Hnodup_tl.
        apply incl_cons_inv in Hincl_pre_pl.        

        (* Then specializes the induction hypothesis. *)
        specialize (IHo fm Hwell_def_sitpn Hnodup_m
                        Hnodup_tl Hincl_pre_pl Hfun
                        p' n Hin_p'_tail) as Himpl.
        specialize (not_in_in_diff p p' tail (conj Hnot_in_tl Hin_p'_tail))
          as Hdiff_pp.
        specialize (modify_m_in_if_diff
                      marking Nat.sub (pre sitpn t p)
                      e0 n Hdiff_pp) as Hequiv'.
        rewrite <- Hequiv' in Himpl.
        apply (Himpl Hin_resid).
        
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** No error lemma for update_marking_pre_aux. *)
  
  Lemma update_marking_pre_aux_no_error :
    forall (sitpn : Sitpn)
           (t : Trans)
           (pre_places : list Place)
           (m : list (Place * nat)),
      incl pre_places (fst (split m)) ->
      exists m' : list (Place * nat),
        update_marking_pre_aux sitpn m t pre_places = Some m'.
  Proof.
    intros sitpn t; induction pre_places; intros residual_marking Hincl_pre.
    (* BASE CASE *)
    - simpl; exists residual_marking; reflexivity.
    (* INDUCTION CASE *)
    - simpl.
      assert (Hin_eq : In a (a :: pre_places)) by apply in_eq.
      specialize (Hincl_pre a Hin_eq) as Hin_a_res.
      specialize (modify_m_no_error residual_marking a Nat.sub (pre sitpn t a) Hin_a_res)
        as Hmodify_ex.
      inversion_clear Hmodify_ex as (m' & Hmodify).
      rewrite Hmodify.
      apply incl_cons_inv in Hincl_pre.
      specialize (modify_m_same_struct residual_marking a Nat.sub (pre sitpn t a) Hmodify)
        as Hsame_struct.
      rewrite Hsame_struct in Hincl_pre.
      apply (IHpre_places m' Hincl_pre).
  Qed.

  (** Correctness proof for [update_marking_pre]. 

      Needed to prove GENERAL CASE in sitpn_fire_aux_sens_by_residual. *)
  
  Lemma update_marking_pre_correct :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans)
           (final_marking : list (Place * nat)),
      IsWellDefinedSitpn sitpn ->
      NoDup (fst (split marking)) ->
      In t (transs sitpn) ->
      update_marking_pre sitpn marking (lneighbours sitpn t) t = Some final_marking ->
      forall (p : Place) (n : nat),
        In (p, n) marking -> In (p, n - (pre sitpn t p)) final_marking.
  Proof.
    intros sitpn marking t;
      functional induction (update_marking_pre sitpn marking (lneighbours sitpn t) t)
                 using update_marking_pre_ind;
      intros final_marking Hwell_def_sitpn Hnodup_resm Hin_t_transs Hfun p n Hin_resm.

    (* GENERAL CASE *)
    - (* Two cases, either p ∈ (pre_pl neigh_of_t), or
       p ∉ (pre_pl neigh_of_t). *)
      assert (Hvee_in_pre_pl := classic (In p (pre_pl (lneighbours sitpn t)))).
      inversion_clear Hvee_in_pre_pl as [Hin_p_pre | Hnotin_p_pre].

      (* First case, p ∈ pre_pl, then applies update_marking_pre_aux_correct. *)
      + explode_well_defined_sitpn.

        (* Builds NoDup pre_pl. *)
        assert (Hin_flat : In p (flatten_neighbours (lneighbours sitpn t)))
          by (unfold flatten_neighbours; apply in_or_app; left; assumption).      
        unfold NoDupInNeighbours in Hnodup_neigh.
        specialize (Hnodup_neigh t Hin_t_transs) as Hnodup_flat.
        apply proj1 in Hnodup_flat;
          apply nodup_app in Hnodup_flat;
          apply proj1 in Hnodup_flat.

        (* Then, applies update_marking_pre_aux_correct. *)
        apply (update_marking_pre_aux_correct
                 marking t Hwell_def_sitpn Hnodup_resm Hnodup_flat
                 (incl_refl (pre_pl (lneighbours sitpn t))) Hfun p n Hin_p_pre Hin_resm).
        
      (* Second case, p ∉ pre_pl, then applies 
       update_marking_pre_aux_not_in_pre_places. *)
      + explode_well_defined_sitpn.
        unfold AreWellDefinedPreEdges in Hwell_def_pre.
        specialize (Hwell_def_pre t p Hin_t_transs) as Hw_pre_edges.
        apply proj2 in Hw_pre_edges; specialize (Hw_pre_edges Hnotin_p_pre).
        rewrite Hw_pre_edges; rewrite Nat.sub_0_r.
        specialize (update_marking_pre_aux_not_in_pre_places
                      sitpn marking t (pre_pl (lneighbours sitpn t))
                      Hfun p Hnotin_p_pre n) as Hequiv.
        rewrite <- Hequiv; assumption.
  Qed.

  (** No error lemma for [update_marking_pre]. *)
  
  Lemma update_marking_pre_no_error :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans),
      IsWellDefinedSitpn sitpn ->
      incl (flatten_neighbours (lneighbours sitpn t)) (fst (split marking)) ->
      exists final_marking : list (Place * nat),
        update_marking_pre sitpn marking (lneighbours sitpn t) t = Some final_marking.
  Proof.
    intros sitpn marking t Hwell_def_sitpn Hincl_flat.
    explode_well_defined_sitpn.
    unfold NoDupTranss in Hnodup_transs.
    unfold update_marking_pre.
    assert (Hincl_prepl : incl (pre_pl (lneighbours sitpn t)) (fst (split marking))).
    {
      intros x Hin_x_pre.
      apply or_introl
        with (B := In x ((test_pl (lneighbours sitpn t))
                           ++ (inhib_pl (lneighbours sitpn t))
                           ++ (post_pl (lneighbours sitpn t))))
        in Hin_x_pre.
      apply in_or_app in Hin_x_pre.
      apply (Hincl_flat x Hin_x_pre).
    }
    apply (update_marking_pre_aux_no_error sitpn t marking Hincl_prepl).
  Qed.

  (** [map_update_marking_pre] preserves marking structure. *)
  
  Lemma map_update_marking_pre_same_marking :
    forall (sitpn : Sitpn)
           (m : list (Place * nat))
           (fired : list Trans)
           (m' : list (Place * nat)),
      map_update_marking_pre sitpn m fired = Some m' ->
      MarkingHaveSameStruct m m'.
  Proof.
    intros sitpn m fired;
      functional induction (map_update_marking_pre sitpn m fired) using map_update_marking_pre_ind;
      intros fm Hfun.
    (* BASE CASE *)
    - injection Hfun as Hfun; rewrite Hfun; reflexivity.
    (* GENERAL CASE *)
    - apply update_marking_pre_same_marking in e0.
      specialize (IHo fm Hfun) as Hsame_struct.
      unfold MarkingHaveSameStruct in *.
      transitivity (fst (split m')); [assumption | assumption].
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** 
   * Correctness lemma for [map_update_marking_pre].
   * 
   * map_update_marking_pre sitpn m fired = m' ⇒ m' = m - ∑ pre(t), ∀ t ∈ fired
   * 
   * [map_update_marking_pre] substracts tokens in the pre-places 
   *  of all transitions ∈ fired. 
   *  
   *)
  
  Lemma map_update_marking_pre_sub_pre :
    forall (sitpn : Sitpn)
           (m : list (Place * nat))
           (fired : list Trans)
           (m' : list (Place * nat)),
      IsWellDefinedSitpn sitpn ->
      NoDup (fst (split m)) ->
      incl fired (transs sitpn) ->
      map_update_marking_pre sitpn m fired = Some m' ->
      forall (p : Place) (n : nat),
        In (p, n) m -> In (p, n - pre_sum sitpn p fired) m'.
  Proof.
    intros sitpn m fired;
      functional induction (map_update_marking_pre sitpn m fired) using map_update_marking_pre_ind;
      intros fm Hwell_def_sitpn Hnodup_m Hincl_transs Hfun p n Hin_m.
    
    (* BASE CASE *)
    - injection Hfun as Heq_marking; rewrite <- Heq_marking.
      simpl; rewrite Nat.sub_0_r; assumption.
      
    (* GENERAL CASE *)
    - specialize (Hincl_transs t (in_eq t tail)) as Hin_t_transs. 
      simpl. 
      rewrite Nat.sub_add_distr.
      specialize (update_marking_pre_correct
                    marking t Hwell_def_sitpn Hnodup_m Hin_t_transs e0 p n Hin_m) as Hin_m'.
      apply update_marking_pre_same_marking in e0;
        unfold MarkingHaveSameStruct in e0;
        rewrite e0 in Hnodup_m.
      apply (IHo fm Hwell_def_sitpn Hnodup_m (incl_cons_inv t tail (transs sitpn) Hincl_transs)
                 Hfun p (n - pre sitpn t p) Hin_m').

    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** No error lemma for [map_update_marking_pre]. *)

  Lemma map_update_marking_pre_no_error :
    forall (sitpn : Sitpn)
           (fired : list Trans)
           (m : list (Place * nat)),
      IsWellDefinedSitpn sitpn ->
      (forall (t : Trans),
          In t fired ->
          incl (flatten_neighbours (lneighbours sitpn t)) (fst (split m))) ->
      exists m' : list (Place * nat),
        map_update_marking_pre sitpn m fired = Some m'.
  Proof.
    intros sitpn; induction fired; intros m Hwell_def_sitpn Hincl_fl_m.

    (* BASE CASE *)
    - simpl; exists m; reflexivity.

    (* INDUCTION CASE *)
    - simpl.
      assert (Hin_eq : In a (a :: fired)) by apply in_eq.
      specialize (Hincl_fl_m a Hin_eq) as Hincl_flat.
      specialize (update_marking_pre_no_error
                    m a Hwell_def_sitpn Hincl_flat)
        as Hupdate_pre_ex.
      inversion_clear Hupdate_pre_ex as ( final_marking & Hupdate_pre ).
      rewrite Hupdate_pre.
      specialize (update_marking_pre_same_marking sitpn m a Hupdate_pre)
        as Hsame_struct.
      rewrite Hsame_struct in Hincl_fl_m.
      assert (Hincl_fl_tl :
                forall t : Trans,
                  In t fired ->
                  incl (flatten_neighbours (lneighbours sitpn t)) (fst (split final_marking))).
      {
        intros t Hin_t_fired;
          apply (in_cons a) in Hin_t_fired;
          apply (Hincl_fl_m t Hin_t_fired).
      }
      apply (IHfired final_marking Hwell_def_sitpn Hincl_fl_tl).
  Qed.  

    (** [update_marking_post_aux] postserves marking structure. *)
  
  Lemma update_marking_post_aux_same_marking :
    forall (sitpn : Sitpn)
           (m : list (Place * nat))
           (t : Trans)
           (post_places : list Place)
           (m' : list (Place * nat)),
      update_marking_post_aux sitpn m t post_places = Some m' ->
       fst (split m) = fst (split m').
  Proof.
    intros sitpn m t post_places;
      functional induction (update_marking_post_aux sitpn m t post_places)
                 using update_marking_post_aux_ind;
      intros fm Hfun.
    (* BASE CASE *)
    - injection Hfun as Hfun; rewrite Hfun; reflexivity.
      
    (* GENERAL CASE *)
    - apply modify_m_same_struct in e0.
      specialize (IHo fm Hfun) as Hsame_struct.
      unfold MarkingHaveSameStruct in *.
      transitivity (fst (split m')); [assumption | assumption].
      
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** [update_marking_post] postserves marking structure. *)
  
  Lemma update_marking_post_same_marking :
    forall (sitpn : Sitpn)
           (m : list (Place * nat))
           (t : Trans)
           (m' : list (Place * nat)),
      update_marking_post sitpn m (lneighbours sitpn t) t = Some m' ->
      fst (split m) = fst (split m').
  Proof.
    intros sitpn m t;
      functional induction (update_marking_post sitpn m (lneighbours sitpn t) t) using update_marking_post_ind;
      intros m' Hfun;
      unfold update_marking_post in Hfun;
      apply update_marking_post_aux_same_marking in Hfun;
      assumption.
  Qed.

  (** Needed to prove update_marking_post_aux_correct. *)

  Lemma update_marking_post_aux_not_in_post_places :
    forall (sitpn : Sitpn)
           (m : list (Place * nat))
           (t : Trans)
           (post_places : list Place)
           (m' : list (Place * nat)),
      update_marking_post_aux sitpn m t post_places = Some m' ->
      forall (p : Place),
        ~In p post_places ->
        forall (n : nat), In (p, n) m <-> In (p, n) m'.
  Proof.
    intros sitpn m t post_places;
      functional induction (update_marking_post_aux sitpn m t post_places)
                 using update_marking_post_aux_ind;
      intros fm Hfun p' Hnot_in_post n.
    (* BASE CASE *)
    - injection Hfun as Hfun.
      rewrite Hfun; reflexivity.
    (* GENERAL CASE *)
    - apply not_in_cons in Hnot_in_post.
      elim Hnot_in_post; intros Hdiff_pp' Hnot_in_tl.
      apply not_eq_sym in Hdiff_pp'.
      specialize (modify_m_in_if_diff
                    marking Nat.add (post sitpn t p)
                    e0 n Hdiff_pp') as Hequiv.
      rewrite Hequiv.
      apply (IHo fm Hfun p' Hnot_in_tl n).

    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** Correctness proof for [update_marking_post_aux].
    Expostss the structure of the returned [m'] regarding the structure
    of [m]. 

    Needed to prove update_marking_post_correct. *)

  Lemma update_marking_post_aux_correct :
    forall (sitpn : Sitpn)
           (m : list (Place * nat))
           (t : Trans)
           (post_places : list Place)
           (m' : list (Place * nat)),
      IsWellDefinedSitpn sitpn ->
      NoDup (fst (split m)) ->
      NoDup post_places ->
      incl post_places (post_pl (lneighbours sitpn t)) ->
      update_marking_post_aux sitpn m t post_places = Some m' ->
      forall (p : Place) (n : nat),
        In p post_places ->
        In (p, n) m ->
        In (p, n + (post sitpn t p)) m'.
  Proof.
    intros sitpn m t post_places;
      functional induction (update_marking_post_aux sitpn m t post_places)
                 using update_marking_post_aux_ind;
      intros fm Hwell_def_sitpn Hnodup_m
             Hnodup_post_pl Hincl_post_pl Hfun p' n Hin_post_pl Hin_resid.
    
    (* BASE CASE, post_places = []. *)
    - inversion Hin_post_pl.
      
    (* GENERAL CASE *)
    - inversion Hin_post_pl as [Heq_pp' | Hin_p'_tail].

      (* First subcase, p = p'. *)
      + rewrite <- Heq_pp' in Hin_post_pl.
        rewrite <- Heq_pp' in Hin_resid.
        specialize (modify_m_correct
                      marking p Nat.add (post sitpn t p)
                      Hnodup_m e0 n Hin_resid) as Hin_resid'.
        apply NoDup_cons_iff in Hnodup_post_pl.
        elim Hnodup_post_pl; intros Hnot_in_tl Hnodup_tl.
        rewrite Heq_pp' in Hnot_in_tl.
        specialize (update_marking_post_aux_not_in_post_places
                      sitpn m' t tail
                      Hfun p' Hnot_in_tl (n + post sitpn t p)) as Hin_equiv'.
        rewrite Heq_pp' in Hin_resid'.
        rewrite Heq_pp' in Hin_equiv'.
        rewrite Hin_equiv' in Hin_resid'; assumption.

      (* Second subcase, In p' tail, then apply induction hypothesis. *)
      (* But we need to show NoDup (fst (split residual')) first. *)
      + specialize (modify_m_same_struct
                      marking p Nat.add (post sitpn t p) e0)
          as Hsame_struct.
        unfold MarkingHaveSameStruct in Hsame_struct.
        rewrite Hsame_struct in Hnodup_m.

        (* Builds the other hypotheses, needed to specialize IHo. *)
        apply NoDup_cons_iff in Hnodup_post_pl;
          elim Hnodup_post_pl;
          intros Hnot_in_tl Hnodup_tl.
        apply incl_cons_inv in Hincl_post_pl.        

        (* Then specializes the induction hypothesis. *)
        specialize (IHo fm Hwell_def_sitpn Hnodup_m
                        Hnodup_tl Hincl_post_pl Hfun
                        p' n Hin_p'_tail) as Himpl.
        specialize (not_in_in_diff p p' tail (conj Hnot_in_tl Hin_p'_tail))
          as Hdiff_pp.
        specialize (modify_m_in_if_diff
                      marking Nat.add (post sitpn t p)
                      e0 n Hdiff_pp) as Hequiv'.
        rewrite <- Hequiv' in Himpl.
        apply (Himpl Hin_resid).
        
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** No error lemma for update_marking_post_aux. *)
  
  Lemma update_marking_post_aux_no_error :
    forall (sitpn : Sitpn)
           (t : Trans)
           (post_places : list Place)
           (m : list (Place * nat)),
      incl post_places (fst (split m)) ->
      exists m' : list (Place * nat),
        update_marking_post_aux sitpn m t post_places = Some m'.
  Proof.
    intros sitpn t; induction post_places; intros residual_marking Hincl_post.
    (* BASE CASE *)
    - simpl; exists residual_marking; reflexivity.
    (* INDUCTION CASE *)
    - simpl.
      assert (Hin_eq : In a (a :: post_places)) by apply in_eq.
      specialize (Hincl_post a Hin_eq) as Hin_a_res.
      specialize (modify_m_no_error residual_marking a Nat.add (post sitpn t a) Hin_a_res)
        as Hmodify_ex.
      inversion_clear Hmodify_ex as (m' & Hmodify).
      rewrite Hmodify.
      apply incl_cons_inv in Hincl_post.
      specialize (modify_m_same_struct residual_marking a Nat.add (post sitpn t a) Hmodify)
        as Hsame_struct.
      rewrite Hsame_struct in Hincl_post.
      apply (IHpost_places m' Hincl_post).
  Qed.

  (** Correctness proof for [update_marking_post]. 

      Needed to prove GENERAL CASE in sitpn_fire_aux_sens_by_residual. *)
  
  Lemma update_marking_post_correct :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans)
           (final_marking : list (Place * nat)),
      IsWellDefinedSitpn sitpn ->
      NoDup (fst (split marking)) ->
      In t (transs sitpn) ->
      update_marking_post sitpn marking (lneighbours sitpn t) t = Some final_marking ->
      forall (p : Place) (n : nat),
        In (p, n) marking -> In (p, n + (post sitpn t p)) final_marking.
  Proof.
    intros sitpn marking t;
      functional induction (update_marking_post sitpn marking (lneighbours sitpn t) t)
                 using update_marking_post_ind;
      intros final_marking Hwell_def_sitpn Hnodup_resm Hin_t_transs Hfun p n Hin_resm.

    (* GENERAL CASE *)
    - (* Two cases, either p ∈ (post_pl neigh_of_t), or
       p ∉ (post_pl neigh_of_t). *)
      assert (Hvee_in_post_pl := classic (In p (post_pl (lneighbours sitpn t)))).
      inversion_clear Hvee_in_post_pl as [Hin_p_post | Hnotin_p_post].

      (* First case, p ∈ post_pl, then applies update_marking_post_aux_correct. *)
      + explode_well_defined_sitpn.

        (* Builds NoDup post_pl. *)
        assert (Hin_flat : In p (flatten_neighbours (lneighbours sitpn t)))
          by (unfold flatten_neighbours; do 3 (apply in_or_app; right); assumption).      
        unfold NoDupInNeighbours in Hnodup_neigh.
        specialize (Hnodup_neigh t Hin_t_transs) as Hnodup_flat.
        apply proj2 in Hnodup_flat.

        (* Then, applies update_marking_post_aux_correct. *)
        apply (update_marking_post_aux_correct
                 marking t Hwell_def_sitpn Hnodup_resm Hnodup_flat
                 (incl_refl (post_pl (lneighbours sitpn t))) Hfun p n Hin_p_post Hin_resm).
        
      (* Second case, p ∉ post_pl, then applies 
       update_marking_post_aux_not_in_post_places. *)
      + explode_well_defined_sitpn.
        unfold AreWellDefinedPostEdges in Hwell_def_post.
        specialize (Hwell_def_post t p Hin_t_transs) as Hw_post_edges.
        apply proj2 in Hw_post_edges; specialize (Hw_post_edges Hnotin_p_post).
        rewrite Hw_post_edges. rewrite <- plus_n_O.
        specialize (update_marking_post_aux_not_in_post_places
                      sitpn marking t (post_pl (lneighbours sitpn t))
                      Hfun p Hnotin_p_post n) as Hequiv.
        rewrite <- Hequiv; assumption.
  Qed.

  (** No error lemma for [update_marking_post]. *)
  
  Lemma update_marking_post_no_error :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans),
      IsWellDefinedSitpn sitpn ->
      incl (flatten_neighbours (lneighbours sitpn t)) (fst (split marking)) ->
      exists final_marking : list (Place * nat),
        update_marking_post sitpn marking (lneighbours sitpn t) t = Some final_marking.
  Proof.
    intros sitpn marking t Hwell_def_sitpn Hincl_flat.
    explode_well_defined_sitpn.
    unfold NoDupTranss in Hnodup_transs.
    unfold update_marking_post.
    assert (Hincl_postpl : incl (post_pl (lneighbours sitpn t)) (fst (split marking))).
    {
      intros x Hin_x_post.
      apply or_intror
        with (A := In x (pre_pl (lneighbours sitpn t) ++ test_pl (lneighbours sitpn t) ++ inhib_pl (lneighbours sitpn t)))
        in Hin_x_post.
      apply in_or_app in Hin_x_post.
      rewrite <- app_assoc in Hin_x_post.
      rewrite <- app_assoc in Hin_x_post.
      apply (Hincl_flat x Hin_x_post).
    }
    apply (update_marking_post_aux_no_error sitpn t marking Hincl_postpl).
  Qed.

  (** [map_update_marking_post] postserves marking structure. *)
  
  Lemma map_update_marking_post_same_marking :
    forall (sitpn : Sitpn)
           (m : list (Place * nat))
           (fired : list Trans)
           (m' : list (Place * nat)),
      map_update_marking_post sitpn m fired = Some m' ->
      MarkingHaveSameStruct m m'.
  Proof.
    intros sitpn m fired;
      functional induction (map_update_marking_post sitpn m fired) using map_update_marking_post_ind;
      intros fm Hfun.
    (* BASE CASE *)
    - injection Hfun as Hfun; rewrite Hfun; reflexivity.
    (* GENERAL CASE *)
    - apply update_marking_post_same_marking in e0.
      specialize (IHo fm Hfun) as Hsame_struct.
      unfold MarkingHaveSameStruct in *.
      transitivity (fst (split m')); [assumption | assumption].
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** 
   * Correctness lemma for [map_update_marking_post].
   * 
   * map_update_marking_post sitpn m fired = m' ⇒ m' = m - ∑ post(t), ∀ t ∈ fired
   * 
   * [map_update_marking_post] substracts tokens in the post-places 
   *  of all transitions ∈ fired. 
   *  
   *)
  
  Lemma map_update_marking_post_add_post :
    forall (sitpn : Sitpn)
           (m : list (Place * nat))
           (fired : list Trans)
           (m' : list (Place * nat)),
      IsWellDefinedSitpn sitpn ->
      NoDup (fst (split m)) ->
      incl fired (transs sitpn) ->
      map_update_marking_post sitpn m fired = Some m' ->
      forall (p : Place) (n : nat),
        In (p, n) m -> In (p, n + post_sum sitpn p fired) m'.
  Proof.
    intros sitpn m fired;
      functional induction (map_update_marking_post sitpn m fired) using map_update_marking_post_ind;
      intros fm Hwell_def_sitpn Hnodup_m Hincl_transs Hfun p n Hin_m.
    
    (* BASE CASE *)
    - injection Hfun as Heq_marking; rewrite <- Heq_marking.
      simpl; rewrite <- (plus_n_O n); assumption.
      
    (* GENERAL CASE *)
    - specialize (Hincl_transs t (in_eq t tail)) as Hin_t_transs. 
      simpl.
      rewrite <- plus_assoc_reverse.
      specialize (update_marking_post_correct
                    marking t Hwell_def_sitpn Hnodup_m Hin_t_transs e0 p n Hin_m) as Hin_m'.
      apply update_marking_post_same_marking in e0;
        unfold MarkingHaveSameStruct in e0;
        rewrite e0 in Hnodup_m.
      apply (IHo fm Hwell_def_sitpn Hnodup_m (incl_cons_inv t tail (transs sitpn) Hincl_transs)
                 Hfun p (n + post sitpn t p) Hin_m').

    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** No error lemma for [map_update_marking_post]. *)

  Lemma map_update_marking_post_no_error :
    forall (sitpn : Sitpn)
           (fired : list Trans)
           (m : list (Place * nat)),
      IsWellDefinedSitpn sitpn ->
      (forall (t : Trans),
          In t fired ->
          incl (flatten_neighbours (lneighbours sitpn t)) (fst (split m))) ->
      exists m' : list (Place * nat),
        map_update_marking_post sitpn m fired = Some m'.
  Proof.
    intros sitpn; induction fired; intros m Hwell_def_sitpn Hincl_fl_m.

    (* BASE CASE *)
    - simpl; exists m; reflexivity.

    (* INDUCTION CASE *)
    - simpl.
      assert (Hin_eq : In a (a :: fired)) by apply in_eq.
      specialize (Hincl_fl_m a Hin_eq) as Hincl_flat.
      specialize (update_marking_post_no_error
                    m a Hwell_def_sitpn Hincl_flat)
        as Hupdate_post_ex.
      inversion_clear Hupdate_post_ex as ( final_marking & Hupdate_post ).
      rewrite Hupdate_post.
      specialize (update_marking_post_same_marking sitpn m a Hupdate_post)
        as Hsame_struct.
      rewrite Hsame_struct in Hincl_fl_m.
      assert (Hincl_fl_tl :
                forall t : Trans,
                  In t fired ->
                  incl (flatten_neighbours (lneighbours sitpn t)) (fst (split final_marking))).
      {
        intros t Hin_t_fired;
          apply (in_cons a) in Hin_t_fired;
          apply (Hincl_fl_m t Hin_t_fired).
      }
      apply (IHfired final_marking Hwell_def_sitpn Hincl_fl_tl).
  Qed.  
  
End SitpnUpdateMarking.
