(** In this file are recorded all lemmas that are using
    tactics defined in the 'HilecopTactics' file.
    
    This is a way to avoid cyclic dependency between
    'HilecopLemmas' and 'HilecopTactics'. 
 *)

Require Import Hilecop.Utils.HilecopLemmas.
Require Import Hilecop.Utils.HilecopTactics.
Require Import Hilecop.Utils.HilecopDefinitions.
Require Import Permutation.

(** Proves the equivalence between to list 
    of couples l' and l'', with some hypotheses
    on these two lists.
 *)

Lemma eq_if_eq_fs {A B : Type} :
  forall (l l' l'' : list (A * B)),
    (forall (a : A)
            (b : B),
        In (a, b) l -> exists (b' : B), In (a, b') l' /\ In (a, b') l'') ->
    fst (split l) = fst (split l') ->
    fst (split l) = fst (split l'') ->
    NoDup (fst (split l)) ->
    NoDup (fst (split l')) ->
    NoDup (fst (split l'')) ->
    forall (x : A) (y : B), In (x, y) l' <-> In (x, y) l''.
Proof.
  intros l l' l'' Hin_l_in_ll Heq_fs_ll' Heq_fs_ll''
         Hnodup_l Hnodup_l' Hnodup_l'' x y.

  (* Proves both side of the implication. *)
  split;
    let deduce_goal list Heq_fs_list := 
        (intros Hin_xy_list;
         specialize (in_fst_split x y list Hin_xy_list) as Hin_x_fs_list;
         rewrite <- Heq_fs_list in Hin_x_fs_list;
         apply (in_fst_split_in_pair x l) in Hin_x_fs_list;
         inversion_clear Hin_x_fs_list as (z & Hin_xz_l);
         specialize (Hin_l_in_ll x z Hin_xz_l) as Hex_in_ll;
         inversion_clear Hex_in_ll as (c & Hw_in_xc_ll);
         inversion_clear Hw_in_xc_ll as (Hin_xc_list & Hin_xc_list');
         apply_nodup_same_pair;
         injection Heq_pairs as Heq_yc;
         rewrite Heq_yc;
         assumption) in
    (deduce_goal l' Heq_fs_ll' || deduce_goal l'' Heq_fs_ll'').
Qed.

(** Proves the equivalence between to list 
    of couples m and n, with some hypotheses
    on these two lists.
 *)

Lemma equiv_if_perm_and_nodup_fs {A B : Type} :
  forall (l m n : list (A * B)),
    (forall (a : A)
            (b : B),
        In (a, b) l -> exists (b' : B), In (a, b') m /\ In (a, b') n) ->
    Permutation (fs l) (fs m) ->
    Permutation (fs l) (fs n) ->
    NoDup (fs l) ->
    NoDup (fs m) ->
    NoDup (fs n) ->
    forall (x : A) (y : B), In (x, y) m <-> In (x, y) n.
Proof.
  intros l m n Hin_l_in_mn Hperm_fs_lm Hperm_fs_ln
         Hnodup_l Hnodup_m Hnodup_n x y.
  
  (* Proves both side of the implication. *)
  split;
    let deduce_goal list Heq_fs_list := 
        (intros Hin_xy_list;
         specialize (in_fst_split x y list Hin_xy_list) as Hin_x_fs_list;
         rewrite <- Heq_fs_list in Hin_x_fs_list;
         apply (in_fst_split_in_pair x l) in Hin_x_fs_list;
         inversion_clear Hin_x_fs_list as (z & Hin_xz_l);
         specialize (Hin_l_in_mn x z Hin_xz_l) as Hex_in_ll;
         inversion_clear Hex_in_ll as (c & Hw_in_xc_ll);
         inversion_clear Hw_in_xc_ll as (Hin_xc_list & Hin_xc_list');
         unfold fs in *;
         apply_nodup_same_pair;
         injection Heq_pairs as Heq_yc;
         rewrite Heq_yc;
         assumption) in
    (deduce_goal m Hperm_fs_lm || deduce_goal n Hperm_fs_ln).
Qed.
