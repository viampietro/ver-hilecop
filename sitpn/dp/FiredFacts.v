(** * Facts about the [Fired] Predicate *)

Require Import common.Coqlib.
Require Import common.InAndNoDup.
Require Import dp.Sitpn.
Require Import dp.Fired.

(** ** Facts about the [IsTopPriorityList] predicate *)

Lemma is_top_prio_in_acc :
  forall sitpn (lofT : list (T sitpn)) tp tp',
    IsTopPriorityListAux lofT tp tp' ->
    forall t, List.In t tp -> List.In t tp'.
Proof.
  induction 1; firstorder.
Defined.

Lemma is_top_prio_diff_v :
  forall sitpn (lofT : list (T sitpn)) tp tp',
    IsTopPriorityListAux lofT tp tp' ->
    forall lofT' t,
      IsDiff lofT tp' lofT' ->
      List.In t lofT ->
      List.In t lofT' \/ List.In t tp'.
Proof.
  induction 1.

  - inversion 2.
  - intros.
      lazymatch goal with
      | [ H: List.In _ (_ :: _) |- _ ] =>
        inversion_clear H as [Heq | Hin]
      end.
      
    + right;
        rewrite Heq in *;
        lazymatch goal with
        | [ H: IsTopPriorityListAux _ (tp ++ [?t]) _ |- _ ] =>
          apply (is_top_prio_in_acc sitpn lofT (tp ++ [t]) tp' H t (in_last t tp))
        end.

    + unfold IsDiff in *. admit.
      
  - admit.
Admitted.

(** ** Facts about the [ElectFired] predicate *)

Lemma elect_fired_in_acc :
    forall sitpn s m fired lofT m' fired',
      @ElectFired sitpn s m fired lofT (m', fired') ->
      forall t, List.In t fired -> List.In t fired'.
Proof.
  intros *; intros Helectf.

  dependent induction Helectf.

  - auto.
  - specialize (IHHelectf m' fired' eq_refl); intros; apply IHHelectf.
    apply in_or_app; left; assumption.
  - eapply IHHelectf; eauto.
Qed.
