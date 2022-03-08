(** * Facts about the Sitpn Semantics  *)

Require Import common.CoqLib.
Require Import common.ListLib.
Require Import common.GlobalFacts.
Require Import sitpn.Sitpn.
Require Import sitpn.SitpnSemanticsDefs.
Require Import sitpn.SitpnFacts.

Lemma PInputsOf_ex : forall sitpn (t : T sitpn), exists pinputs_of_t, PInputsOf t pinputs_of_t.
  intros sitpn t; unfold PInputsOf.
Admitted.

Lemma TOutputsOf_ex : forall sitpn (p : P sitpn), exists toutputs_of_p, TOutputsOf p toutputs_of_p.
Admitted.

Lemma NoDup_tfilter :
  forall {A B : Type} (l : list A) (f : { a : A | List.In a l } -> bool)
         (InA2sigInA : forall a : A, List.In a l -> { a : A | List.In a l }),
    List.NoDup l -> SetoidList.NoDupA P1SigEq (tfilter f l InA2sigInA).
Admitted.

Lemma pinputs_correct :
  forall sitpn (t : T sitpn) inputs_of_t,
    pinputs t = inputs_of_t -> PInputsOf t inputs_of_t.
Proof.
  intros * EQ. 
  unfold PInputsOf. unfold Set_in_ListA.
  split.
  2: { rewrite <- EQ; eapply NoDup_tfilter; exact (nodup_pls sitpn). }
Admitted.

