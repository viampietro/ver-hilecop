(** * Facts about the Sitpn Semantics  *)

Require Import Sitpn.
Require Import SitpnSemanticsDefs.

Lemma PInputsOf_ex : forall sitpn (t : T sitpn), exists pinputs_of_t, PInputsOf t pinputs_of_t.
  intros sitpn t; unfold PInputsOf.
Admitted.

Lemma TOutputsOf_ex : forall sitpn (p : P sitpn), exists toutputs_of_p, TOutputsOf p toutputs_of_p.
Admitted.

