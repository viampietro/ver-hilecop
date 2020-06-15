(** * Facts about the simulation relations *)

Require Import Simulation.

(** Every source and target states verifying the [simloop] relation at
    time 0 are equal. *)

Lemma simloop_eqstate_at_0 :
  forall Ep ed dstate cstmt dstate',
    simloop Ep ed dstate cstmt 0 dstate' -> dstate = dstate'.
Proof.
  inversion 1;
  [ match goal with | [ H: 0 > 0 |- _ ] => inversion H end | auto ].
Qed.

(** Adds the premises of [simloop] in hypotheses when tau is greater
    than 0. *)

Lemma simloop_tau_gt0 :
  forall Ep ed dstate cstmt dstate'' tau,
    tau > 0 ->
    simloop Ep ed dstate cstmt tau dstate'' ->
    exists dstate',
      simcycle Ep ed tau dstate cstmt dstate' /\
      simloop Ep ed dstate' cstmt (tau - 1) dstate''.
Proof.
  intros *; intros Htau_gt0 Hsim; inversion Hsim.
  - match goal with
    | [
      Hcyc: simcycle _ _ _ _ _ dstate',
      Hsimloop: simloop _ _ _ _ _ _                  
      |- _ ] =>
      exists dstate'; apply (conj Hcyc Hsimloop)
    end.
  - match goal with
    | [ Htau: 0 = tau, Htau_gt0: tau > 0 |- _ ] =>
      rewrite <- Htau in Htau_gt0; inversion Htau_gt0
    end.
Qed.
