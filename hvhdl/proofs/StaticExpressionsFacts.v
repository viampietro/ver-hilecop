(** * Facts about Static Expressions *)

Require Import hvhdl.Environment.
Require Import hvhdl.StaticExpressions.
Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.SemanticalDomains.

(** ** Facts about Locally Static Expressions *)

Section LStatic.

End LStatic.

(** ** Facts about Globally Static Expressions *)

Section GStatic.

  Lemma is_gstatic_expr_eq_iff_eq_gens :
    forall {Δ1 Δ2 e},
      EqGens Δ1 Δ2 ->
      is_gstatic_expr Δ1 e <->
      is_gstatic_expr Δ2 e.
  Proof.
    split.
    (* CASE A -> B *)
    - induction 1; eauto with hvhdl.
      eapply IsGStaticGeneric with (t := t) (v := v);
        rewrite <- H; assumption.
    (* CASE B -> A *)
    - induction 1; eauto with hvhdl.
      eapply IsGStaticGeneric with (t := t) (v := v);
        rewrite H; assumption.
  Qed.
  
End GStatic.
