(** * Tactics for Sitpn Instances *)

(** ** Proof of decidability for a priority relation *)

Ltac decide_prio_dec_aux :=
  lazymatch goal with
  | [ H: _ |- {match ?a with _ => _ end} + {~match ?a with _ => _ end}] =>
    case a; decide_prio_dec_aux
  | [ H: _ |- forall n, _ ] =>
    let id := fresh in intros id; decide_prio_dec_aux
  | [ H: _ |- {False} + {~False} ] => right; intros f; contradiction
  | [ H: _ |- {True} + {~True} ] => left; exact I
  end.

Ltac decide_prio_dec := 
  lazymatch goal with
  | [ |- forall x y : _, {?prrel _ _ } + {~?prrel _ _ } ] =>
    unfold prrel; intros x y; destruct x as (a, pf); destruct y as (b, pf');
    decide_prio_dec_aux
  end.
