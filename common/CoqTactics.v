(** * General-purpose Tactics *)

Ltac split_and :=
  match goal with
  | |- ?A /\ ?B => split; [ split_and | split_and]
  | _ => idtac
  end.
