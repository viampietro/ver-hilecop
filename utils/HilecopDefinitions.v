Require Import Lists.List.

(** Macro for fst and split composition. *)

Definition fs {A B : Type} (l : list (A * B)) := fst (split l).
