(** * More Tactics for lists *)

Require Import List.
Require Import common.InAndNoDup.

Import ListNotations.

(** Search for a hypothesis H of the form (incl l l') 
    and a hypothesis H' of the form (In a l).
    If H and H' in the context then apply H a H'
    and name the resulting hypothesis as Hin. *)

Ltac apply_incl Hin :=
  lazymatch goal with
  | [ H: incl ?l ?l' |- _ ] =>
    lazymatch goal with
    | [H': In ?a l |- _ ] => specialize (H a H') as Hin
    | _ => fail "No hypotheses of the form (In ?a ?l) in the context"
    end
  | _ => fail "No hypotheses of the form (incl ?l ?l') in the context"
  end.

(* Applies the [in_app_or] lemma on an hypothesis of the 
   form "In _ (_ ++ _)", then inversion. *)

Ltac destruct_in_app_or :=
  lazymatch goal with
  | [ H : List.In _ (_ ++ _) |- _ ] =>
    apply in_app_or in H; inversion_clear H
  end.

(* Deduces "?a = ?b" from "In ?a [?b]".  Introduces an hypothesis Heqn
   in the proof context.  *)

Ltac singleton_eq :=
  lazymatch goal with
  | [ H: List.In ?a [?b] |- _ ] =>
    let Heq := fresh "Heq" in
    inversion_clear H as [Heq | ]; [auto | contradiction]
  end.

(** Given a [H] of type [NoDup ?l], reduces [H] to a form
    where [?l] has no head element. *)

Ltac red_nodup H :=
  lazymatch type of H with
  | List.NoDup (?a :: ?l) =>
    inversion_clear H;
    lazymatch goal with
    | [ H': ~List.In a _, H'': List.NoDup l |- _ ] =>
      clear H'; red_nodup H''
    | _ => fail "Proper hypotheses not found after NoDup reduction"
    end
  | _ => idtac
  end.

(** Given a [H] of the form [NoDup ?l] where [?l] is of the form [?m0 ++ ... ++ ?m__i], 
    deduces [NoDup ?m__n] where [n] is given in parameter. *)

Ltac get_nodup_at H n :=
  lazymatch type of n with
  | nat =>
    lazymatch type of H with
    | List.NoDup (?l ++ ?l') =>
      lazymatch n with
      | 0 =>
        specialize (proj1 (nodup_app l l' H));
        let H := fresh "H" in intros H
      | S ?m =>
        specialize (proj2 (nodup_app l l' H));
        let H := fresh "H" in intros H; get_nodup_at H m
      end
    | List.NoDup _ =>
      lazymatch n with
      | 0 => idtac
      | S ?m => fail "No reduction possible at" n "in" H
      end
    end
  | _ => fail "Term" n "is not of type nat"
  end.
