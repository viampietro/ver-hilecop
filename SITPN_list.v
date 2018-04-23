Require Import Arith Bool List Omega.

(* Require Import Cpdt.CpdtTactics Cpdt.MoreSpecif. *)
(* Require Extraction. *)

Set Implicit Arguments.  (* after match *)
Set Asymmetric Patterns.  (* before match ? *)

(* length-indexed lists *)

Section ilist.
  Variable A : Set.

  Inductive ilist : nat -> Set :=
  | Nil : ilist O
  | Cons : forall n, A -> ilist n -> ilist (S n).

  Fixpoint app n1 (ls1 : ilist n1) n2 (ls2 : ilist n2) :
    ilist (n1 + n2) :=
    match ls1 in (ilist n1) return (ilist (n1 + n2)) with
    | Nil => ls2
    | Cons _ x ls1' => Cons x (app ls1' ls2)
    end.

  Inductive fin : nat -> Set :=
  | First : forall n, fin (S n)
  | Next : forall n, fin n -> fin (S n).
  
  Fixpoint get n (ls : ilist n) : fin n -> A :=
    match ls with
    | Nil =>
      fun idx => match idx in fin n' return (match n' with
                                             | O => A
                                             | S _ => unit
                                             end) with
                 | First _ => tt
                 | Next _ _ => tt
                 end
    | Cons _ x ls' =>
      fun idx => match idx in fin n' return (fin (pred n') -> A) -> A with
                 | First _ => fun _ => x
                 | Next _ idx' => fun get_ls' => get_ls' idx'
                 end (get ls')
    end.
  
End ilist.

Arguments Nil {A}.
Arguments First {n}.

Check Cons 0 (Cons 1 (Cons 2 Nil)).

Eval simpl in get (Cons 0 (Cons 1 (Cons 2 Nil))) First.
Compute get (Cons 0 (Cons 1 (Cons 2 Nil))) First.

Eval simpl in get (Cons 0 (Cons 1 (Cons 2 Nil))) (Next First).
Eval simpl in get (Cons 0 (Cons 1 (Cons 2 Nil))) (Next (Next First)).