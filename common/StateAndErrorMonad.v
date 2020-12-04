(** * State and Error Monad *)

Require Import String.
Require Import List.
Require Import ListsDep.

Section StateAndErrMonad.

  (* A state type *)
  
  Variable state : Type.

  (* The value returned by a state-and-error monad can either
     be an error with a message or a couple state-value.
   *)
  
  Inductive Res (A: Type) (s : state) : Type :=
  | Error: string -> Res A s
  | OK: A -> state -> Res A s.

  Arguments OK {A s}.
  Arguments Error {A s}.
  
  Definition Mon (A : Type) : Type := forall s : state, Res A s.

  Definition Ret {A : Type} : A -> Mon A := fun x s => OK x s.
  Definition Err {A: Type} (msg: string) : Mon A := fun (s: state) => Error msg.

  Definition Bind {A B : Type} : Mon A -> (A -> Mon B) -> Mon B :=
    fun c1 c2 s1 =>
      match c1 s1 with
      | Error msg => Error msg
      | OK x s2 =>
        match c2 x s2 with
        | Error msg => Error msg
        | OK y s3 => OK y s3
        end
      end.
  Definition Get : Mon state := fun s => OK s s.
  Definition Put : state -> Mon unit := fun s _ => OK tt s.


End StateAndErrMonad.

Arguments Mon {state}.
Arguments Err {state A}.
Arguments Ret {state A}.
Arguments Bind {state A B}.
Arguments Get {state}.
Arguments Put {state}.

Notation "'do' X <- A ; B" := (Bind A (fun X => B))
                                (at level 200, X ident, A at level 100, B at level 200).

Notation "'RedS' r" := match r with
                     | OK _ _ _ _ s => s
                     | Error _ _ _ _ => _
                       end (at level 0).

Notation "'RedV' r" := match r with
                     | OK _ _ _ v _ => inl v
                     | Error _ _ _ msg => inr msg
                     end (at level 0).

(* State-and-error monad version of lists function. *)

Fixpoint titer {A B C} (f : B -> @Mon C unit) (lofAs : list A) {struct lofAs} :
  (forall a, In a lofAs -> B) -> @Mon C unit :=
  match lofAs with
  | nil => fun _ => Ret tt
  | a :: tl =>
    fun pf : _ =>
      (* Creates a B from a proof that (In a (a :: tl)). *)
      let b := pf a (in_eq a tl) in

      (* Creates a proof that (forall a, In a tl -> B) *)
      let pf_tl := in_T_in_sublist_T a tl pf in
      
      do _ <- titer f tl pf_tl; f b
  end.

Fixpoint fold_left {A B C} (f : C -> B -> @Mon A C) (l : list B) (c : C) {struct l} : @Mon A C :=
  match l with
  | nil => Ret c
  | b :: tl =>
    do c' <- f c b;
    fold_left f tl c'
  end.

Fixpoint iter {A B} (f : B -> @Mon A unit) (l : list B) {struct l} : @Mon A unit :=
  match l with
  | nil => Ret tt
  | b :: tl => do _ <- iter f tl; f b
  end.

Fixpoint find {A B} (f : B -> @Mon A bool) (l : list B) {struct l} : @Mon A (option B) :=
  match l with
  | nil => Ret None
  | b :: tl =>
    do res <- f b;
    if res then Ret (Some b) else find f tl
  end.
