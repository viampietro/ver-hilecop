(** * State and Error Monad *)

Require Import String.
Require Import List.
Require Import ListDep.

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

  Definition Bind2 {A B C: Type} (f: Mon (A * B)) (g: A -> B -> Mon C) : Mon C :=
    Bind f (fun xy => g (fst xy) (snd xy)).
  
  Definition Get : Mon state := fun s => OK s s.
  Definition Put : state -> Mon unit := fun s _ => OK tt s.

End StateAndErrMonad.

Arguments OK {state A s}.
Arguments Error {state A s}.
Arguments Mon {state}.
Arguments Err {state A}.
Arguments Ret {state A}.
Arguments Bind {state A B}.
Arguments Get {state}.
Arguments Put {state}.

Notation "'do' X <- A ; B" := (Bind A (fun X => B))
                                (at level 200, X ident, A at level 100, B at level 200).

Notation "'do' '|(' X , Y ')|' <- A ; B" := (Bind2 A (fun X Y => B))
   (at level 200, X ident, Y ident, A at level 100, B at level 200).

Notation "'RedS' r" := match r with
                     | OK _ s => inl s
                     | Error msg => inr msg
                       end (at level 0).

Notation "'RedV' r" := match r with
                     | OK v _ => inl v
                     | Error msg => inr msg
                     end (at level 0).


