(** * State and Error Monad *)

Require Import String.
Require Import List.
Require Import ListsDep.
Require Import StateAndErrorMonad.

Import ListNotations.

(*  *)

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

(*  *)

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

(** ** State-and-error monadic map function *)

Section Map.

  Variable state B C : Type.
  
  Variable f : B -> @Mon state C.
  
  (** Maps all elements of [lofBs] to a term [c] of [C] and returns
      the resulting list or return an error. *)

  Fixpoint map_aux (lofBs : list B) (lofCs : list C) {struct lofBs} :
    Mon (list C) :=
    match lofBs with
    | nil => Ret lofCs
    | b :: tl =>
      do c <- f b;
      map_aux tl (lofCs ++ [c])
    end.

  (** Wrapper around the [omap_aux] function. *)

  Definition map (lofBs : list B) : @Mon state (list C) :=
    map_aux lofBs nil.
  
End Map.

Arguments map_aux {state B C}.
Arguments map {state B C}.

(** ** Transform and map elements of a list. *)

Section TMap.

  Variable state : Type.
  Variable A B C : Type.
  Variable f : B -> @Mon state C.
  
  (** Given a proof that all elements in [lofAs] can yield a term of
      [B], transform each element of [lofAs] into a term [b] of [B], then
      maps [b] to Some term [c] of [C] or return an error.
   *)

  Fixpoint tmap_aux (lofAs : list A) (lofCs : list C) {struct lofAs} :
    (forall a, In a lofAs -> B) -> @Mon state (list C) :=
    match lofAs with
    | nil => fun _ => Ret lofCs
    | a :: tl =>
      fun pf : _ =>
        (* Creates a B from a proof that (In a (a :: tl)). *)
        let b := pf a (in_eq a tl) in

        (* Creates a proof that (forall a, In a tl -> B) *)
        let pf_tl := in_T_in_sublist_T a tl pf in

        (* Continues the mapping or returns an error. *)
        do c <- f b;
        tmap_aux tl (lofCs ++ [c]) pf_tl
    end.

  (** Wrapper around the [topte_map_aux] function. *)

  Definition tmap (lofAs : list A) :
    (forall a, In a lofAs -> B) -> @Mon state (list C) :=
    tmap_aux lofAs nil.
  
End TMap.

Arguments tmap {state A B C}.
