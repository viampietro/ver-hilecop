(** * State and Error Monad *)

Require Import String.
Require Import List.
Require Import ListDep.
Require Import StateAndErrorMonad.

Import ListNotations.

(** ** State-and-error monad version of getv *)

Fixpoint getv {state A B}
         {eqk}
         (eqk_dec : forall x y, {eqk x y} + {~eqk x y})
         (k : A) (l : list (A * B)) {struct l} : @Mon state B :=
  match l with
  | nil => Err ("getv: found unassociated key.")
  | (a, b) :: tl =>
    if eqk_dec k a then Ret b else getv eqk_dec k tl
  end.

(** ** State-and-error monad version of find *)

(** The difference between [find] and [getv] is that [find] returning
    [None] is not necessarily an error, whereas if a key [k] is not
    associated to a value in list [l], then [getv k l] returns an
    error.*)

Fixpoint find {state A} (f : A -> @Mon state bool) (l : list A) {struct l} : @Mon state (option A) :=
  match l with
  | nil => Ret None
  | a :: tl =>
    do res <- f a;
    if res then Ret (Some a) else find f tl
  end.

(** ** State-and-error monad version of iter *)

Fixpoint iter {state A} (f : A -> @Mon state unit) (l : list A) {struct l} : @Mon state unit :=
  match l with
  | nil => Ret tt
  | b :: tl => do _ <- iter f tl; f b
  end.

Functional Scheme iter_ind := Induction for iter Sort Prop.

Fixpoint titer {state A B} (f : B -> @Mon state unit) (lofAs : list A) {struct lofAs} :
  (forall a, In a lofAs -> B) -> @Mon state unit :=
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

Functional Scheme titer_ind := Induction for titer Sort Prop.

(** ** State-and-error monad version of map *)

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

(** ** State-and-error monad version of transform and map *)

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

(** ** State-and-error monad version of fold left.  *)

Fixpoint fold_left {state A B} (f : B -> A -> @Mon state B) (l : list A) (b : B) {struct l} : @Mon state B :=
  match l with
  | nil => Ret b
  | a :: tl =>
    do b' <- f b a;
    fold_left f tl b'
  end.

Section TFold_Left_Recursor.

  Variable State : Type.
  Variable A B C : Type.
  Variable f : C -> B -> @Mon State C.

  (** Given a proof that all elements in [lofAs] can yield a term of
      [B], transform each element of [lofAs] into a term [b] of [B], then
      calls [f] on [c] and [b] to build a new term of [C]. *)
  
  Fixpoint tfold_left (lofAs : list A) (c : C) : 
    (forall a, In a lofAs -> B) -> @Mon State C :=
    match lofAs with
    | nil => fun _ => Ret c
    | a :: tl =>
      fun pf : _ =>
        (* Creates a B from a proof that (In a (a :: tl)). *)
        let b := pf a (in_eq a tl) in

        (* Creates a proof that (forall a, In a tl -> B) *)
        let pf_tl := in_T_in_sublist_T a tl pf in

        (* Builds a new term of C by calling f on b and c and
           continues. *)
        do c' <- f c b;
        tfold_left tl c' pf_tl
    end.
  
End TFold_Left_Recursor.

Arguments tfold_left {State A B C}.

(** ** State-and-error monad version of foreach. *)

Section ForEach.

  Variable state A : Type.
  Variable f : A -> list A -> @Mon state unit.
  
  Fixpoint foreach_aux (lft rght : list A) {struct rght} : @Mon state unit :=
    match rght with
    | a :: tl => do _ <- f a (lft ++ tl); foreach_aux (lft ++ [a]) tl
    | _ => Ret tt
    end.

  Definition foreach (l : list A) : @Mon state unit := foreach_aux [] l.
  
End ForEach.

Arguments foreach {state A}.

Section TForEach.

  Variable state A B : Type.
  Variable f : forall (b : B) (lofBs : list B) (lofAs : list A) (pf : forall a, In a lofAs -> B), @Mon state unit.
  
  Fixpoint tforeach_aux (lft : list B) (rght : list A) {struct rght} :
    (forall a, In a rght -> B) -> @Mon state unit :=
    match rght with
    | a :: tl =>
      fun pf =>
        (* Creates a B from a proof that (In a (a :: tl)). *)
        let b := pf a (in_eq a tl) in
        (* Creates a proof that (forall a, In a tl -> B) *)
        let pf_tl := in_T_in_sublist_T a tl pf in
        
        do _ <- f b lft tl pf_tl; tforeach_aux (lft ++ [b]) tl pf_tl
    | _ => fun _ => Ret tt
    end.

  Definition tforeach (l : list A) : (forall a, In a l -> B) -> @Mon state unit :=
    tforeach_aux [] l.
  
End TForEach.

Arguments tforeach {state A B}.
