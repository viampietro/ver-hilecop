Require Import MSets.MSetWeakList.
Require Import Coq.Structures.OrdersEx.
Require Import NArith.
Require Import SetoidList.

(** Defines finite sets of natural. *)

Module NSet := Make (N_as_OT).
Import NSet.

Declare Scope nset_scope.

Infix "U" := union (at level 60, right associativity).
Infix "U+" := add (at level 60, right associativity).
Notation "{[ ]}" := empty (format "{[ ]}") : nset_scope.
Notation "{[ x , y , .. , z ]}" := (add x (add y .. (add z empty) ..)) : nset_scope.
Notation "{[ x ]}" := (add x empty) (at level 0) : nset_scope.

(* Include NatSet.Raw. *)

(* Lemma for_all_ind : forall Q x s, For_all Q (x :: s) -> For_all Q s. *)
(* Proof. *)
(*   intros Q x s Hforall y Hin_y_s. *)
(*   apply (Hforall y (InA_cons_tl x Hin_y_s)). *)
(* Defined. *)

(* Fixpoint filter_ Q (EltSubset := { e : elt | Q e }) (f : EltSubset -> bool) (s : t) : For_all Q s -> t := *)
(*   match s return For_all Q s -> t with *)
(*   | nil => (fun _ => nil) *)
(*   | x :: l => *)
(*     (fun for_all : For_all Q _ => *)

(*        (* Existantial version of t of type {t | In t (this (transitions sitpn))} *) *)
(*        let xe := exist Q x (for_all x (InA_cons_hd l (eq_refl x))) in *)

(*        (* Proof that for_all is valid on decreasing list. *)        *)
(*        if f xe then x :: filter_ Q f l (for_all_ind Q x l for_all) else filter_ Q f l (for_all_ind Q x l for_all)) *)
(*   end. *)
