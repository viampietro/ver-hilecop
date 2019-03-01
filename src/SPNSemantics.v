Require Import Hilecop.SPNAnimator.

(*! ============================= !*)
(*! ======= Spn Semantics ======= !*)
(*! ============================= !*)


(** * Preliminary definitions *)

(** In all the following definitions, (IsWellDefinedSpn spn) is a necessary condition. *)

Inductive IsPredInList {A : Type} (a b : A) : list A -> Prop :=
| IsPredInList_cons:
    forall l l' l'' : list A,
      NoDup (l ++ a :: l' ++ b :: l'') -> 
      IsPredInList a b (l ++ a :: l' ++ b :: l'').

Definition l := [0; 2; 3].

(** HasHigherPriority: ∀ t, t' ∈ T, t ≻ t' *)

Definition HasHigherPriority
           (spn : Spn)
           (t t' : trans_type) :=
  IsWellDefinedSpn spn ->
  forall pgroup : list trans_type,
    In pgroup spn.(priority_groups) ->
    In t pgroup ->
    In t' pgroup ->
    IsPredInList t t' pgroup.

(** IsSensitized:
    ∀ t ∈ T, marking m, t ∈ sens(m) if
    ∀ p ∈ P, m(p) ≥ Pre(p, t) ∧ 
             m(p) ≥ Pre_t(p, t) ∧ 
             (m(p) < Pre_i(p, t) ∨ Pre_i(p, t) = 0) *)

Definition IsSensitized
           (spn : Spn)
           (marking : marking_type)
           (t : trans_type) : Prop :=
  IsWellDefinedSpn spn ->
  HaveSameStructMarking spn.(marking) marking ->
  forall (p : place_type)
    (n : nat),
    In (p, n) marking ->
    n >= (pre spn t p) /\
    n >= (test spn t p) /\
    (n < (inhib spn t p) \/ (inhib spn t p) = 0).

(** SpnIsFirable: 
    ∀ t ∈ T, state s = (m), marking m, t ∈ firable(s) if 
    t ∈ sens(m) *)

Definition SpnIsFirable
           (spn : Spn)
           (state : SpnState)
           (t : trans_type) :=
  IsSensitized spn state.(marking) t.



(** * Semantics definition *)

(** Represents the two clock events regulating the Spn evolution. *)

Inductive clock : Set :=
| falling_edge : clock
| raising_edge : clock.

(** Represents the Spn Semantics  *)

Inductive SpnSemantics (spn : Spn) (fired : list trans_type) (spn' : Spn) : Prop :=
| SpnSemantics_falling_edge :
| SpnSemantics_raising_edge : .