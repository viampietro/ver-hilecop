(***********************************)
(********  notations  **************)


Notation "!" := (False_rec _ _).
Notation "[ e ]" := (exist _ e _).

Print sumbool.

Notation "'Yes'" := (left _ _).
Notation "'No'" := (right _ _).
Notation "'Reduce' x" := (if x then Yes else No) (at level 50).

Definition eq_nat_dec : forall n m : nat, {n = m} + {n <> m}.
  refine (fix f (n m : nat) : {n = m} + {n <> m} :=
            match n, m with
            | O, O => Yes
            | S n', S m' => Reduce (f n' m')
            | _, _ => No
            end); congruence.
Defined.

Compute eq_nat_dec 2 2.
Compute eq_nat_dec 2 3.

Require Import Extraction.
Extraction eq_nat_dec.

Definition eq_nat_dec' (n m : nat) : {n = m} + {n <> m}.
  decide equality.
Defined.

Extract Inductive sumbool => "bool" ["true" "false"].
Extraction eq_nat_dec'.

Notation "x || y" := (if x then Yes else Reduce y).

Set Implicit Arguments.

(* monade *)
Inductive maybe (A : Set) (P : A -> Prop) : Set :=
| Unknown : maybe P
| Found : forall x : A, P x -> maybe P.

Print maybe.

Notation "{{ x | P }}" := (maybe (fun x => P)).
Notation "??" := (Unknown _).
Notation "[| x |]" := (Found _ x _).

Definition pred_strong7 : forall n : nat, {{m | n = S m}}.
  refine (fun n =>
    match n return {{m | n = S m}} with
      | O => ??
      | S n' => [|n'|]
    end); trivial.
Defined.

Eval compute in pred_strong7 2.
Eval compute in pred_strong7 0.

Print sumor.
Notation "!!" := (inright _ _).
Notation "[|| x ||]" := (inleft _ [x]).

Definition pred_strong8 : forall n : nat, {m : nat | n = S m} + {n = 0}.
  refine (fun n =>
    match n with
      | O => !!
      | S n' => [||n'||]
    end); trivial.
Defined.

Eval compute in pred_strong8 2.
Eval compute in pred_strong8 0.

(*************** draft *************)

Require Import Arith. (* for beq_nat  *)

Definition placeType := nat.   (* nat or Set or Finite Set *)
Definition transitionType := nat.
Definition markingType := placeType -> nat.

Definition set (m:markingType) (p:placeType) (j:nat) : markingType :=
  fun p' => if beq_nat p p' 
            then j             (* j tokens inside place p *)
            else m p'.         (* m(p') tokens elsewhere  *)

Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.  (* "finite" is harder *)
Definition transitionPredecessors (t:transitionType) : Ensemble placeType :=
Empty_set placeType.
Definition transitionSuccessors (t:transitionType) :  Ensemble placeType :=
Empty_set placeType.

(*************************************************)
(**************************************************)
           
Inductive place_type : Set :=
| mk_place : nat -> place_type.
(* places indexées par les entiers naturels *)

Inductive transition_type : Set :=
| mk_trans : nat -> transition_type.
(* transitions indexées par les entiers naturels *)

Definition weight_type :=
  transition_type -> place_type -> option nat.
(* weight of any "type" of arc (pred, post, pred_i, pred_t), 
if any weight. *)

Definition marking_type := place_type -> option nat.
(* a marking is a partial function *)

Record PN : Type := mk_PN
                      { place : place_type -> Prop ;
                        transition : transition_type -> Prop ;
                        pre : weight_type ;
                        post : weight_type ;
                        pre_test : weight_type ;
                        pre_inhibit : weight_type ;
                        init_marking : marking_type }.
Print PN.

(* predecessor, successor ... 
to update the markings and emulate the Petri nets *)
Definition place_before_trans (t:transition_type) (p:place_type)  : bool :=
  false.

Definition place_after_trans (t:transition_type) (p:place_type) : bool :=
  false.


(****************************************************************)
(******************** IPN ***************************************)

Inductive node : Set := place | transition.

Section IPN.
  Variable conds : Set.  (* conditions allowing transitions *)
  Variable c : conds.

  Definition condition_type :=
    transition_type -> conds -> bool.
  (* condition_type t C = true     <=> C is associated with t *)
  (* Instead of "bool", "Prop" is possible...  (-> binary predicate) *)
  Notation "cond [ trans ]" := (condition_type trans cond = true)  
                                 (at level 50) : type_scope. (* ? *)
  (* difference between Notation and Infix ? *)
  Record IPN : Type := mk_IPN
                         { pn :> PN ;
                           cond : condition_type
                           (* actions and functions ... *) }.
  Print IPN.
End IPN.

Require Import Coq.Bool.Bool.
Definition conditionType := nat.  (* c1, c2, c3, ... *)
Definition eval := conditionType -> bool.    (* condition true or false *)

Definition trans_firable (m:marking_type) (t:transition_type) : Prop :=
  (* (trans_enabled m t) andb forall c in t, eval c = true)  *)
  if True
  then True
  else False.

Definition marking_after (m:marking_type) (t:transition_type) (proofmt : trans_firable m t) : marking_type :=
  if trans_firable m t = false
  then m
  else m :-: pre(t) :+: post(t).  

(******************************************************************)
(******* example of Petri net (page 24 in Ibrahim thesis) *********)

(* 3 places *)
Definition places (p : place_type) :=
  match p with
  | mk_place 0 => True
  | mk_place 1 => True
  | mk_place 2 => True
  | _ => False
  end.

(* 3 transitions *)
Definition transitions (t : transition_type) :=
  match t with
  | mk_trans 0 => True
  | mk_trans 1 => True
  | mk_trans 2 => True
  | _ => False
  end.

(* 3 arcs PT (place transition) 
 "incoming" : transition pivot   ;   "outcoming" : place pivot *) 
Definition pre_function (t : transition_type) (p : place_type) :=
  match (t, p) with
  | (mk_trans 0, mk_place 0) => Some 1
  | (mk_trans 1, mk_place 1) => Some 2
  | (mk_trans 2, mk_place 2) => Some 1
  | _ => None
  end.

(* 4 arcs TP *)
Definition post_function (t : transition_type) (p : place_type) :=
  match (t, p) with
  | (mk_trans 0, mk_place 1) => Some 2
  | (mk_trans 0, mk_place 2) => Some 1
  | (mk_trans 1, mk_place 0) => Some 1
  | (mk_trans 2, mk_place 0) => Some 1
  | _ => None
  end.

(* tokens *)
Definition initial_marking (p : place_type) :=
  match p with
  | mk_place 0 => Some 1
  | mk_place 1 => Some 2
  | mk_place 2 => Some 1
  | _ => None
  end.

(* 1 arc of type "test" *)
Definition pre_test_function (t : transition_type) (p : place_type) :=
  match (t, p) with
  | (mk_trans 2, mk_place 1) => Some 1
  | _ => None
  end.

(* 1 arc of type "inhibitor"  *)
Definition pre_inhibit_function (t : transition_type) (p : place_type) :=
  match (t, p) with
  | (mk_trans 1, mk_place 2) => Some 1
  | _ => None
  end.

Definition conditions (t : transition_type) (c : conds) := false.
(* no conditions in this Petri Net (and no actions of functions)
 ---> reseaux de Petri generalise etendu, mais pas interprete *)

Definition ipn := mk_IPN
                    (mk_PN
                       places
                       transitions
                       pre_function
                       post_function
                       pre_test_function
                       pre_inhibit_function                 
                       initial_marking)
                    conditions.

