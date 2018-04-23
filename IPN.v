(********************** David Delahaye et Mathieu Lasjaunias *******)
(*******************************************************************)

Require Import Arith. Search nat.

(*************************************************)

Inductive place_type : Set :=
| mk_place : nat -> place_type.
(* une place pour chaque entier naturel *)

Inductive transition_type : Set :=
| mk_trans : nat -> transition_type.
(* une transition pour chaque entier naturel *)

Definition weight_type :=
  transition_type -> place_type -> option nat.

(* 4 "TYPES" of arcs : pred, post, pred_inhib, pred_test 
   along with "some" weight   (default is 1 in real). *)

Definition marking_type := place_type -> option nat.
(* again a partial function    (print option.) *)

(*
Print beq_nat. Print Nat.eqb.
(* égalités de fonctions ?   retrouver le nat input du constructeur mk_place ! *)
Definition beq_places (p p' : place_type) : bool :=
fix eq_places (p p' : place_type) : bool :=
  match p with
  | _ => match p' with
      end.

(* given a marking m, one wants to put j tokens inside place p *)  
Definition mark (m:marking_type) (p:place_type) (j:nat) : marking_type :=
  fun p' => if beq_nat p p' 
            then j             (* j tokens inside place p *)
            else m p'.         (* other tokens untouched  *)
*)

Definition is_enabled
           (pre_of_t:place_type -> option nat)
           (m:place_type -> option nat)
  : bool := false.    (* le verre à moitié vide *)

Definition enabled (pre:weight_type) (m:marking_type) : transition_type -> bool := fun t => is_enabled (pre t) m.

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

Variable conds : Set.  (* conditions allowing transitions *)
Variable c : conds.

Definition condition_type :=
  transition_type -> conds -> bool.
(* condition_type t C = true     <=> C is associated with t *)

Notation "cond [ trans ]" := (condition_type trans cond = true)  
                               (at level 50) : type_scope. (* ? *)
(* difference between Notation and Infix ? *)
Record IPN : Type := mk_IPN
                       { pn :> PN ;
                         cond : condition_type
                         (* actions and functions ... *) }.
Print IPN.
  
Require Import Coq.Bool.Bool.
Definition conditionType := nat.  (* c1, c2, c3, ... *)
Definition eval := conditionType -> bool.    (* condition true or false *)

Definition trans_firable (m:marking_type) (t:transition_type) : bool :=
  (* (trans_enabled m t) andb forall c in t,   *)
  if true
  then true
  else false.

(*
Definition marking_after (m:marking_type) (t:transition_type) (proofmt : trans_firable m t) : marking_type :=
  if trans_firable m t = false
  then m
  else m :-: pre(t) :+: post(t).  
 *)

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

