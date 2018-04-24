(******* Mathieu Lasjaunias, David Delahaye, David Andreu   *******)
(******************************************************************)

Require Import Arith Omega List Bool. Search nat.

(*************************************************)

Inductive place_type : Set :=
| mk_place : nat -> place_type.
(* une place pour chaque entier naturel *)

Inductive transition_type : Set :=
| mk_trans : nat -> transition_type.
(* une transition pour chaque entier naturel *)

Print option.
Definition weight_type :=
  transition_type -> place_type -> option nat.

(*   4 "TYPES" of arcs : pred, post, pred_inhib, pred_test 
    along with "some" weight   (default is 1 in real).       *)

Definition marking_type := place_type -> option nat.
(* again a _partial_ function : "None" if no value     *)

(*************************** Petri Nets ******)
Record PN : Type := mk_PN
                      { place : list place_type ;
                        transition : list transition_type ;

                        pre : weight_type ;
                        post : weight_type ;
                        pre_test : weight_type ;
                        pre_inhib : weight_type ;

                        init_marking : marking_type }.
Print PN.
Search list. Print list.

(* predecessors, successors ...
 to update the markings and emulate the Petri nets *)
Definition place_before_trans (t:transition_type) (p:place_type) : bool :=
  false.

Definition place_after_trans (t:transition_type) (p:place_type) : bool :=
  false.

(******************* Semantics ********************)

(* verify if 2 places are equal; return a boolean *)
Definition beq_places (p p' : place_type) : bool :=
  match (p, p') with
  | (mk_place n, mk_place n') => beq_nat n n'
  end.

(* given a marking m, one wants to put j tokens inside place p *)  
Definition mark (m:marking_type) (p:place_type) (j:nat) : marking_type :=
  fun p' =>  if beq_places p p'
             then Some j        (* j tokens inside place p *)
             else m p'.         (* other tokens unchanged  *)

(* given a marking m, one wants to put j tokens inside place p *)  
Definition mark_add (m:marking_type) (p:place_type) (j:nat) : marking_type :=
  fun p' =>
    if beq_places p p'
    then   match (m p') with
           | None => Some j   (* j tokens inside place p *)
           | Some i => Some (i + j)
           end
    else m p'.         (* other tokens unchanged  *)

(****  Induction structurelle sur une liste  ******)
Definition get_index (p : place_type) : nat :=
  match p with
  | mk_place n  => n
  end.

Print le. Print Nat. Require Import Nat. (* Nat.leb *)
Fixpoint pn_trans_enabled
           (places : list place_type)
           (pre_t : place_type -> nat)
           (m : place_type -> nat)
  : bool :=
  match places with
  | nil => true
  | cons h tail => if leb (pre_t h) (m h)
                   then pn_trans_enabled tail pre_t m
                   else false 
  end.

Print eq.
Fixpoint pn_trans_enabled'
         (places : list place_type)
         (pre_t : place_type -> option nat)
         (m : marking_type)
  : bool :=
  match places with
  | nil => true
  | cons h tail => match pre_t h with
                   | None => pn_trans_enabled tail pre_t m
                   | Some n => match m h with
                               | Some p => andb (leb n p)
                                                pn_trans_enabled tail pre_t m
                               | _ => false
                               end
                   end
  end.
  
(****** les options c'est peut-être pas une bonne idée ...  ***)

Definition pn_trans_is_enabled
           (places : list place_type)
           (pre : weight_type)
           (m : marking_type)
  : transition_type -> bool :=
  
  fun t => pn_trans_enabled places (pre t) m.



(****************************************************************)
(********** IPN (Interpreted Petri Net) *************************)
(****************************************************************)

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
(*********** redrawn in my beautiful Oxford ! *********************)

Import ListNotations.
(* 3 places *)
Definition places : (list place_type) :=
  [ mk_place 0 ;
    mk_place 1 ;
    mk_place 2 ].

(* 3 transitions *)
Definition transitions : (list transition_type) :=
  [ mk_trans 0 ;
    mk_trans 1 ;
    mk_trans 2 ].

(* 3 arcs PT (place transition)  "incoming" *) 
Definition pre_function (t : transition_type) (p : place_type)
  :=
  match (t, p) with
  | (mk_trans 0, mk_place 0) => Some 1
  | (mk_trans 1, mk_place 1) => Some 2
  | (mk_trans 2, mk_place 2) => Some 1
  | _ => None
  end.

(* 4 arcs TP                     "outcoming" *)
Definition post_function (t : transition_type) (p : place_type)
  :=
  match (t, p) with
  | (mk_trans 0, mk_place 1) => Some 2
  | (mk_trans 0, mk_place 2) => Some 1
  | (mk_trans 1, mk_place 0) => Some 1
  | (mk_trans 2, mk_place 0) => Some 1
  | _ => None
  end.

(*** tokens of the initial marking ***)
Definition initial_marking (p : place_type) :=
  match p with
  | mk_place 0 => Some 1
  | mk_place 1 => Some 2
  | mk_place 2 => Some 1
  | _ => None
  end. Check initial_marking. Check marking_type.

(* 1 arc of type "test" *)
Definition pre_test_function (t : transition_type) (p : place_type) :=
  match (t, p) with
  | (mk_trans 2, mk_place 1) => Some 1
  | _ => None
  end.

(* 1 arc of type "inhibitor"  *)
Definition pre_inhi_function (t : transition_type) (p : place_type) :=
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
                       pre_inhi_function                 

                       initial_marking)
                    conditions.
Print ipn.
