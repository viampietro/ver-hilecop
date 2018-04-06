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
Definition place_before_trans (t:transition_type) (p:place_type)  : Prop :=
  False.

Definition place_after_trans (t:transition_type) (p:place_type) : Prop :=
  False.

Definition trans_firable (m:marking_type) (t:transition_type) : Prop :=
  False.

Definition marking_after (m:marking_type) (t:transition_type) (p : trans_firable m t) : marking_type :=
  m.  

(******************************************************************)
Parameter conds : Set.  (* conditions allowing transitions *)
Parameter c : conds.
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


(*************************************************************)
(******* example 0 (page 24 in Ibrahim thesis) *********)

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

