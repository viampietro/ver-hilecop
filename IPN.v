(**** by Mathieu Lasjaunias and David Delahaye *******)
(*****************************************************)

Require Import Arith Omega List Bool. Search nat.
(* Require Import Nat. *)

(***** Semantic of (extended generalized) Petri nets ******)

Inductive place_type : Set :=
| mk_place : nat -> place_type.
(* places indexed par natural numbers *)

Inductive transition_type : Set :=
| mk_trans : nat -> transition_type.
(* transitions indexed by natural numbers *)

Inductive arc_type : Set :=
| mk_pt : place_type -> transition_type -> nat -> arc_type
| mk_tp : transition_type -> place_type -> nat -> arc_type

| mk_inhi : place_type -> transition_type -> nat -> arc_type
| mk_test : place_type -> transition_type -> nat -> arc_type.
                                                      
Definition weight_type := transition_type -> place_type -> option nat.

(*   4 "TYPES" of arcs : pred, post, pred_inhib, pred_test 
    along with "some" weight   (default is 1 in real).       *)

Definition marking_type := place_type -> nat.
(*  "None" if no token ;   "Some j"      if j tokens     *)

(************** Structure  (= Record) ********** ******)
Structure PN : Type := mk_PN
                      { places : list place_type ;
                        transitions : list transition_type ;

                        pre : weight_type ;
                        post : weight_type ;

                        pre_test : weight_type ;
                        pre_inhi : weight_type ;

                        marking : marking_type }.
Print PN.
Search list. Print list.

(************* Semantics of these Petri nets **************)

Definition get_index (p : place_type) : nat :=
  match p with
  | mk_place n  => n
  end.

(* verify if 2 places are equal, return a boolean *)
Definition beq_places (p p' : place_type) : bool :=
  match (p, p') with
  | (mk_place n, mk_place n') => beq_nat n n'
  end.

(* given a marking m, set j tokens in place p *)  
Definition set (m:marking_type) (p:place_type) (j:nat)
  : marking_type :=
  fun p' =>  if beq_places p p'
             then j             (* set j tokens in place p *)
             else m p'.         (* other tokens left unchanged  *)
Definition reset (m:marking_type) (p:place_type) (j:nat)
  : marking_type :=
  set m p 0.

(* given a marking m, _add_ j tokens inside place p *)  
Definition add_mark (m:marking_type) (p:place_type) (j:option nat)
  : marking_type :=
  fun p' =>
    if beq_places p p'
    then match j with
          | None => m p
          | Some i => (m p) + i  (* j=i tokens added *)
          end      
    else m p'.         (* other places left unchanged  *)

Definition sub_mark (m:marking_type) (p:place_type) (j:option nat) : marking_type :=
  fun p' =>
    if beq_places p p'
    then match j with
          | None => m p
          | Some i => (m p) - i  (* j=i tokens substracted *)
          end
    else m p'.         (* other places left unchanged  *)

(*******************************************)
(****  Structural induction on lists  ******)
Require Import Nat. (* for Nat.leb != (Bool.)leb *)

Fixpoint pn_trans_enabled
         (places : list place_type)
         (pre_t : place_type -> option nat)
         (m : marking_type)
  : bool :=
  match places with
  | nil => true
  | cons h tail => match pre_t h with
                   | None => pn_trans_enabled tail pre_t m
                   | Some n => andb (leb n (m h))
                                    (pn_trans_enabled tail pre_t m)
                   end
  end.

Definition pn_trans_is_enabled
           (places : list place_type)
           (pre : weight_type)
           (m : marking_type)
  : transition_type -> bool :=  
  fun t => pn_trans_enabled places (pre t) m.

Print transitions.
Fixpoint pn_enabled (pn:PN) (l : list transition_type) {struct l} :
  list transition_type :=
  match l with
  | nil => nil
  | cons t tail => if (pn_trans_is_enabled
                         (places pn)
                         (pre pn)
                         (marking pn)
                         t)
                   then cons t (pn_enabled pn tail)
                   else pn_enabled pn tail
  end.

Definition pn_is_enabled (pn:PN) : list transition_type :=
  pn_enabled pn (transitions pn).

Print PN. Print weight_type. Print marking_type. Check add_mark.
Fixpoint fire (pn : PN)  (t:transition_type) : PN  :=
  mk_PN
    (places pn)
    (transitions pn)
    (pre pn)
    (post pn)
    (pre_test pn)
    (pre_inhi pn)
    match (places pn) with
    | nil => (marking pn)
    | cons p tail => add_mark  (sub_mark (marking pn)
                                         p
                                         ((pre pn) t p))
                               p
                               ((post pn) t p)
    end.

(*** relation de priorite pour _determiniser_ le systeme ****)
Require Import Relations. Print relation. 
Definition priority_type := transition_type -> transition_type -> Prop.

(****************************************************************)
(********** IPN (Interpreted Petri Net) *************************)
(****************************************************************)

Parameter gards : Set.  (* conditions/gards  on transitions *)
Parameter g : gards.

Definition condition_type := transition_type -> gards -> bool.
(* condition_type t C = true     <=>     C is associated with t *)

Notation "cond [ trans ]" := (condition_type trans cond = true)  
                               (at level 50) : type_scope. (* ? *)

Record IPN : Type := mk_IPN
                       { pn : PN ;
                         conds : condition_type
                         (* actions and functions ...
                           not relevant for now *) }.
Print IPN.
  
Definition conditionType := nat.  (* c1, c2, c3, ... *)
Definition evalb := conditionType -> bool.    (* condition true or false *)


(******************************************************************)
(**** small example of  Petri net (page 24 in Ibrahim thesis) *****)
(******************************************************************)

Import ListNotations.
(* 3 places *)
Definition ex_places : (list place_type) :=
  [ mk_place 0 ;
    mk_place 1 ;
    mk_place 2 ].

(* 3 transitions *)
Definition ex_transitions : (list transition_type) :=
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
  | mk_place 0 =>  2
  | mk_place 1 =>  0
  | mk_place 2 =>  0
  | _ => 0
  end. Print initial_marking. Check marking_type.  (* ? *)

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

Hypothesis c0  c1 : gards.
Definition conditions (t : transition_type) (c : gards)
  : bool
  := match (t, c) with
  | (mk_trans 0, c0) => true
  | (mk_trans 2, c1) => true
  | _ => false
  end.

(* reseaux de Petri generalise etendu, interprete *)

Definition ex_pn := mk_PN
                   ex_places
                   ex_transitions
                   
                   pre_function
                   post_function
                   pre_test_function
                   pre_inhi_function                 

                   initial_marking.

Definition ipn := mk_IPN
                    ex_pn

                    conditions.

(* disons   t_i prioritaire sur t_j   pour tout j >= i *) 
Definition priority (t1 t2 : transition_type) : Prop :=
  (* transitions squared *)
  match (t1 , t2) with
  | (mk_trans 0, mk_trans 0) => True
  | (mk_trans 0, mk_trans 1) => True
  | (mk_trans 0, mk_trans 2) => True
  | (mk_trans 1, mk_trans 0) => False
  | (mk_trans 1, mk_trans 1) => True
  | (mk_trans 1, mk_trans 2) => True
  | (mk_trans 2, mk_trans 0) => False
  | (mk_trans 2, mk_trans 1) => False
  | (mk_trans 2, mk_trans 2) => True
  | (_,_) => False  (* False or True   whatever *) 
  end.
                                  
Compute pn_is_enabled ex_pn.

(**************** Syntax of SITPN ****************)

Record interval_type : Set :=
  { mini : nat ;
    maxi : nat ;
    min_le_max : mini <= maxi }.
Print interval_type.

Definition temporal_transition_type :=
  transition_type -> interval_type -> bool.
(* temporal_transition_type t i = true   <=> C is associated with t *)

Record ITPN : Type := mk_ITPN
  { ipn :> IPN;
    intervals : temporal_transition_type }.
Print ITPN.


Inductive clock : Set :=
| rising_edge | falling_edge.
Print clock_ind.



(******************************************************************)
(************* David Andreu's example (redrawn in my Oxford) ******)
(******************************************************************)

(* 7 places *)
Definition places' : (list place_type) :=
  [ mk_place 1 ;
    mk_place 2 ;
    mk_place 3 ;
    mk_place 4 ;
    mk_place 5 ;
    mk_place 6 ;
    mk_place 7 ].

(* 6 transitions *)
Definition transitions' : (list transition_type) :=
  [ mk_trans 0 ;
    mk_trans 1 ;
    mk_trans 2 ;
    mk_trans 3 ;
    mk_trans 4 ;
    mk_trans 5 ;
    mk_trans 6 ].

(* 7 arcs PT (place transition)  "incoming" *) 
Definition pre1 (t : transition_type) (p : place_type) :=
  match (t, p) with
  | (mk_trans 0, mk_place 0) => Some 1
  | (mk_trans 1, mk_place 0) => Some 1
  | (mk_trans 2, mk_place 2) => Some 2
  | (mk_trans 2, mk_place 3) => Some 1
  | (mk_trans 3, mk_place 4) => Some 1
  | (mk_trans 4, mk_place 5) => Some 1
  | (mk_trans 5, mk_place 6) => Some 1
  | _ => None
  end.

(* 1 arc of type "test" *)
Definition pre_test1 (t : transition_type) (p : place_type) :=
  match (t, p) with
  | (mk_trans 1, mk_place 1) => Some 1
    (* place 1 needs (at least) 1 token, 
       which won't be taken by transition 1 *)
  | _ => None
  end.

(* 1 arc of type "inhibitor"  *)
Definition pre_inhibit1 (t : transition_type) (p : place_type) :=
  match (t, p) with
  | (mk_trans 0, mk_place 1) => Some 1
  (* place 1 needs less than 1 token, 
     which won't be taken by transition 1 *)
  | _ => None
  end.

(* 7 arcs TP      "normal outcoming"  *)
Definition post1 (t : transition_type) (p : place_type) :=
  match (t, p) with
  | (mk_trans 0, mk_place 1) => Some 1
  | (mk_trans 0, mk_place 2) => Some 2
  | (mk_trans 0, mk_place 3) => Some 1
  | (mk_trans 1, mk_place 4) => Some 1
  | (mk_trans 2, mk_place 6) => Some 1
  | (mk_trans 3, mk_place 5) => Some 1
  | (mk_trans 4, mk_place 6) => Some 1
  | (mk_trans 5, mk_place 1) => Some 1
  | _ => None
  end.

(* tokens *)
Definition init_marking1 (p : place_type) :=
  match p with
  | mk_place 0 => Some 1
  | mk_place 1 => Some 0
  | mk_place 2 => Some 0
  | mk_place 3 => Some 0
  | mk_place 4 => Some 0
  | mk_place 5 => Some 0
  | mk_place 6 => Some 0
  | _ => None
  end.

Definition cond1 (t : transition_type) (c : conds) :=
  match (t, c) with
  | (mk_trans 1, C) => true
  | _ => false
  end.
  (* 1 condition/gard  :  Petri net influenced by environnement *)

Lemma preuve3le5 : 3 <= 5. Proof. omega. Qed.
Definition int1_35 := Build_interval_type
                     3
                     5
                     preuve3le5.
Print le.
Lemma preuve2le255 : 2 <= 255. Proof. omega. Qed.
Definition int1_2oo := Build_interval_type
                     2
                     255
                     preuve2le255.

Definition ints1 (t : transition_type) (i : interval_type) :=
  match (t, i) with
  | (mk_trans 3, int1_35) => true
  | (mk_trans 6, int1_2oo) => true
  | _ => false
  end.
  
(* no conditions in this Petri Net (and no actions of functions)
 ---> reseaux de Petri generalise etendu, mais pas interprete *)

Definition itpn1 :=  mk_ITPN
                       (Build_IPN
                          (Build_PN
                             place1
                             transition1
                             pre1
                             post1
                             init_marking1)
                          pre_test1
                          pre_inhibit1
                          cond1)
                       ints1.