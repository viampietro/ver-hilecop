(**** by Mathieu Lasjaunias and David Delahaye *******)
(*****************************************************)

Require Import Arith Omega List Bool. Search nat.
(* Require Import Nat. *)

(***** Syntax of (extended generalized) Petri nets ******)

Inductive place_type : Set :=
| mk_place : nat -> place_type.
(* places indexed par natural numbers *)

Inductive transition_type : Set :=
| mk_trans : nat -> transition_type.
(* transitions indexed by natural numbers *)

Inductive arc_type : Set :=
| mk_pt : place_type -> transition_type -> nat -> arc_type
| mk_tp : transition_type -> place_type -> nat -> arc_type
(* extended (generalized = nat) Petri nets *)
| mk_inhi : place_type -> transition_type -> nat -> arc_type
| mk_test : place_type -> transition_type -> nat -> arc_type.
                                                      
Definition weight_type := transition_type -> place_type -> option nat.

(*   4 "TYPES" of arcs : pred, post, pred_inhib, pred_test 
    along with "some" weight   (default is 1 in real).       *)

Definition marking_type := place_type -> nat.
(*  "None" if no token ;   "Some j"      if j tokens     *)


Search list. Print list.   (** "more operational" than functions *) 
(*** "Structure" = "Record" **) 
Structure PN : Type := mk_PN
                      { places : list place_type ;
                        transitions : list transition_type ;
                        attention_places : NoDup places ;
                        attention_transitions : NoDup transitions ; 
                        
                        pre : weight_type ;
                        post : weight_type ;

                        pre_test : weight_type ;
                        pre_inhi : weight_type ;

                        marking : marking_type
                        (* marking : list nat *)}.
Print PN.

(**********************************************************)
(********** Semantics of these simple Petri nets **********)

(** probably useless but who knows .. **)
Definition get_place_index (p : place_type) : nat :=
  match p with
  | mk_place n  => n
  end.
(** probably useless but who knows .. **)
Definition get_transition_index (t : transition_type) : nat :=
  match t with
  | mk_trans n  => n
  end.

(* verify if 2 places have same index, return a boolean *)
Definition beq_places (p p' : place_type) : bool :=
  match (p, p') with
  | (mk_place n, mk_place n') => beq_nat n n'
  end.
(* verify if 2 transitions have same index, return a bool *)
Definition beq_transitions (t t' : transition_type) : bool :=
  match (t, t') with
  | (mk_trans n, mk_trans n') => beq_nat n n'
  end.

(* given a marking m, set j tokens in place p *)  
Definition set (m:marking_type) (p:place_type) (j:nat)
  : marking_type :=
  fun p' =>  if beq_places p p'
             then j             (* set j tokens in place p *)
             else m p'.         (* other tokens left unchanged  *)
Definition reset (m:marking_type) (p:place_type) (j:nat)
  : marking_type :=    set m p 0.


(* given a marking m, add j tokens inside place p *)  
Definition add_mark (m:marking_type) (p:place_type) (j:option nat)
  : marking_type :=
  fun p' =>
    if beq_places p p'
    then match j with
          | None => m p
          | Some i => (m p) + i  (* j=i tokens added *)
          end      
    else m p'.         (* other places left unchanged  *)

Definition substract_mark (m:marking_type) (p:place_type) (j:option nat) : marking_type :=
  fun p' =>
    if beq_places p p'
    then match j with
          | None => m p
          | Some i => (m p) - i  (* j=i tokens substracted *)
          end
    else m p'.         (* other places left unchanged  *)
(** one can make 1 such function instead of 2 (+ -) **)

(******************************************************)
(****  Structural induction on lists  (Fixpoint) ******)

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

Fixpoint pn_is_enabled_because (pn:PN) (l : list transition_type) {struct l} :
  list transition_type :=
  match l with
  | nil => nil
  | cons t tail => if (pn_trans_is_enabled
                         (places pn)
                         (pre pn)
                         (marking pn)
                         t)
                   then cons t (pn_is_enabled_because pn tail)
                   else pn_is_enabled_because pn tail
  end.

Definition pn_is_enabled_because_howtosay (pn:PN) : list transition_type :=
  pn_is_enabled_because pn (transitions pn).

(*  maybe "Fixpoint fire_aux ... "   
    and then "Definition fire ..."  *)
Fixpoint fire_trans (pn : PN)  (t:transition_type) : PN  :=
  mk_PN
    (places pn)
    (transitions pn)
    (attention_places pn)
    (attention_transitions pn)
    (pre pn)
    (post pn)
    (pre_test pn)
    (pre_inhi pn)
    match (places pn) with
    | nil => (marking pn)
    | cons p tail => add_mark (substract_mark (marking pn)
                                              p
                                              ((pre pn) t p))
                              p
                              ((post pn) t p)
    end.

(*** relation de priorite pour _determiniser_ le systeme ****)
Require Import Relations. Print relation. 
Definition priority_type := transition_type -> transition_type -> bool.  (* bool better than Prop for if/then/else *)

Import ListNotations.
Section Insertion_sort.
  Variable A : Type.
  Variable leb : A -> A -> bool.
  Notation "a <= b" := (leb a b = true).

  Fixpoint insert (a:A) (l: list A) : list A :=
    match l with
    | nil  => [a]
    | b::l' => if leb a b
               then a::l
               else b::insert a l'
    end.
  
  Fixpoint sort (l: list A) : list A :=
    match l with
    | [ ] => [ ]
    | a::l' => insert a (sort l')
    end.
End Insertion_sort.

Definition sort_trans (prio:priority_type) (l:list transition_type)
  : list transition_type :=
  sort transition_type prio l.

Search list.
Print last. (* default value in case the list is empty ! *)
Definition highest_transition (prio:priority_type) (l:list transition_type)
  : transition_type :=
  last (sort_trans prio l) (mk_trans 512).

Variable priori : priority_type.  (* plus tard on veut un exemple *)
Definition fire_pn (pn:PN) : PN :=
  match pn_is_enabled_because_howtosay pn with
  | nil => pn
  | t::tail => fire_trans pn
                          (highest_transition priori
                                              (pn_is_enabled_because_howtosay pn))
  end.

Fixpoint animate_pn (pn:PN) (n:nat) : list marking_type :=
  (* on ne fait que n pas de calcul 
    (qui peut ne pas terminer sinon) 
    et on retourne le chemin des marquages *)
  match n with
  | O => [ marking pn ]
  | S n' => (marking pn) :: (animate_pn (fire_pn pn)
                                     n')
  end.  

(****************************************************************)
(********** syntax of IPN (Interpreted Petri Net) ***************)

(* conditions/gards  on transitions *)
Inductive gard_type : Set :=
| mk_gard : nat -> gard_type.

Definition caracteristic_function_for_gards := transition_type -> gard_type -> bool.
(* condition_type t g = true     <=>     g is associated with t *)

Notation "cond [ trans ]" := (caracteristic_function_for_gards
                                trans
                                cond
                              = true)  
                               (at level 50) : type_scope.
(* one example of notation ...   probably useless though  *)

Record IPN : Type := mk_IPN
                       { pn : PN ;
                         conditions : caracteristic_function_for_gards
                         (* actions and functions ...
                           not relevant for now *) }.
Print IPN.
  
(********************************************************)
(************** semantic for IPN ************************)


(* TO DO *)

(******************************************************************)
(**** small example of  Petri net (page 24 in Ibrahim thesis) *****)

(* 3 places *)
Definition places_ex : (list place_type) :=
  [ mk_place 0 ;
    mk_place 1 ;
    mk_place 2 ].

(* 3 transitions *)
Definition transitions_ex : (list transition_type) :=
  [ mk_trans 0 ;
    mk_trans 1 ;
    mk_trans 2 ].

(* 3 arcs PT (place transition)  "incoming" *) 
Definition pre_function_ex (t : transition_type) (p : place_type)
  :=
  match (t, p) with
  | (mk_trans 0, mk_place 0) => Some 1
  | (mk_trans 1, mk_place 1) => Some 2
  | (mk_trans 2, mk_place 2) => Some 1
  | _ => None
  end.

(* 4 arcs TP                     "outcoming" *)
Definition post_function_ex (t : transition_type) (p : place_type)
  :=
  match (t, p) with
  | (mk_trans 0, mk_place 1) => Some 2
  | (mk_trans 0, mk_place 2) => Some 1
  | (mk_trans 1, mk_place 0) => Some 1
  | (mk_trans 2, mk_place 0) => Some 1
  | _ => None
  end.

(*** tokens of the initial marking ***)
Definition initial_marking_ex (p : place_type) :=
  match p with
  | mk_place 0 =>  2
  | mk_place 1 =>  0
  | mk_place 2 =>  0
  | _ => 0
  end. Print initial_marking_ex. Check marking_type.
(* ? reductions, simplifications ? *)

(* 1 arc of type "test" *)
Definition pre_test_function_ex (t : transition_type) (p : place_type) :=
  match (t, p) with
  | (mk_trans 2, mk_place 1) => Some 1
  | _ => None
  end.

(* 1 arc of type "inhibitor"  *)
Definition pre_inhi_function_ex (t : transition_type) (p : place_type) :=
  match (t, p) with
  | (mk_trans 1, mk_place 2) => Some 1
  | _ => None
  end.


Definition pn_ex := mk_PN
                      places_ex
                      transitions_ex

                      (* proof of no duplicatas  places_ex*)
                      (* proof of no duplicatas  transitions_ex*)
                      
                      pre_function_ex
                      post_function_ex
                      pre_test_function_ex
                      pre_inhi_function_ex                 
                      
                      initial_marking_ex.

Definition conditions_ex (t : transition_type) (c : gard_type)
  : bool
  := match (t, c) with
  | (mk_trans 0, mk_gard 0) => true
  | (mk_trans 2, mk_gard 1) => true
  | _ => false
  end.

(* reseaux de Petri generalise etendu, interprete *)

Definition ipn_ex := mk_IPN
                       pn_ex
                       conditions_ex.

(* disons   t_i prioritaire sur t_j   pour tout j >= i *) 
Definition priority (t1 t2 : transition_type) : bool :=
  (* transitions squared  ---> lot's of match branches ... *)
  match (t1 , t2) with
  | (mk_trans 0, mk_trans 0) => true
  | (mk_trans 0, mk_trans 1) => true
  | (mk_trans 0, mk_trans 2) => true
  | (mk_trans 1, mk_trans 0) => false
  | (mk_trans 1, mk_trans 1) => true
  | (mk_trans 1, mk_trans 2) => true
  | (mk_trans 2, mk_trans 0) => false
  | (mk_trans 2, mk_trans 1) => false
  | (mk_trans 2, mk_trans 2) => true
  | (_,_) => false  (* False or True     who care ? *) 
  end.



Eval simpl in (animate_pn pn_ex 10). Print caca.

(*************************************************)
(**************** Syntax of SITPN ****************)

Record interval_type : Set := mk_interval
  { mini : nat ;
    maxi : nat ;
    min_le_max : mini <= maxi }.

                             
Definition caracterictic_function_for_intervals :=
  transition_type -> interval_type -> bool.
(* temporal_transition_type t i = true   <=> C is associated with t *)


Record ITPN : Type := mk_ITPN
  { ipn : IPN;
    intervals : caracterictic_function_for_intervals }.
Print ITPN.


(* Inductive clock : Set :=
| rising_edge | falling_edge. 
Print clock_ind.      NOT NEEDED NOW  *)

(****************************************************)
(************** Semantic of SITPN *******************)

(* TO DO : how to deal cleanly with intervals ? *)


(******************************************************************)
(******* David Andreu's big example (redrawn in my Oxford) ********)

(* 7 places *)
Definition places_ex2 : (list place_type) :=
  [ mk_place 1 ;
    mk_place 2 ;
    mk_place 3 ;
    mk_place 4 ;
    mk_place 5 ;
    mk_place 6 ;
    mk_place 7 ].

(* 6 transitions *)
Definition transitions_ex2 : (list transition_type) :=
  [ mk_trans 0 ;
    mk_trans 1 ;
    mk_trans 2 ;
    mk_trans 3 ;
    mk_trans 4 ;
    mk_trans 5 ;
    mk_trans 6 ].

(* 7 arcs PT (place transition)  "incoming" *) 
Definition pre_function_ex2 (t : transition_type) (p : place_type) :=
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
Definition pre_test_function_ex2 (t : transition_type) (p : place_type) :=
  match (t, p) with
  | (mk_trans 1, mk_place 1) => Some 1
    (* place 1 needs (at least) 1 token, 
       which won't be taken by transition 1 *)
  | _ => None
  end.

(* 1 arc of type "inhibitor"  *)
Definition pre_inhi_function_ex2 (t : transition_type) (p : place_type) :=
  match (t, p) with
  | (mk_trans 0, mk_place 1) => Some 1
  (* place 1 needs less than 1 token, 
     which won't be taken by transition 1 *)
  | _ => None
  end.

(* 7 arcs TP      "normal outcoming"  *)
Definition post_function_ex2 (t : transition_type) (p : place_type) :=
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
Definition init_marking_ex2 (p : place_type) :=
  match p with
  | mk_place 0 => 1
  | mk_place 1 => 0
  | mk_place 2 => 0
  | mk_place 3 => 0
  | mk_place 4 => 0
  | mk_place 5 => 0
  | mk_place 6 => 0
  | _ => 0
  end.

Definition conditions_ex2 (t : transition_type) (c : gard_type) :=
  match (t, c) with
  | (mk_trans 1, mk_gard 1) => true
  | _ => false
  end.
  (* 1 condition/gard  :  Petri net influenced by environnement *)

Lemma preuve3le5 : 3 <= 5. Proof. omega. Qed.
Definition int1_35 := mk_interval
                     3
                     5
                     preuve3le5.
Print le.
Lemma preuve2le255 : 2 <= 255. Proof. omega. Qed.
Definition int1_2oo := mk_interval
                     2
                     255
                     preuve2le255.

Definition intervals_ex2 (t : transition_type) (i : interval_type) :=
  match (t, i) with
  | (mk_trans 3, int1_35) => true
  | (mk_trans 6, int1_2oo) => true
  | _ => false
  end.
  
(* no conditions in this Petri Net (and no actions of functions)
 ---> reseaux de Petri generalise etendu, mais pas interprete *)

Definition itpn1 :=  mk_ITPN
                       (mk_IPN
                          (mk_PN
                             places_ex2
                             transitions_ex2

                             pre_function_ex2
                             post_function_ex2
                             pre_test_function_ex2
                             pre_inhi_function_ex2
                             
                             init_marking_ex2)
                          conditions_ex2)
                       intervals_ex2.