(*****************************************************)
(**** by Mathieu Lasjaunias and David Delahaye *******)
(*****************************************************)

Require Import Arith Omega List Bool.
Search nat. (* Require Import Nat.    needed ? older than Arith ? *)
Search list.

(********************************************************)
(***** Syntax of (extended, generalized) Petri nets ******)

Inductive place_type : Set :=
| mk_place : nat -> place_type.
(* places indexed by natural numbers *)

Inductive transition_type : Set :=
| mk_trans : nat -> transition_type.
(* transitions indices and constructor *)

(*
Inductive arc_type : Set :=
| mk_arc_pt : place_type -> transition_type -> nat -> arc_type
| mk_arc_tp : transition_type -> place_type -> nat -> arc_type
(* extended (generalized = nat) Petri nets *)
| mk_arc_inhi : place_type -> transition_type -> nat -> arc_type
| mk_arc_test : place_type -> transition_type -> nat -> arc_type.
 *)

(*   4 "TYPES" of arcs : pred, post, pred_inhib, pred_test 
    along with "some" weight   (default is 1 in real).       *)

Definition weight_type := transition_type -> place_type -> option nat.
(* partial function :   Some x / None   *)
Definition marking_type := place_type -> nat.

(***  priority relation     to DETERMINE the Petri net ***)
Require Import Relations. Print relation. (* standard library *)
Definition priority_type := transition_type -> transition_type -> bool.  (* "bool" better than "Prop"     for     if/then/else *)

(** "Structure" = "Record" **) 
Structure PN : Type := mk_PN
                      { places : list place_type ;
                        transitions : list transition_type ;
                        (* no_dup_places : NoDup places ;
                        no_dup_transitions : NoDup transitions ; *) 
                        
                        pre : weight_type ;
                        post : weight_type ;

                        pre_test : weight_type ;
                        pre_inhi : weight_type ;

                        marking : marking_type ;
                        (*marking : list (place_type * nat)*)
                        priority : priority_type }.
Print PN.

Print NoDup. Print nodup. Print NoDup_nodup. (* opaque proof ? *)
Print find_some.  (* big,  but probably useful function *)
(* split  / combine   ... *)

(**********************************************************)
(************ Semantics of these Petri nets  **************)

Definition get_place_index (p : place_type) : nat :=
  match p with
  | mk_place n  => n
  end.
Definition get_transition_index (t : transition_type) : nat :=
  match t with
  | mk_trans n  => n
  end.

Search nat. Require Import Decidable. Print Decidable.
SearchPattern (forall x y : _, {x = y} + {x <> y}).
Print N.eq_dec.
Definition dec_places : forall x y : place_type, {x = y} + {x <> y}.
Proof.
  decide equality.
  decide equality.
Qed.

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
Print marking_type. Print place_type.
Definition set_mark (m:marking_type) (p:place_type) (j:nat)
  : marking_type :=
  fun p' =>  if beq_places p p'
             then j             (* set j tokens in place p *)
             else m p'.         (* other tokens left unchanged  *)
Definition reset (m:marking_type) (p:place_type) (j:nat)
  : marking_type := set_mark m p 0.


(* given a marking m, add j tokens inside place p *)  
Definition incr_mark (m:marking_type) (p:place_type)
           (j:option nat) (op:nat->nat->nat)
  : marking_type :=
  fun p' =>
    if beq_places p p'
    then match j with
          | None => m p
          | Some i => op (m p) i  (* j=i tokens added *)
          end      
    else m p'.         (* other places left unchanged  *)

(* Require Import Nat. (* for Nat.leb != (Bool.)leb *) 
   library "Nat" is included into "Arith"   ? ... *)

(***** this complex function is maybe bugged ! ***)


Locate "<?". Print Nat.ltb. Print Nat.leb.
Print pre. Print weight_type.
Fixpoint pn_trans_enabled_PT (places : list place_type)
         (pre_t : place_type -> option nat)
         (m : marking_type)
  : bool :=
  match places with
  | nil => true
  | cons h tail => match pre_t h with
                   | None => pn_trans_enabled_PT tail pre_t m
                   | Some n => (n <=? (m h))
                                 &&
                                 (pn_trans_enabled_PT tail pre_t m)
                   end
  end.
Fixpoint pn_trans_enabled_TEST (places : list place_type)
         (pre_test_t : place_type -> option nat)
         (m : marking_type)
  : bool :=
  match places with
  | nil => true
  | cons h tail => match pre_test_t h with
                   | None => pn_trans_enabled_TEST tail pre_test_t m
                   | Some n => (n <=? (m h))
                                 &&
                                 (pn_trans_enabled_TEST tail pre_test_t m)
                   end
  end.
(*** TO DO : only 1 such function "pn_trans_enabled_ptORtest"
      instead of 2 ***)

Fixpoint pn_trans_enabled_INHI (places : list place_type)
         (pre_inhi_t : place_type -> option nat)
         (m : marking_type)
  : bool :=
  match places with
  | nil => true
  | cons h tail => match pre_inhi_t h with
                   | None => pn_trans_enabled_INHI tail pre_inhi_t m
                   | Some n => ((m h) <? n)
                                 &&
                                 (pn_trans_enabled_INHI tail pre_inhi_t m)
                   end
  end.

(* enabled =  arcs_PT + arcs_TEST + arcs_INHI     are satisfied *)
(*** decidable, of course ***)
Definition pn_trans_is_enabled (places : list place_type)
           (pre : weight_type)
           (pre_test : weight_type)
           (pre_inhi : weight_type)
           (m : marking_type)
  : transition_type -> bool :=  
  fun t => (pn_trans_enabled_PT places (pre t) m)
             &&
             (pn_trans_enabled_TEST places (pre_test t) m)
             &&
             (pn_trans_enabled_INHI places (pre_inhi t) m). 

(* for a given marking, return the list of "enabled transitions" *)
Fixpoint pn_trans_is_enabled_because (pn:PN) (l : list transition_type) {struct l} (* structural induction over list of transitions *) :
  list transition_type :=
  match l with
  | nil => nil
  | cons t tail => if (pn_trans_is_enabled
                         (places pn)
                         (pre pn)
                         (pre_test pn)
                         (pre_inhi pn)  
                         (marking pn)
                         t)
                   then cons t (pn_trans_is_enabled_because pn tail)
                   else pn_trans_is_enabled_because pn tail
  end.

Definition pn_is_enabled_because_look (pn:PN) : list transition_type :=
  pn_trans_is_enabled_because pn (transitions pn).

(*  maybe first   "Fixpoint fire_aux ... "   
    and then      "Definition fire ..."  *)
Print Nat.sub. Print Nat.add.

Fixpoint update_marking
         (pn:PN)
         (l: list place_type)
         (t:transition_type)
         (m:marking_type)
         {struct l}
  (* structural induction over list of places *)
  : marking_type :=
  match l with
  | nil => (marking pn)
  | cons p tail => update_marking pn
                                  tail
                                  t
                                  (incr_mark (incr_mark (marking pn)
                                                        p
                                                        ((pre pn) t p)
                                                        Nat.sub)
                                             p
                                             ((post pn) t p)
                                             Nat.add)
  end.
 
(* fire transition t, updating the marking accordingly *)
Definition fire_trans (pn : PN)  (t:transition_type) : PN  :=
  mk_PN
    (places pn)
    (transitions pn)
    (* (no_dup_places pn)
    (no_dup_transitions pn) *)
    (pre pn)
    (post pn)
    (pre_test pn)
    (pre_inhi pn)
    (update_marking pn
                    (places pn)
                    t
                    (marking pn))
    (priority pn).

Import ListNotations.  (* very handful notations *)
Require Import Coq.Sorting.Sorted. Search sort.
(* to get the priority transition, and determine the system *)
Section Insertion_sort.
  Variable A : Type.
  
  Variable leb : A -> A -> bool.
  Notation "a <= b" := (leb a b = true).

  (* Fixpoint extract_higher (l : list A) (nonil : l <> nil) : A := 

   no need to sort the list of transition
only the highest priority transition is looked for 

OR MAYBE NOT : we need to fire ALL enabled transitions
 as much as possible, getting across "conflicts" between transitions 
*)
        
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

  Variable a : A.
  (* Fixpoint find_highest (A:Type) (l:list A) : (A * list A) :=
    match l with
    | nil => (a, nil)
    | b::l' => if leb a b
               then find_highest b l'
               else find_highest a l'
    end.*)
End Insertion_sort.

Definition sort_trans (prio:priority_type) (l:list transition_type)
  : list transition_type :=
  sort transition_type prio l.

Search list. Print last. (* default value in case the list is empty ! *)
Print exists_last. (* full of sumbools but maybe useful ? *)
Definition highest_transition (prio:priority_type) (l:list transition_type)
  : transition_type :=
  last (sort_trans prio l) (mk_trans 512).

(*****************************************************)
Variable priori : priority_type.  (*  ?????????  *)
Definition fire_pn (pn:PN) : PN :=
  match pn_is_enabled_because_look pn with
  | nil => pn  (* fire no transition *)
  | t::tail => fire_trans pn
                          (highest_transition priori
                                              (pn_is_enabled_because_look pn))
  end.

Fixpoint animate_pn (pn:PN) (n:nat) : list marking_type :=
  (* on fait n pas de calcul  
    et on retourne le chemin des marquages *)
  match n with
  | O => [ marking pn ]
  | S n' => (marking pn) :: (animate_pn (fire_pn pn)
                                        n')
  end.  

Search list.
Fixpoint function2list (places:list place_type) (m:marking_type)
  : list (place_type * nat) :=
  match places with
  | nil => nil
  | p::tail => (p,m p) :: function2list tail m
  end.

Fixpoint animate_pn_list (pn:PN) (n:nat) : list (list (place_type * nat)) :=
  (* on fait n pas de calcul  
    et on retourne le chemin des marquages *)
  match n with  
  | O => [ function2list (places pn) (marking pn) ]
  | S n' => (function2list (places pn) (marking pn))
              :: (animate_pn_list (fire_pn pn) n')
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
(* a (probably useless example of notation ... *)

Record IPN : Type := mk_IPN
                       { pn : PN ;
                         conditions : caracteristic_function_for_gards
                         (* actions and functions ...
                           not relevant for now *) }.
Print IPN.
  
(********************************************************)
(************** semantic for IPN ************************)


(* TO DO. But not today *)

(******************************************************************)
(**** small example of  Petri net (page 24 in Ibrahim thesis) *****)

Print NoDup. Print nodup. Print NoDup_nodup. (* opaque proof ? *)
(* 3 places *)
Definition places_ex : (list place_type) :=
 (* nodup *) [ mk_place 0 ;
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

(* disons   t_i prioritaire sur t_j   pour tout j >= i *)
(* faut-il un ordre strict ou large ?? *)
Definition priority_ex (t1 t2 : transition_type) : bool :=
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

Definition pn_ex := mk_PN
                      places_ex
                      transitions_ex

                      (* proof of no duplicatas  places_ex*)
                      (* proof of no duplicatas  transitions_ex*)
                      
                      pre_function_ex
                      post_function_ex
                      pre_test_function_ex
                      pre_inhi_function_ex                 
                      
                      initial_marking_ex
                      priority_ex.
Check pn_ex. Compute (marking pn_ex).

Compute (animate_pn_list
           pn_ex
           10).
Compute (pn_is_enabled_because_look pn_ex). Print pn_ex.
Compute fire_pn pn_ex.
(*** ne marche pas bordel ! rien n'est changé ***)
Print fire_pn.
Compute (highest_transition priority_ex
                                           (pn_is_enabled_because_look pn_ex)).  (* highest priority  works well *)
Compute (fire_trans pn_ex
                    (highest_transition priority_ex
                                        (pn_is_enabled_because_look pn_ex))).  (*** c'est fire_trans qui marche pas !!! *)
Print fire_trans. (*** donc c'est update_marking qui foire !!! *)
Print update_marking.  (*** ou plus exactement incr_mark ! *)
Print incr_mark.




(**********************************************************)
(* should I print the list of transitions 
   labelling this path of markings ?

should I print the list of enabled transitions at each step ?

     If "yes", how to do so without getting mad at Coq ? *)
(**********************************************************)



(*** interpreted Petri net ***)
Definition conditions_ex (t : transition_type) (c : gard_type)
  : bool
  := match (t, c) with
  | (mk_trans 0, mk_gard 0) => true
  | (mk_trans 2, mk_gard 1) => true
  | _ => false
  end.

Definition ipn_ex := mk_IPN
                       pn_ex
                       conditions_ex.





(*************************************************)
(**************** Syntax of SITPN ****************)

Print Between.  (** seems cool ! and cooler than what I can do **)
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
Print clock_ind.      

Not needed now.     Will it ever be needed ?  *)

(****************************************************)
(************** Semantic of SITPN *******************)

(* TO DO  *)


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