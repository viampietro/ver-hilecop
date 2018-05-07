(*************************************************************)
(**** by Mathieu Lasjaunias, David Delahaye, David Andreu ****)
(*************************************************************)

Require Import Arith Omega List Bool. (* libraries *) 
Search nat.
(* Require Import Nat.  needed ? older than (called by ?) Arith ? *)
Search list.

(*********************************************************)
(***** Syntax of (extended, generalized) Petri nets ******)

Inductive place_type : Set :=
| mk_place : nat -> place_type.
(* places indexed by natural numbers *)

Inductive trans_type : Set :=
| mk_trans : nat -> trans_type.
(* transitions indices and constructor *)

(*   4 "TYPES" of arcs : pred, post, pred_inhib, pred_test 
    along with "some" weight   (default is 1 in real).       *)
Definition weight_type := trans_type -> place_type -> option nat.
(*  Why not "have fun" also with 4 new constructors ????
Inductive arc_type : Set :=
| mk_arc_pt : place_type -> transition_type -> nat -> arc_type
| mk_arc_tp : transition_type -> place_type -> nat -> arc_type
(* extended (generalized = nat) Petri nets *)
| mk_arc_inhi : place_type -> transition_type -> nat -> arc_type
| mk_arc_test : place_type -> transition_type -> nat -> arc_type.
 *)

(* partial function :   Some x / None   *)
Definition marking_type := place_type -> nat.

(***  priority relation     to DETERMINE the Petri net ***)
Require Import Relations. Print relation. (* standard library *)
Inductive prior_type : Set :=
  mk_prior_type :  forall (rel : trans_type -> trans_type -> bool),
    (forall x : trans_type, (rel x x) = false) ->
    () ->
    () -> prior_type.


(** "Structure" = "Record" **) 
Structure PN : Type := mk_PN
                      { places : list place_type ;
                        transs : list trans_type ;
                        nodup_places : NoDup places ;
                        nodup_transitions : NoDup transs ;
                        
                        pre : weight_type ;
                        post : weight_type ;

                        pre_test : weight_type ;
                        pre_inhi : weight_type ;

                        marking : marking_type ;
                        (*marking : list (place_type * nat)*)
                        priority : prior_type }.
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
Definition get_transition_index (t : trans_type) : nat :=
  match t with
  | mk_trans n  => n
  end.

(* verify if 2 places have same index, return a boolean *)
Definition beq_places (p p' : place_type) : bool :=
  match (p, p') with
  | (mk_place n, mk_place n') => beq_nat n n'
  end.
(* verify if 2 transitions have same index, return a bool *)
Definition beq_transs (t t' : trans_type) : bool :=
  match (t, t') with
  | (mk_trans n, mk_trans n') => beq_nat n n'
  end.

SearchPattern (forall x y : _, {x = y} + {x <> y}).
Print N.eq_dec.   (* awful but useful *) 
Definition places_eq_dec : forall x y : place_type,
    {x = y} + {x <> y}.
Proof.
  decide equality.
  decide equality.
Defined.
Definition transs_eq_dec : forall x y : trans_type,
    {x = y} + {x <> y}.
Proof.
  decide equality.
  decide equality.
Defined.

(********** given a marking m, set j tokens in place p **********)
Print marking_type. Print place_type.
Definition set_mark (m:marking_type) (p:place_type) (j:nat)
  : marking_type :=
  fun p' =>  if beq_places p p'
             then j             (* set j tokens in place p *)
             else m p'.         (* other tokens left unchanged  *)
Definition reset (m:marking_type) (p:place_type) (j:nat)
  : marking_type := set_mark m p 0.     (*** reset a place ***)

(* given a marking m, add/remove j tokens inside place p *)  
Definition modif_mark
           (m:marking_type)
           (p:place_type)
           (j:option nat)  (** option nat because of weight_type **)
           (op:nat->nat->nat)
  : marking_type :=
  fun p' =>
    if beq_places p p'
    then match j with
          | None => m p              (* no change *)
          | Some i => op (m p) i     (* j=i tokens added/removed *)
          end      
    else m p'.         (* other places left unchanged  *)

Print Nat.sub. Print Nat.add.   (** the 2 op(erators) to use ... **)
(* Require Import Nat. (* for Nat.leb != (Bool.)leb *) 
   library "Nat" is included into "Arith" ?   not clear ... *)

(***** this "modif_mark" function is bugged ??????????????? *****)

Locate "<?". Print Nat.ltb. Print Nat.leb.
Print pre. Print weight_type.
(**** uphill / downhill *)
Fixpoint enough_tokens_uphill
         (places : list place_type)
         (pre_classic_or_test_t : place_type -> option nat)
         (** "classic" and "test" arcs **)
         (m : marking_type)
  : bool :=
  match places with
  | nil => true
  | cons h tail => match pre_classic_or_test_t h with
                   | None => enough_tokens_uphill
                               tail
                               pre_classic_or_test_t
                               m
                   | Some n => (n <=? (m h))
                                 &&
                                 (enough_tokens_uphill
                                    tail
                                    pre_classic_or_test_t
                                    m)
                   end
  end.
Fixpoint not_too_many_tokens_uphill
         (places : list place_type)
         (pre_inhi_t : place_type -> option nat) (* inhibitor arcs *)
         (m : marking_type)
  : bool :=
  match places with
  | nil => true
  | cons h tail => match pre_inhi_t h with
                   | None => not_too_many_tokens_uphill
                               tail
                               pre_inhi_t
                               m
                   | Some n => ((m h) <? n)
                                 &&
                                 (not_too_many_tokens_uphill
                                    tail
                                    pre_inhi_t
                                    m)
                   end
  end.

(* enabled = arcs_classic + arcs_test + arcs_inhi     satisfied ! *)
(*** decidable, of course : ***)
Definition pn_trans_is_enabled (places : list place_type)
           (pre : weight_type)
           (pre_test : weight_type)
           (pre_inhi : weight_type)
           (m : marking_type)
  : trans_type -> bool :=  
  fun t => (enough_tokens_uphill places (pre t) m)
             &&
             (enough_tokens_uphill places (pre_test t) m)
             &&
             (not_too_many_tokens_uphill places (pre_inhi t) m). 

(* for a given marking, return the list of "enabled transitions" *)
Fixpoint pn_trans_is_enabled_because
         (pn:PN)
         (l : list trans_type) {struct l}
         (* structural induction over list of transitions *) :
  list trans_type :=
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
(*** for a Petri net, return the list of enabled transitions ***)
Definition pn_is_enabled_because_look (pn:PN) : list trans_type :=
  pn_trans_is_enabled_because pn (transs pn).

(****************************************************
marquage intermediaire (in english ?)  

transition enabled/firable (sensibilise/tirable)

conflit structurel / conflit effectif
( t0 est en conflit effectif avec t1 ne signifie pas que 
  t1 est en conflit effectif avec t0)

desensibilisation, de façon transitoire, 
resensibilisation (quasi-immediate)

NewEnabled est-il important ?  pas sûr..

----> quelles structures de donnée et quelles fonctions ? <---

*********************************************************)

Fixpoint update_marking
         (l : list place_type)
         (t : trans_type)
         (pre post : weight_type)
         (m : marking_type)
         {struct l}
  (* structural induction over list of places *)
  : marking_type :=
  match l with
  | nil => m
  | cons p tail => update_marking
                     tail
                     t
                     pre post
                     (modif_mark
                        (modif_mark
                           m
                           p
                           (pre t p)
                           Nat.sub)
                        p
                        (post t p)
                        Nat.add)
  end.
 
(* fire transition t, updating the marking of the Petri net ! *)
Definition fire_trans (pn : PN)  (t:trans_type) : PN  :=
  mk_PN
    (places pn)
    (transs pn)
    (nodup_places pn)
    (nodup_transitions pn)
    (pre pn)
    (post pn)
    (pre_test pn)
    (pre_inhi pn)
    (update_marking
       (places pn)
       t
       (pre pn) (post pn)
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

   we need to fire ALL enabled transitions
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

Definition sort_transs
           (prior : prior_type)
           (l : list trans_type)
  : list trans_type :=
  sort
    trans_type
    prior
    l.

Print PN. Print weight_type.
Fixpoint common_pre
           (t t' : trans_type)
           (pre : weight_type)
           (places : list place_type)
  : bool :=
  match places with
  | [ ] => false
  | p :: places' => match ((pre t p), (pre t' p)) with
                    | (Some _, Some _) => true
                    | (_, _) => common_pre
                                  t t'
                                  pre
                                  places'
                    end
  end.

Definition confl_with
         (t t' : trans_type)
         (prior : prior_type)
         (pre : weight_type)
         (places : list place_type)
  : bool :=
  if andb (common_pre
             t t'
             pre
             places)
          
          (prior t t') 
  then true
  else false.
Notation "t1 'confl' t2" := (confl_with
                               t1
                               t2
                             = true)  
                              (at level 50) : type_scope.
Print PN.
Print prior_type.
(*Definition confl_with
         (prior : prior_type)
         (pre : weight_type)
         ( : list place_type)
  : bool :=*)


(*** list of lists    ...   c'est chaud bouillant ca ... *)
(*Fixpoint struct_conflicts
           (prior : prior_type)
           (l : list trans_type)
  : list (list trans_type) :=
  match l with
  | [ ] => [ [ ]]
  | t :: l' => match [ l' ]
  end.*)

Search list. Print last. (* default value in case the list is empty ! *)
Print exists_last. (* full of sumbools but maybe useful ? *)
Definition highest_transition
           (prior : prior_type)
           (l : list trans_type)
  : trans_type :=
  last
    (sort_transs
       prior
       l)
    (mk_trans 512).

(********************* MAIN FUNCTION ************************)
Definition fire_pn (pn:PN) : PN :=
  match pn_is_enabled_because_look pn with
  | nil => pn  (* fire no transition *)
  | t::tail => fire_trans
                 pn
                 (highest_transition
                    (priority pn)
                    (pn_is_enabled_because_look pn))
  end.

(**** for the 3 following functions the goal is to have lists ! ****)
Fixpoint animate_pn (pn:PN) (n:nat) : list marking_type :=
  (*  run "fire_pn" for n steps, 
      return a path of length n  *)
  match n with
  | O => [ marking pn ]
  | S n' => (marking pn) :: (animate_pn (fire_pn pn)
                                        n')
  end.  
Print marking_type.
Search list.
Fixpoint function2list (places:list place_type) (m:marking_type)
  : list (place_type * nat) :=
  match places with
  | nil => nil
  | p :: tail => (p, m p) :: function2list tail m
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

Definition caract_funct_gards := trans_type -> gard_type -> bool.
(* condition_type t g = true     <=>     g is associated with t *)

Notation "cond [ trans ]" := (caract_funct_gards
                                trans
                                cond
                              = true)  
                               (at level 50) : type_scope.
(* a (probably useless example of notation ... *)

Record IPN : Type := mk_IPN
                       { pn : PN ;
                         conditions : caract_funct_gards
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
Definition ex_places : (list place_type) :=
  nodup
    places_eq_dec
    [ mk_place 0 ;
      mk_place 1 ;
      mk_place 2 ].
Print PN.
Definition ex_nodup_places : NoDup ex_places :=
  NoDup_nodup
    places_eq_dec
    ex_places. 

(* 3 transitions *)
Definition ex_transs : (list trans_type) :=
  [ mk_trans 0 ;
    mk_trans 1 ;
    mk_trans 2 ].
Definition ex_nodup_transs : NoDup ex_transs :=
  NoDup_nodup
    transs_eq_dec
    ex_transs. 

(* 3 arcs PT (place transition)  "incoming" *) 
Definition ex_pre_function (t : trans_type) (p : place_type)
  :=
  match (t, p) with
  | (mk_trans 0, mk_place 0) => Some 1
  | (mk_trans 1, mk_place 1) => Some 2
  | (mk_trans 2, mk_place 2) => Some 1
  | _ => None
  end.

(* 4 arcs TP                     "outcoming" *)
Definition ex_post_function (t : trans_type) (p : place_type)
  :=
  match (t, p) with
  | (mk_trans 0, mk_place 1) => Some 2
  | (mk_trans 0, mk_place 2) => Some 1
  | (mk_trans 1, mk_place 0) => Some 1
  | (mk_trans 2, mk_place 0) => Some 1
  | _ => None
  end.

(*** tokens of the initial marking ***)
Definition ex_initial_marking (p : place_type) :=
  match p with
  | mk_place 0 =>  2
  | mk_place 1 =>  0
  | mk_place 2 =>  0
  | _ => 0
  end. Print ex_initial_marking. Check marking_type.
(* ? reductions, simplifications ? *)

(* 1 arc of type "test" *)
Definition ex_pre_test_function (t : trans_type) (p : place_type) :=
  match (t, p) with
  | (mk_trans 2, mk_place 1) => Some 1
  | _ => None
  end.

(* 1 arc of type "inhibitor"  *)
Definition ex_pre_inhi_function (t : trans_type) (p : place_type) :=
  match (t, p) with
  | (mk_trans 1, mk_place 2) => Some 1
  | _ => None
  end.

(* disons   t_j prioritaire sur t_i   pour tout j >= i 
   " plus l'indice est grand, plus c'est prioritaire "  *)
(* faut-il un ordre strict ou large ? *)
Definition ex_priority (t1 t2 : trans_type) : bool :=
  (* transitions squared  ---> lot's of match branches ... *)
  match (t1 , t2) with
  | (mk_trans 0, mk_trans 0) => false
  | (mk_trans 0, mk_trans 1) => true
  | (mk_trans 0, mk_trans 2) => true
  | (mk_trans 1, mk_trans 0) => false
  | (mk_trans 1, mk_trans 1) => false
  | (mk_trans 1, mk_trans 2) => true
  | (mk_trans 2, mk_trans 0) => false
  | (mk_trans 2, mk_trans 1) => false
  | (mk_trans 2, mk_trans 2) => false
  | (_,_) => false  (* False or True     who care ? *) 
  end.

Print pre. Print weight_type.
Definition ex_pn := mk_PN
                      ex_places
                      ex_transs
                      ex_nodup_places
                      ex_nodup_transs
                      
                      ex_pre_function
                      ex_post_function
                      ex_pre_test_function
                      ex_pre_inhi_function                 
                      
                      ex_initial_marking
                      ex_priority.

Check ex_pn. Compute (marking ex_pn). (* initial marking good *)

Compute (animate_pn_list
           ex_pn
           10).

Compute (pn_is_enabled_because_look
           ex_pn). 
Compute (pn_is_enabled_because_look
           (fire_pn
              ex_pn)).
Compute (pn_is_enabled_because_look
           (fire_pn
              (fire_pn
                 ex_pn))).   (* ... *)


Compute (highest_transition
           ex_priority
           (pn_is_enabled_because_look
              ex_pn)).
Compute (highest_transition
           ex_priority
           (pn_is_enabled_because_look
              (fire_pn
                 ex_pn))).   (*  t_2 est prio sur t_0   *) 

Compute (fire_trans
           ex_pn
           (highest_transition
              ex_priority
              (pn_is_enabled_because_look
                 ex_pn))). 

(**********************************************************)
(* should I print the list of transitions 
   labelling this path of markings ?

should I print the list of enabled transitions at each step ?

(**** transitions can be _partitioned_ :
structural conflicts are _classes_ of transitions ***)

Some functions need to be done to have "nice" priorities  *)


(**********************************************************)



(*** interpreted Petri net ***)
Definition ex_conditions (t : trans_type) (c : gard_type)
  : bool
  := match (t, c) with
  | (mk_trans 0, mk_gard 0) => true
  | (mk_trans 2, mk_gard 1) => true
  | _ => false
  end.

Definition ipn_ex := mk_IPN
                       ex_pn
                       ex_conditions.





(*************************************************)
(**************** Syntax of SITPN ****************)

Print Between.  (** seems cool ! and cooler than what I can do **)
Record inter_type : Set := mk_inter
  { mini : nat ;
    maxi : nat ;
    min_le_max : mini <= maxi }.

                             
Definition caract_funct_inters :=
  trans_type -> inter_type -> bool.
(* temporal_transition_type t i = true   <=> C is associated with t *)


Record ITPN : Type := mk_ITPN
  { ipn : IPN;
    inters : caract_funct_inters }.
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
Definition ex2_places : (list place_type) :=
  [ mk_place 1 ;
    mk_place 2 ;
    mk_place 3 ;
    mk_place 4 ;
    mk_place 5 ;
    mk_place 6 ;
    mk_place 7 ].
Definition ex2_nodup_places : NoDup ex2_places :=
  NoDup_nodup
    places_eq_dec
    ex2_places. 

(* 6 transitions *)
Definition ex2_transs : (list trans_type) :=
  [ mk_trans 0 ;
    mk_trans 1 ;
    mk_trans 2 ;
    mk_trans 3 ;
    mk_trans 4 ;
    mk_trans 5 ;
    mk_trans 6 ].
Definition ex2_nodup_transs : NoDup ex2_transs :=
  NoDup_nodup
    transs_eq_dec
    ex2_transs. 

(* 7 arcs PT (place transition)  "incoming" *) 
Definition ex2_pre_function (t : trans_type) (p : place_type) :=
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
Definition ex2_pre_test_function (t : trans_type) (p : place_type) :=
  match (t, p) with
  | (mk_trans 1, mk_place 1) => Some 1
    (* place 1 needs (at least) 1 token, 
       which won't be taken by transition 1 *)
  | _ => None
  end.

(* 1 arc of type "inhibitor"  *)
Definition ex2_pre_inhi_function (t : trans_type) (p : place_type) :=
  match (t, p) with
  | (mk_trans 0, mk_place 1) => Some 1
  (* place 1 needs less than 1 token, 
     which won't be taken by transition 1 *)
  | _ => None
  end.

(* 7 arcs TP      "normal outcoming"  *)
Definition ex2_post_function (t : trans_type) (p : place_type) :=
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
Definition ex2_init_marking (p : place_type) :=
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

Definition ex2_conditions (t : trans_type) (c : gard_type) :=
  match (t, c) with
  | (mk_trans 1, mk_gard 1) => true
  | _ => false
  end.
  (* 1 condition/gard  :  Petri net influenced by environnement *)

Lemma preuve3le5 : 3 <= 5. Proof. omega. Qed.
Definition int1_35 := mk_inter
                        3
                        5
                        preuve3le5.
Print le.
Lemma preuve2le255 : 2 <= 255. Proof. omega. Qed.
Definition int1_2oo := mk_inter
                         2
                         255
                         preuve2le255.

Definition ex2_inters (t : trans_type) (i : inter_type) :=
  match (t, i) with
  | (mk_trans 3, int1_35) => true
  | (mk_trans 6, int1_2oo) => true
  | _ => false
  end.

Definition ex2_priority (t1 t2 : trans_type) : bool :=
  (* se restreindre aux conflits structurels !!!!!!!  *)
  match (t1 , t2) with
  | (mk_trans 0, mk_trans 0) => false
  | (mk_trans 0, mk_trans 1) => true
  | (mk_trans 0, mk_trans 2) => true
  | (mk_trans 1, mk_trans 0) => false
  | (mk_trans 1, mk_trans 1) => false
  | (mk_trans 1, mk_trans 2) => true
  | (mk_trans 2, mk_trans 0) => false
  | (mk_trans 2, mk_trans 1) => false
  | (mk_trans 2, mk_trans 2) => false
  | (_,_) => false  (* False or True     who care ? *) 
  end.
  
Definition itpn1 :=  mk_ITPN
                       (mk_IPN
                          (mk_PN
                              ex2_places
                              ex2_transs
                              ex2_nodup_places
                              ex2_nodup_transs
                              
                              ex2_pre_function
                              ex2_post_function
                              ex2_pre_test_function
                              ex2_pre_inhi_function
                              
                              ex2_init_marking
                              ex2_priority
                          )
                          ex2_conditions
                       )
                       ex2_inters.