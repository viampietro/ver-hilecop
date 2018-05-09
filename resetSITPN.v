(*************************************************************)
(**** by Mathieu Lasjaunias, David Delahaye, David Andreu ****)
(*************************************************************)

Require Import Arith Omega List Bool. (* best libraries ever *) 
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
(*  Why not this inductive definition with 4 constructors ????
Inductive arc_type : Set :=
| mk_arc_pt : place_type -> transition_type -> nat -> arc_type
| mk_arc_tp : transition_type -> place_type -> nat -> arc_type
(* extended (generalized = nat) Petri nets *)
| mk_arc_inhi : place_type -> transition_type -> nat -> arc_type
| mk_arc_test : place_type -> transition_type -> nat -> arc_type.
 *)

Definition marking_type := place_type -> nat.

(***  priority relation     
  to DETERMINE the Petri net 
  (along with imperative semantic) ***)
Require Import Relations. Print relation. 
Search relation. Print transitive.
Inductive prior_type : Set :=
  mk_prior_type :  forall (rel : trans_type -> trans_type -> bool),
    (forall (x : trans_type), (rel x x) = false) -> (* irreflexive *)
    (forall (x y : trans_type), (rel x y) = true -> (* asymmetric *)
                                (rel y x = false)) ->
    (forall (x y z : trans_type), (rel x y) = true -> (* transitive *)
                                  (rel y z) = true ->
                                  (rel x z) = true) ->
    prior_type.

Print prior_type. (* 1 big constructor *)
Definition prio_over
           (t1 t2 : trans_type)
           (prior : prior_type)
  : bool :=
  match prior with
  | mk_prior_type
      rel
      asymm
      irref
      trans => if rel t1 t2
               then true
               else false
  end.
Notation "t1 >> t2" := (prio_over t1 t2 _)
                          (at level 50) : type_scope.
(*** but for wich prior ?   is this notation correct ? ***)

(* conditions  on transitions *)
Inductive cond_type : Set :=
| mk_cond : nat -> cond_type.

Definition caract_funct_gards := trans_type -> cond_type -> bool.
(* condition_type t g = true     <=>     g is associated with t *)

Notation "cond [ trans ]" := (caract_funct_gards
                                trans
                                cond)  
                               (at level 50) : type_scope.
(* a (probably useless example of notation ... *)
Print Between.

(** "Structure" = "Record" **) 
Structure SITPN : Type := mk_SITPN
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
                        
                        priority : prior_type ;
                        
                        conds : trans_type -> list cond_type ;

                        local_clocks : trans_type -> option nat ;
                        intervals : trans_type -> option (nat * nat)
                      (* between don't works ! why ? *)}.
Print SITPN.

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
   library "Nat" is included into "Arith" ...   not clear but ... *)

Locate "<?". Print Nat.ltb. Print Nat.leb.
Print pre. Print weight_type.
(**** uphill (input set, preset) ***)
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
(**** downhill (output set, postset) ***)
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

(*************  "enabled" iff 
"arcs_classic" + "arcs_test" + "arcs_inhi" satisfied *************)
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
Fixpoint enabled_transs_aux
         (sitpn : SITPN)
         (l : list trans_type) {struct l}
         (* structural induction over list of transitions *) :
  list trans_type :=
  match l with
  | nil => nil
  | cons t tail => if (pn_trans_is_enabled
                         (places    sitpn)
                         (pre       sitpn)
                         (pre_test  sitpn)
                         (pre_inhi  sitpn)  
                         (marking   sitpn)
                         t)
                   then cons t (enabled_transs_aux
                                  sitpn
                                  tail)
                   else enabled_transs_aux
                          sitpn
                          tail
  end.
(*** for a Petri net, return the list of enabled transitions ***)
Definition enabled_transs (sitpn : SITPN)
  : list trans_type :=
  enabled_transs_aux
    sitpn
    (transs sitpn).

(**************** enabled is no firable *************************)
Import ListNotations.
Definition eval_cond (c : cond_type) : bool := true.

Fixpoint conds_firable_trans_aux
           (t : trans_type)
           (con : list cond_type)
  : bool :=
  match con with
  | []  => true
  | c :: tail => (eval_cond c)
                   && (conds_firable_trans_aux
                         t
                         tail)
  end.

Definition conds_firable_trans
           (t : trans_type)
           (conds : trans_type -> list cond_type)
  : bool :=
  conds_firable_trans_aux
    t 
    (conds t). 

Print SITPN.
Definition inter_firable_trans
           (t : trans_type)
           (local_clocks : trans_type -> option nat)
           (intervals : trans_type -> option (nat * nat))
  : bool :=
  match (intervals t) with
  | None  => true
  | Some (a,b) => match (local_clocks t) with
                  | None => (* impossible pardi *) false
                  | Some x => if (a <=? x)
                                   &&
                                   (x <=? b)
                              then true
                              else false
                  end
  end.

Definition firable_trans
           (t : trans_type)
           (conds : trans_type -> list cond_type)
           (local_clocks : trans_type -> option nat)
           (intervals : trans_type -> option (nat * nat))
            : bool :=
  (conds_firable_trans
     t
     conds)
    &&
    (inter_firable_trans
       t
       local_clocks 
       intervals).

(*** for a Petri net, return the list of enabled transitions ***)
(***** just throwing away transitions not "enabled" *)
Fixpoint firable_transs
         (sitpn : SITPN)
         (enabled_trans : list trans_type)
  : list trans_type :=
  match enabled_trans with
  | [] => []
  | t :: tail => if firable_trans
                      t
                      (conds sitpn)
                      (local_clocks sitpn)
                      (intervals sitpn)
                 then t :: (firable_transs
                              sitpn
                              tail)
                 else (firable_transs
                         sitpn
                         tail)
  end.

(************************************)
Fixpoint update_marking_pre
         (l : list place_type)
         (t : trans_type)
         (pre : weight_type)
         (m : marking_type)
         {struct l}
  (* structural induction over list of places *)
  : marking_type :=
  match l with
  | nil => m
  | cons p tail => update_marking_pre
                     tail
                     t
                     pre
                     (modif_mark
                           m
                           p
                           (pre t p)
                           Nat.sub)
  end.

Fixpoint update_marking_post
         (l : list place_type) 
         (t : trans_type)
         (post : weight_type)
         (m : marking_type)         
  (* structural induction over list of places *)
  : marking_type :=
  match l with
  | nil => m
  | cons p tail => update_marking_post
                     tail
                     t
                     post
                     (modif_mark
                           m
                           p
                           (post t p)
                           Nat.add)
  end.

Definition update_marking
           (P : list place_type) 
           (t : trans_type)
           (pre post : weight_type)
           (m : marking_type)         
  (* structural induction over list of places *)
  : marking_type :=
  update_marking_post
    P  
    t
    post
    (update_marking_pre
       P 
       t
       pre
       m).

(* fire transition t, only updating the marking of the Petri net ! *)
Definition fire_one_trans
           (sitpn : SITPN)
           (t:trans_type)
  : SITPN  :=
  mk_SITPN
    (places sitpn)
    (transs sitpn)
    (nodup_places sitpn)
    (nodup_transitions sitpn)
    (pre sitpn)
    (post sitpn)
    (pre_test sitpn)
    (pre_inhi sitpn)
    (update_marking
       (places sitpn)
       t
       (pre sitpn) (post sitpn)
       (marking sitpn))
    (priority sitpn)
    (conds sitpn)
    (local_clocks sitpn)
    (intervals sitpn).

Fixpoint fire_many_transs
           (sitpn : SITPN)
           (to_be_fired : list trans_type)
  : SITPN :=
  match to_be_fired with
  | nil => sitpn
  | t :: tail  => fire_many_transs
                    (fire_one_trans
                       sitpn
                       t)
                    tail
  end.

(***********************************************)

Section structural_conflicts.
  Variable pre : weight_type.
  (* Variable places : list place_type. *)

  Fixpoint common_pre
           (t t' : trans_type)
           (places : list place_type)
    : bool :=
    match places with
    | [ ] => false
    | p :: places' => match ((pre t p), (pre t' p)) with
                      | (Some _, Some _) => true
                      | (_, _) => common_pre
                                    t t'
                                    places'                                  
                      end
    end.

  Fixpoint common_pre_with_somebody
           (t : trans_type) (sometranss : list trans_type)
           (places : list place_type)
    : bool :=
    match sometranss with
    | [ ] => false
    | tr :: lesstranss => if common_pre
                               t tr
                               places
                          then true
                          else common_pre_with_somebody
                                 t lesstranss
                                 places
    end.

  Fixpoint somebody_common_pre_with_somebody
           (sometranss1 sometranss2 : list trans_type)
           (places : list place_type)
    : bool :=
    match sometranss1 with
    | [ ] => false
    | t :: lesstranss1 => if common_pre_with_somebody
                               t sometranss2
                               places
                          then true
                          else somebody_common_pre_with_somebody
                                 lesstranss1 sometranss2
                                 places
  end.    

  Search list.
  Section fusionning_lists.
    Variables (A : Type).
    
    Fixpoint fusion_two_lists
             (L : list (list A))
             (l1 l2 : list A)
      (* l1 , l2  in L *)
      : list (list A) :=
      (*match L with
    | l1 :: L'  => fusion_two_lists
                     L'
                     l1 l2
    | l2 :: L'  => fusion_two_lists
                     L'
                     l1 l2
    | _ :: L'   => fusion_two_lists
                     L
                     l1 l2
    | [ ]      => (l1 ++ l2) :: L 
    end.*)
      [].
  End fusionning_lists.
  
  Fixpoint merging_list_in_list_of_lists
           (L : list (list trans_type))      
           (sometranss1 : list trans_type)
           (places : list place_type) {struct L}
    : list (list trans_type) :=
    match L with
    | [] => L
    | sometranss2 :: L' => if somebody_common_pre_with_somebody
                                sometranss1 sometranss2
                                places
                           then ((sometranss1 ++ sometranss2) :: L')
                                  
                           else sometranss2 :: (merging_list_in_list_of_lists
                                                  L'
                                                  sometranss1
                                                  places)
  end.

  Definition building_structural_conflicts
             (transs : list (list trans_type))
             (places : list place_type)
    : list (list trans_type) :=
    match transs with
    | []  => transs
    | l :: tail  => merging_list_in_list_of_lists
                      tail
                      l
                      (places : list place_type)
    end.

End structural_conflicts.

Section effective_conflicts.
  Variable struct_conflicts : list (list trans_type).
  Variable firable_transs : list trans_type.

  Fixpoint conforming_data_pruning
           (struct_conflicts : list (list trans_type))
           (firable_transs : list trans_type)
    : list (list trans_type) :=
    [].
  (* il suffit de garder de struct_conflicts
  en supprimant toutes les transitions n'apparaissant pas dans firable_transs *)

  Print SITPN.
  Fixpoint conforming_data_ordering
           (firable_transs : list (list trans_type)) (* better *)
           (priority : prior_type)
    : list (list trans_type) :=
    [].
  (* il suffit d'ordonner chacune des listes *)


  Definition to_be_fired
             (conformed_firable : list (list trans_type))
             (sitpn : SITPN)
    : SITPN :=
    sitpn.
  (* on peut tirer les transitions autant que possible 
 il suffit de tirer les premières de listes (updating le marking)
en retirant les transitions suivantes qui ne sont plus tirables
 
et en recommançant avec la liste de listes restante
qui n'est pas forcement plus courte (bordel !) *)

  
End effective_conflicts.





