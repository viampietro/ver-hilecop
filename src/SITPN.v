(***********************)
(**** by ML, DD, DA ****)
(***********************)

Require Import Arith Omega List Bool.
(* Require Import Nat. *)
Search nat. Search list.

(*********************************************************)
(***** Syntax of (generalized, extended) Petri nets ******)

Inductive locat_type : Set :=
| mk_locat : nat -> locat_type.
(* places indexed by natural numbers *)

Inductive trans_type : Set :=
| mk_trans : nat -> trans_type.
(* transitions indices and constructor *)

(*   4 "TYPES" of arcs : pred, post, pred_inhib, pred_test 
    along with "some" weight   (default is 1 in real).       *)

Structure posi_type : Set := mk_posi
                              { int : nat ;
                                posit : int > 0 }.
(* a given arc has some weight >= 1 *)
Definition weight_type := trans_type ->
                          locat_type ->
                          option posi_type.
(*  Why not this inductive definition with 4 constructors ????
Inductive arc_type : Set :=
| mk_arc_pt : place_type -> transition_type -> nat -> arc_type
| mk_arc_tp : transition_type -> place_type -> nat -> arc_type
(* extended (generalized = nat) Petri nets *)
| mk_arc_inhi : place_type -> transition_type -> nat -> arc_type
| mk_arc_test : place_type -> transition_type -> nat -> arc_type.
 *)

Definition marking_type := locat_type -> nat.

(*****************************************************************)
(***  priority relation  ..................................   
  to DETERMINE the Petri net (along with imperative semantic) ***)

Definition prior_type := list (list trans_type).
    (*
      no_inter :
        forall (l1 l2 : list trans_type),
        forall (x : trans_type),
          (In l1 list_lists) -> (In l2 list_lists) ->
          (In x l1) -> (In x l2) ->
          (l1 = l2) ;  }.
  cover :
       forall (x : trans_type),
         (In x transs) ->
         exists (l : list trans_type),
           (In x l) -> (In l list_lists) }. *)


(****************************************************************)
Print NoDup. Print nodup. Print NoDup_nodup. (* opaque proof ? *)
Print find_some.  (* maybe useful *)
(* split  / combine   ... *)

(*************************************************************)
(********* intervals of time...   for Time Petri nets  *******) 

Structure chrono_type : Set :=
  mk_chrono
    {
      mini : nat  ; (* no [0, . ] in _S_TPN ! *)
      maxi : nat ;
      min_leb_max : mini <= maxi  ;
      cpt  : nat ;   (* possibly 0   /!\  *)
      (* in_range  : bool      mini <= cpt <= maxi 
sumbool ? ; *)
    }.

Print "<=?".

Definition eval_chronos_type := trans_type -> option chrono_type.

(**************************************************************)
(* conditions  on transitions...   for Interpreted Petri nets *)

(*
Inductive cond_type : Set :=
| mk_cond : nat -> cond_type. *)

(*** conditions are evolving through time 
   scenario/scenari 
some transitions of a Petri net are given conditions
which have a boolean value  ****)

(***  a list of size n allows one to compute up to n cycles  ***) 

Definition eval_conds_type := trans_type -> option bool.
(* some transitions (+ transitions not inside the Petri net)
don't have any condition at all *)

Definition scenar_type := list eval_conds_type.



Structure SITPN : Set := mk_SITPN
                           { 
                             locats : list locat_type ;
                             transs : list trans_type ;
                             nodup_places : NoDup locats ;
                             nodup_transitions : NoDup transs ;
                             
                             pre : weight_type ;
                             post : weight_type ;
                             
                             test : weight_type ;
                             inhib : weight_type ;
                             
                             marking : marking_type ;

                             priority : prior_type ;

                             chronos : eval_chronos_type ;

                             scenario : scenar_type
                           }.



(*** interpreted Petri net ***)
Definition ex_eval_conds_cycle1 (t : trans_type)
  : option bool :=
  match t with
  | mk_trans 0  => Some true
  | mk_trans 2  => Some false
  | _ => None
  end.
Definition ex_eval_conds_cycle2 (t : trans_type)
  : option bool :=
  match t with
  | mk_trans 0  => Some true
  | mk_trans 2  => Some true
  | _ => None
  end.
Definition ex_eval_conds_cycle3 (t : trans_type)
  : option bool :=
  match t with
  | mk_trans 0  => Some true
  | mk_trans 2  => Some true
  | _ => None
  end.

Import ListNotations.
Definition ex_scenar := [ex_eval_conds_cycle1 ;
                           ex_eval_conds_cycle2 ;
                           ex_eval_conds_cycle3 ].

  
Definition sitpn_ex := mk_SITPN
                         ex_pn
                         ex_conditions.







(***************************************************************)
(**************** "firable" is stronger than "enabled" *********)
(********************** conditions & intervals *****************)


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





Print SITPN. Print time_interval_type. Print nat_star.
Definition inter_firable_trans
           (t : trans_type)
           (intervals : trans_type -> option time_interval_type)
  : bool :=
  match (intervals t) with
  | None  => true
  | Some inter => match inter with
                  | mk_inter
                      mini
                      maxi
                      min_le_max
                      cpt => (*match (mini, maxi) with
                             | (mk_nat_star
                                  inta
                                  carea,
                                mk_nat_star
                                  intb
                                  careb) =>*) if (mini <=? cpt)
                                                   &&
                                                   (cpt <=? maxi)
                                              then true
                                              else false
                  end
                                
  end.



(* conditions + intervals *)
Definition firable_trans
           (t : trans_type)
           (conds : trans_type -> list cond_type)
           (intervals : trans_type -> option time_interval_type)
            : bool :=
  (conds_firable_trans
     t
     conds)
    &&
    (inter_firable_trans
       t
       intervals).
