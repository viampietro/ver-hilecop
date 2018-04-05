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

Record PN : Type := Build_PN
                      { place : place_type -> Prop ;
                        transition : transition_type -> Prop ;
                        pre : weight_type ;
                        post : weight_type ;
                        init_marking : marking_type }.
Print PN.

(* predecessor, successor ... to update the marking *)
Definition place_before_trans (t:transition_type) (p:place_type) : Prop :=
  False.

Definition place_after_trans (t:transition_type) (p:place_type) : Prop :=
  False.

Definition firable (m:marking_type) (t:transition_type) : Prop :=
  False.

Definition marking_after (m:marking_type) (t:transition_type) (p : firable m t) : marking_type :=
  m.  

(******************************************************************)
Parameter conds : Set.  (* conditions over transitions *)
Parameter c : conds.
Definition condition_type :=
  transition_type -> conds -> bool.
(* condition_type t C = true     <=> C is associated with t *)
(* Instead of "bool", "Prop" is possible...  (-> binary predicate) *)
Notation "cond [ trans ]" := (condition_type trans cond = true)  
                               (at level 50) : type_scope. (* ? *)
(* difference between Notation and Infix ? *)
Record IPN : Type := Build_IPN
                       { pn :> PN ;
                         pre_test : weight_type ;
                         pre_inhibit : weight_type ;
                         cond : condition_type }.
Print IPN.

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


(*************************************************************)
(******* example 0 (page 24 in Ibrahim thesis) *********)

(* 3 places *)
Definition place0 (p : place_type) :=
  match p with
  | mk_place 0 => True
  | mk_place 1 => True
  | mk_place 2 => True
  | _ => False
  end.

(* 3 transitions *)
Definition transition0 (t : transition_type) :=
  match t with
  | mk_trans 0 => True
  | mk_trans 1 => True
  | mk_trans 2 => True
  | _ => False
  end.

(* 3 arcs PT (place transition) 
 "incoming" : transition pivot   ;   "outcoming" : place pivot *) 
Definition pre0 (t : transition_type) (p : place_type) :=
  match (t, p) with
  | (mk_trans 0, mk_place 0) => Some 1
  | (mk_trans 1, mk_place 1) => Some 2
  | (mk_trans 2, mk_place 2) => Some 1
  | _ => None
  end.

(* 4 arcs TP *)
Definition post0 (t : transition_type) (p : place_type) :=
  match (t, p) with
  | (mk_trans 0, mk_place 1) => Some 2
  | (mk_trans 0, mk_place 2) => Some 1
  | (mk_trans 1, mk_place 0) => Some 1
  | (mk_trans 2, mk_place 0) => Some 1
  | _ => None
  end.

(* tokens *)
Definition init_marking0 (p : place_type) :=
  match p with
  | mk_place 0 => Some 1
  | mk_place 1 => Some 2
  | mk_place 2 => Some 1
  | _ => None
  end.

(* 1 arc of type "test" *)
Definition pre_test0 (t : transition_type) (p : place_type) :=
  match (t, p) with
  | (mk_trans 2, mk_place 1) => Some 1
  | _ => None
  end.

(* 1 arc of type "inhibitor"  *)
Definition pre_inhibit0 (t : transition_type) (p : place_type) :=
  match (t, p) with
  | (mk_trans 1, mk_place 2) => Some 1
  | _ => None
  end.

Definition cond0 (t : transition_type) (c : conds) := false.
(* no conditions in this Petri Net (and no actions of functions)
 ---> reseaux de Petri generalise etendu, mais pas interprete *)

Definition ints0 (t : transition_type) (i : interval_type) := false.
(* no conditions in this Petri Net (and no actions of functions)
 ---> reseaux de Petri generalise etendu, mais pas interprete *)

Definition itpn0 := mk_ITPN
                       (Build_IPN
                          (Build_PN
                             place0
                             transition0
                             pre0
                             post0
                             init_marking0)
                          pre_test0
                          pre_inhibit0
                          cond0)
                       ints0.
                       



(*****************************************************************)
(* example 1 (drawn by David Andreu, then built in VHDL) *)

(* 7 places *)
Definition place1 (p : place_type) :=
  match p with
  | mk_place 0 => True
  | mk_place 1 => True
  | mk_place 2 => True
  | mk_place 3 => True
  | mk_place 4 => True
  | mk_place 5 => True
  | mk_place 6 => True
  | _ => False
  end.

(* 6 transitions *)
Definition transition1 (t : transition_type) :=
  match t with
  | mk_trans 0 => True
  | mk_trans 1 => True
  | mk_trans 2 => True
  | mk_trans 3 => True
  | mk_trans 4 => True
  | mk_trans 5 => True
  | _ => False
  end.

(* 7 arcs PT (place transition) 
 "incoming" : transition pivot   ;   "outcoming" : place pivot *) 
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

(* 7 arcs TP    *)
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
  (* 1 condition donc influence de l'environnement donc
---> reseaux de Petri generalise etendu interprete IPN *)

Lemma preuve3le5 : 3 <= 5. Proof. auto. Qed.
Definition int1_35 := Build_interval_type
                     3
                     5
                     preuve3le5.
Print le.
Lemma preuve2le255 : 2 <= 255. Proof. repeat (apply le_S; try apply le_n). Qed.
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

Definition itpn1 :=  Build_ITPN
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