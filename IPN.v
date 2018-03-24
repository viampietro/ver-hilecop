Inductive place_type : Set :=
| mk_place : nat -> place_type.
(* place number 0, place number 1, ... , place number 255, ... *)

Inductive transition_type : Set :=
| mk_trans : nat -> transition_type.
(* transition number 0, transition number 1, ... *)

Definition weight_type :=
  transition_type -> place_type -> option nat.
(* weight of any "type" of arc (pred, post, pred_i, pred_t), 
if any weight. *)

Definition marking_type := place_type -> option nat.
(* a marking is a function. How many tokens for each place ?
Partial vs Total functions *)
 
Parameter conds : Set.  (* conditions *)
Parameter C : conds.
Definition condition_type := transition_type -> conds -> Prop.
(* condition_type t C = True   <=> C is associated with t *)
(* Instead of "Prop", "bool" is possible *)

Record itpn : Type := mk_itpn {
                          place : place_type -> Prop ;
                          transition : transition_type -> Prop ;
                          pre : weight_type ;
                          pre_test : weight_type ;
                          pre_inhibit : weight_type ;
                          post : weight_type ;
                          init_marking : marking_type ;
                          cond : condition_type
                                   (* time Petri net, TO DO *)
                        }.

(*************************************************************)
(******* example 0 (page 20 or so in Ibrahim thesis) *********)

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

Definition cond0 (t : transition_type) (c : conds) := False.
(* no conditions in this Petri Net (and no actions of functions)
 ---> reseaux de Petri generalise etendu, mais pas interprete *)

Definition itpn0 :=  mk_itpn
                       place0
                       transition0
                       pre0
                       pre_test0
                       pre_inhibit0
                       post0
                       init_marking0
                       cond0.


(*****************************************************************)
(* example 1 (drawn by David Andreu, built in VHDL by Baptiste Colombani) *)

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
  | (mk_trans 1, C) => True
  | _ => False
  end.
  (* 1 condition donc influence de l'environnement donc
---> reseaux de Petri generalise etendu interprete IPN *)

Definition itpn1 :=  mk_itpn
                       place1
                       transition1
                       pre1
                       pre_test1
                       pre_inhibit1
                       post1
                       init_marking1
                       cond1.
