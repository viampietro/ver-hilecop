(** * Types and functions used by the generateInfo function. *)

Require Import Coqlib.
Require Import sets.Sitpn.
Require Import NatSet.
Require Import ListsPlus.
Require Import ListsDep.
Require Import GenerateInfosInterface.
Require Import SetoidList.
Require Import InfosTypes.
Require Import GlobalTypes.
Require Import String.
Require Import Ascii.
  
Open Scope string_scope.

(** Given a proof that the list [transitions] contains elements of
      T, returns a couple of lists (inp, outp) where [inp] is the list
      of input transitions of [p], and [outp] the list of output
      transitions of [t].
      
      Remarks:

      - If there are duplicates in [transitions] then the returned lists
        possibly have duplicates.
        
      - If there are no duplicate, then the returned lists have no
        duplicate.

 *)

Fixpoint get_neighbours_of_p_aux sitpn
         (p : (P sitpn))
         (transs : list NatSet.elt)
         (inp : list (T sitpn))
         (outp : list (T sitpn * ArcT)) {struct transs} :
  incl transs (NatSet.this (transitions sitpn)) -> (list (T sitpn) * list (T sitpn * ArcT)) :=
  match transs with
  | nil => (fun _ => (inp, outp))
  | t :: tl =>
    (fun (pr : _) =>
       (* Existantial version of t of type {t | In t (this (transitions sitpn))} *)
       let tx := exist _ t (pr t (in_eq t tl)) in
       (* Proof that the tail of transs is included in (this (transitions sitpn)) *)
       let incltl := (incl_cons_inv t _ _ pr) in

       (* Adds transition t is the list of input or output transitions
            of [p] according to the arcs linking [p] and [t].
        *)
       match (post tx p), (pre p tx) with
       | Some _, Some (a, _) => get_neighbours_of_p_aux sitpn p tl (tx :: inp) ((tx, a) :: outp) incltl
       | Some _, None => get_neighbours_of_p_aux sitpn p tl (tx :: inp) outp incltl
       | None, Some (a, _) => get_neighbours_of_p_aux sitpn p tl inp ((tx, a) :: outp) incltl
       | None, None => get_neighbours_of_p_aux sitpn p tl inp outp incltl
       end
    )
  end.

(** Returns a couple of lists [(i, o)] where [i] is a list of input
      transitions of [p], and [o] is a list of couples [(o, a)] where
      [o] is an output transition of [p], and [a] is the arc type
      relating [p] to [o].

      Correctness: Correct iff all input transitions of [p] are [i],
      and [i] has no duplicates, and all output transitions of [p] are
      in [o] associated with the right arc type, and the list of first
      elements of [o] has no duplicate.

 *)

Definition get_neighbours_of_p (sitpn : Sitpn) (p : (P sitpn)) : optionE (list (T sitpn) * list (T sitpn * ArcT)) :=
  match get_neighbours_of_p_aux sitpn p (NatSet.this (transitions sitpn)) [] [] (incl_refl _) with
  | (nil, nil) => Err ("Place " ++ $$p ++ " is an isolated place.")
  | (inp, outp) => Success (inp, outp)
  end.

(** Returns a PlaceInfo structure containing the information related
      to place [p], a place of [sitpn].

      Error cases :
      
      - p is an isolated place, i.e it doesn't have neither input nor
        output transitions.

      - the priority relation is not a strict total order over the
        output transitions of t. 
 *)

Definition get_p_info sitpn (p : (P sitpn)) : optionE (PlaceInfo sitpn) :=

  (* Gets the input and output transitions list of place p.
     Raises an error if get_neighbours_of_p raises an error.
   *)
  match get_neighbours_of_p sitpn p with
  | Err msg => Err msg
  | Success (inp, outp) => Success (MkPlaceInfo _ inp outp)
  end.



