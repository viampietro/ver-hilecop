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

(** Injects the couple [c], where [c = (t,a)], in the list [stranss]
    depending on the level of priority of [t] compared to the first
    elements of the list [stranss].
    
    Returns the new priority-sorted list where [c] has been injected.

    Correctness hypotheses: (1) ~In t (fs stranss), (2) NoDup (fs
    stranss), (3) First elements of stranss are ordered by decreasing
    level of priority.

    Correct iff the returned has no duplicates and its first elements
    are ordered by decreasing level of priority. *)

Fixpoint inject_t sitpn
         (c : (T sitpn * ArcT))
         (stranss : list (T sitpn * ArcT)) {struct stranss} :
  optionE (list (T sitpn * ArcT)) :=
  let (t, _) := c in
  match stranss with
  (* If the list of priority-ordered transitions is empty, then
     returns a singleton list where t is the element with the highest
     priority. *)
  | [] => Success [c]

  (* If there is a head element, compares the head element with t
     priority-wise. *)
  | ((x, _) as c') :: tl =>

    (* If t and x are the same, then t has already been injected in
       stranss, then stranss is returned. That case does not happen
       given a proof of [~In t (fs stranss)], that is, t is not among 
       the first elements of stranss.

       Otherwise, checks if t has a higher firing priority than x.
     *)
    if eq_trans_dec t x then Success stranss                                     
    else
      (* If t is the element with the highest priority,then puts it as
         the head element of stranss. 
         
         Otherwise, checks if x has a higher priority than t.
       *)
      if t >~ x then Success (c :: stranss)
      else
        (* If x has a higher priority than t, then tries to inject t
           in the list's tail.  *)
        if x >~ t then
          match inject_t sitpn c tl with
          | Success stranss' => Success (c' :: stranss')
          (* Error case: found a transition that is not comparable with
             t is the list's tail.
           *)
          | Err msg => Err msg
          end
        else
          (* Error case: t >~ x and x >~ t evaluate to false. *)
          Err ("Transitions " ++ $$t ++ " and " ++ $$x ++ " are not comparable with the priority relation.")
  end.

(** Injects all transitions of the [transs] list in the list [stranss]
    that contains transitions sorted by level of firing priority.  *)

Fixpoint sort_by_priority_aux sitpn
         (transs : list (T sitpn * ArcT))
         (stranss : list (T sitpn * ArcT)) {struct transs} :
  optionE (list (T sitpn * ArcT)) :=
  match transs with
  | [] => Success stranss
  | c :: tl => match inject_t sitpn c stranss with
               | Success stranss' =>
                 sort_by_priority_aux sitpn tl stranss'
               | Err msg => Err msg
               end
  end.

(** Takes a list of couple [(t, a)] where [t] ∈ T and [a] is an arc
    type.
    
    Returns a new list of couple where the elements of the list are
    ordered on their first element by level of firing priority.

    Raises an error if no strict total ordering can be established in
    relation to the priority order.  *)

Definition sort_by_priority sitpn (transs : list (T sitpn * ArcT)) :
  optionE (list (T sitpn * ArcT)) := sort_by_priority_aux sitpn transs [].

(** Returns a PlaceInfo structure containing the information related
      to place [p], a place of [sitpn].

      Error cases :
      
      - p is an isolated place, i.e it doesn't have neither input nor
        output transitions.

      - the priority relation is not a strict total order over the
        output transitions of t. 
 *)

Definition get_p_info sitpn (p : (P sitpn)) : optionE (PlaceInfo sitpn) :=

  (* Gets the input and output transitions list of place p. *)
  match get_neighbours_of_p sitpn p with
  (* Error case: p is an isolated place. *)
  | Err msg => Err msg
  | Success (inp, outp) =>
    (* Sorts the output transitions of p by decreasing level of firing
       priority. *)
    match sort_by_priority sitpn outp with
    | Success soutp => Success (MkPlaceInfo _ inp soutp)
    (* Error case: the priority relation is not a strict total order
       over the output transitions of p.
     *)
    | Err msg => Err msg
    end
  end.

(** Computes informations for each place [p] that is an element
    of the list [pls] and adds the couple [(p, info)] to the list
    [placeInfos].
 *)

Fixpoint generate_place_infos_aux sitpn
         (pls : list NatSet.elt)
         (place_infos : list (P sitpn * PlaceInfo sitpn))
         {struct pls} :
  incl pls (NatSet.this (places sitpn)) -> optionE (list (P sitpn * PlaceInfo sitpn)) :=
  match pls with
  | [] => (fun _ => Success place_infos)
  | p :: tl => (fun pr : _ =>
                  (* Existantial version of p of type {p | In p (this (places sitpn))} *)
                  let px := exist _ p (pr p (in_eq p tl)) in
                  
                  (* Proof that the tail of places is included in (this (places sitpn)) *)
                  let incltl := (incl_cons_inv p _ _ pr) in

                  (* Computes the informations pertaining to place px. *)
                  match get_p_info sitpn px with
                  | Success pinfo =>
                    (* Adds the couple (px, pinfo) to the list and continues. *)
                    match generate_place_infos_aux sitpn tl ((px, pinfo) :: place_infos) incltl with
                    | Success pinfos => Success pinfos
                    (* Error case: recursive call generated an error. *)
                    | Err msg => Err msg
                    end
                  (* Error case: get_info_p generated an error. *)
                  | Err msg => Err msg
                  end
               )
  end.

(** Computes information for all p ∈ P, and returns the list of
    couples implementing function P → PlaceInfo. *)

Definition generate_place_infos (sitpn : Sitpn) : optionE (list (P sitpn * PlaceInfo sitpn)) :=
  generate_place_infos_aux sitpn (NatSet.this (places sitpn)) [] (incl_refl _).

