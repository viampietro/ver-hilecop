(** * Types and functions used by the generateInfo function. *)

Require Import Coqlib.
Require Import ArcT.
Require Import sets.Sitpn.
Require Import NatSet.
Require Import ListsPlus.
Require Import ListsDep.
Require Import InfosTypes.
Require Import GenerateInfosInterface.

Module GenerateInfosImplFun <: GenerateInfosFun.

  Fixpoint get_in_transs_aux (sitpn : Sitpn) (p : (P sitpn)) (transs : list NatSet.elt) {struct transs} :
    incl transs (NatSet.this (transitions sitpn)) -> list (T sitpn) :=
    match transs with
    | nil => (fun _ => nil)
    | t :: tl =>
      (fun (pr : _) =>
         (* Existantial version of t of type {t | In t (this (transitions sitpn))} *)
         let tex := exist _ t (pr t (in_eq t tl)) in
         (* Proof that the tail of transs is included in (this (transitions sitpn)) *)
         let incltl := (incl_cons_inv t _ _ pr) in
         (* Filter expression to select t as an input transition of p. *)
         let is_intrans_of_p := (fun t => (0 <? (pre p t)) || (0 <? (test p t)) || (0 <? inhib p t)) in

         (* If tex passes the test then adds it to the returned list. 
            Otherwise tex is not selected.
          *)
         if is_intrans_of_p tex then tex :: get_in_transs_aux sitpn p tl incltl
         else get_in_transs_aux sitpn p tl incltl
      )
    end.

  Definition get_in_transs (sitpn : Sitpn) (p : (P sitpn)) : list (T sitpn) :=
    get_in_transs_aux sitpn p (NatSet.this (transitions sitpn)) (incl_refl _).
  
  Definition get_p_info (sitpn : Sitpn) (p : (P sitpn)) : PlaceInfo sitpn :=

    (* Gets the list of input transitions of place p. *)
    let p_in_transs := get_in_transs sitpn p in MkPlaceInfo _ p_in_transs nil.
  
End GenerateInfosImplFun.

