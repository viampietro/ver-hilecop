(** * Well-defined instances of Sitpn. *)

Require Import Coqlib.
Require Import dp.Sitpn.
Require Import dp.SitpnTypes.
Require Import NatSet.
Require Import GlobalTypes.
Require Import InfosTypes.
Require Import GenerateInfos.
Require Import String.
Require Import HexString.
Require Import StateAndErrorMonad.

Import ErrMonadNotations.

Open Scope string_scope.

Set Implicit Arguments.

Local Notation "[ e ]" := (exist _ e _).

(** ** An simple instance of [Sitpn]. *)

Definition places_simpl := [ 0; 1; 2].
Definition transs_simpl := [ 0; 1; 2 ].
Definition Psimpl := { p | List.In p places_simpl }.
Definition Tsimpl := { t | List.In t transs_simpl }.

Definition p0 : Psimpl. refine ([0]); simpl; tauto. Defined.
Definition p1 : Psimpl. refine ([1]); simpl; tauto. Defined.

(* Input arcs function. *)

Definition pre_simpl (p : Psimpl) (t : Tsimpl) : option (ArcT * natstar) :=
  match p, t with
  | [0], [0] => Some (basic, onens)
  | [1], [0] => Some (basic, onens)
  | [1], [1] => Some (basic, onens)
  | [2], [0] => Some (basic, onens)
  | [2], [1] => Some (basic, onens)
  | [2], [2] => Some (basic, onens)
  | _, _ => None
  end.

(* Priority relation function *)

Definition prio_simpl :=
  fun t t' : Tsimpl =>
    match t, t' with
    | [0], ([2] | [1])
    | [2], [1] => true
    | _, _ => false
    end.

(* SITPN structure *)

Example sitpn_simpl :=
  @BuildSitpn
    places_simpl
    transs_simpl
    pre_simpl
    (fun t p => None)
    (fun p => 0)
    (fun t => None)
    [ 30; 31; 32 ]
    [ 10; 11; 12 ]
    [ 60; 61; 62 ]
    (fun t c => mone)
    (fun p a => true)
    (fun t f => false)
    prio_simpl.

(* Initial SitpnInfo structure *)

Definition init_infos sitpn := MkSitpnInfo sitpn [] [] [] [] [].

Compute RedS (generate_sitpn_infos sitpn_simpl (init_infos sitpn_simpl)).
