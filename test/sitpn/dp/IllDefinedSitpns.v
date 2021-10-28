(** * Ill-defined instances of Sitpn. *)

Require Import CoqLib.
Require Import sitpn.Sitpn.
Require Import sitpn.SitpnTypes.
Require Import NatSet.
Require Import GlobalTypes.
Require Import GenerateInfos.
Require Import String.
Require Import HexString.

Open Scope string_scope.

Set Implicit Arguments.

Local Notation "[ e ]" := (exist _ e _).

(** ** An [Sitpn] instance with an empty list of transitions. *)

Example sitpn_emp_transs :=
  @BuildSitpn
    [ 0; 1; 2 ]
    [ ]
    (fun p t => None)
    (fun t p => None)
    (fun p => 0)
    (fun t => None)
    [ ]
    [ ]
    [ ]
    (fun t c => zero)
    (fun p a => false)
    (fun t f => false)
    (fun t t' => False).

Definition prio_emp_transs_dec : forall x y : T sitpn_emp_transs, {x >~ y} + {~x >~ y}. auto. Defined.

(** ** An [Sitpn] instance with isolated places. *)

Definition places_iso_pls := [ 0; 1; 2 ].
Definition transs_iso_pls := [ 0; 1; 2 ].
Definition Piso := { p | List.In p places_iso_pls}.
Definition Tiso := { t | List.In t transs_iso_pls}.

(* Input arcs function. Here, place 2 is isolated. *)

Definition pre_iso_pls (p : Piso) (t : Tiso) : option (ArcT * natstar) :=
  match p, t with
  | [0], [0] => Some (basic, onens)
  | [1], [0] => Some (basic, onens)
  | [1], [1] => Some (basic, onens)
  | _, _ => None
  end.

Example sitpn_iso_pls :=
  @BuildSitpn
    places_iso_pls
    transs_iso_pls
    pre_iso_pls
    (fun t p => None)
    (fun p => 0)
    (fun t => None)
    [ ]
    [ ]
    [ ]
    (fun t c => zero)
    (fun p a => false)
    (fun t f => false)
    (fun t t' => False).

Definition prio_iso_pls_dec : forall x y : T sitpn_iso_pls, {x >~ y} + {~x >~ y}. auto. Defined.

Require Import sitpn2hvhdl.GenerateHVhdl.

(* Compute (sitpn_to_hvhdl sitpn_iso_pls prio_iso_pls_dec 0 0 1). *)
