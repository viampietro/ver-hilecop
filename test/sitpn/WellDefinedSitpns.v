(** * Well-defined instances of Sitpn. *)

Require Import CoqLib.
Require Import sitpn.Sitpn.
Require Import sitpn.SitpnTypes.
Require Import GlobalTypes.
Require Import String.

Import ErrMonadNotations.

Set Implicit Arguments.

Open Scope string_scope.

Local Notation "[ e ]" := (exist _ e _).

(** ** An simple instance of [Sitpn]. *)

Definition places_simpl := [ 0; 1; 2].
Definition transs_simpl := [ 1; 0; 2 ].
Definition conds_simpl := [ 30; 31; 32 ].

Definition Psimpl := { p | List.In p places_simpl }.
Definition Tsimpl := { t | List.In t transs_simpl }.
Definition Csimpl := { c | List.In c conds_simpl }.

Definition p0 : Psimpl. refine ([0]); simpl; tauto. Defined.
Definition p1 : Psimpl. refine ([1]); simpl; tauto. Defined.
Definition t0 :Tsimpl. refine ([0]); simpl; tauto. Defined.
Definition t1 :Tsimpl. refine ([1]); simpl; tauto. Defined.
Definition t2 : Tsimpl. refine ([2]); simpl; tauto. Defined.
Definition c0 : Csimpl. refine ([30]); simpl; tauto. Defined.
Definition c1 : Csimpl. refine ([31]); simpl; tauto. Defined.
Definition c2 : Csimpl. refine ([32]); simpl; tauto. Defined.

(* Input arcs function 
   
   Mutual exclusion between [t0] and [t1] by inhibitor arc.
 *)

Definition pre_simpl (p : Psimpl) (t : Tsimpl) : option (ArcT * natstar) :=
  match p, t with
  | [0], [0] => Some (basic, onens)
  | [0], [1] => Some (inhibitor, onens)
  | [1], [0] => Some (basic, onens)
  | [1], [1] => Some (basic, onens)
  | [2], [0] => Some (basic, onens)
  | [2], [1] => Some (basic, onens)
  | [2], [2] => Some (basic, onens)
  | _, _ => None
  end.

(* Time intervals
   
   Mutual exclusion between [t1] and [t2] by disjoint time intervals
 *)

Definition Is_simpl (t : Tsimpl) : option TimeInterval :=
  match t with
  | [1] => Some it12
  | [2] => Some it12
  | _ => None
  end.

(* Condition associations

   Mutual exclusion between [t0] and [t2] by compl. conditions.  *)

Definition has_C_simpl (t : Tsimpl) (c : Csimpl) : MOneZeroOne :=
  match t, c with
  | [0], [30] => one 
  | [2], [30] => mone
  | _, _ => zero
  end.

(* Priority relation function *)

Definition prio_simpl :=
  fun t t' : Tsimpl =>
    match t, t' with
    | [2], ([1] | [0]) | [1], [0] => True
    | _, _ => False
    end.

(* SITPN structure *)

Example sitpn_simpl :=
  @BuildSitpn
    places_simpl
    transs_simpl
    pre_simpl
    (fun t p => None)
    (fun p => 0)
    Is_simpl
    conds_simpl
    [ 10; 11; 12 ]
    [ 60; 61; 62 ]
    has_C_simpl
    (fun p a => true)
    (fun t f => true)
    prio_simpl.

(* Decidability of priority relation *)
Require Import SitpnInstancesTactics.

Definition prio_simpl_dec : forall x y : Tsimpl, {prio_simpl x y} + {~prio_simpl x y}.
  decide_prio_dec. 
Defined.



