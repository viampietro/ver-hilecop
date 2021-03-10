(** * Implementation of [Sitpn] instance example 1 *)

Require Import common.CoqLib.
Require Import common.GlobalTypes.
Require Import common.GlobalFacts.
Require Import sitpn.dp.Sitpn.
Require Import sitpn.dp.SitpnTypes.
Require Import test.sitpn.dp.SitpnInstancesTactics.

Local Notation "[ e ]" := (exist _ e _).

(** Set of places *)

Definition WforSensorOn := 0.
Definition WafterAnswer := 1.
Definition UniqueQuery := 2.
Definition WforQuery := 3.
Definition CycleCt := 4.
Definition Wafterfoo := 5.
Definition WforAnswer := 6.
Definition Query := 7.
Definition ComputeAfterQuery := 8.
Definition LogError := 9.
Definition ComputeAfterSOn := 10.
Definition ComputeAfterAns := 11.
Definition CheckStatus := 12.

Definition places1 := [WforSensorOn; WafterAnswer; UniqueQuery; WforQuery;
                      CycleCt; Wafterfoo; WforAnswer; Query; ComputeAfterQuery;
                      LogError; ComputeAfterSOn; ComputeAfterAns; CheckStatus].

Definition P1 := { p | List.In p places1 }.

(* Set of transitions *)

Definition SensorOn := 0.
Definition ExecFunction := 1.
Definition SendQuery := 2.
Definition RecvQuery := 3.
Definition TimeOut := 4.
Definition EOCSensorOn := 5.
Definition Answer := 6.
Definition SustainRLED := 7.
Definition EndOfCheck := 8.
Definition EOCAnswer := 9.

Definition transitions1 := [SensorOn; ExecFunction; SendQuery; RecvQuery;
                           TimeOut; EOCSensorOn; Answer; SustainRLED; EndOfCheck;
                           EOCAnswer].

Definition T1 := { t | List.In t transitions1 }.

(** Input arcs function *)

Definition pre1 (p : P1) (t : T1) : option (ArcT * natstar) :=
  match p, t with
  | [0], ([0] | [1]) => Some (basic, onens)
  | [1], [1] => Some (test, onens)
  | [1], [2] => Some (basic, onens)
  | [2], [2] => Some (basic, onens)
  | [3], ([3] | [4]) => Some (basic, onens)
  | [4], [0] => Some (basic, onens)
  | [4], [1] => Some (inhibitor, onens)
  | [5], [2] => Some (basic, onens)
  | [6], [6] => Some (basic, onens)
  | [7], [3] => Some (basic, onens)
  | [8], [6] => Some (basic, onens)
  | [9], [7] => Some (basic, onens)
  | [10], [5] => Some (basic, onens)
  | [11], [9] => Some (basic, onens)
  | [12], [8] => Some (basic, onens)
  | _, _ => None
  end.

(** Output arcs function *)

Definition post1 (t : T1) (p : P1) : option natstar :=
  match t, p with
  | [0], [10] => Some onens
  | [1], [4] => Some twons
  | [1], [5] => Some onens
  | [2], ([6] | [7] | [0]) => Some onens
  | [3], [8] => Some onens
  | [4], [9] => Some onens
  | [5], [0] => Some onens
  | [6], ([11] | [12]) => Some onens
  | [7], [12] => Some onens
  | [8], [3] => Some onens
  | [9], [1] => Some onens
  | _, _ => None
  end.

(** Initial marking *)

Definition M01 (p : P1) : nat :=
  match p with
  | [4] => 2
  | [0] | [1] | [2] | [3] => 1
  | _ => 0
  end.

(** Time intervals *)

Definition Is1 (t : T1) : option TimeInterval :=
  match t with
  | [4] => Some it10inf
  | [7] => Some it33
  | _ => None
  end.

(** Conditions *)

Definition conditions1 := [30]%list.
Definition C1 := { c | List.In c conditions1 }.

Definition has_C1 (t : T1) (c : C1) : MOneZeroOne :=
  match t, c with
  | [0], [30] => one
  | _, _ => zero
  end.

(* Actions *)

Definition actions1 := [10; 11].
Definition A1 := { a | List.In a actions1 }.

Definition has_A1 (p : P1) (a : A1) : bool :=
  match p, a with
  | [8], [10] | [9], [11] => true
  | _, _ => false
  end.

(* Functions *)

Definition functions1 := [60]%list.
Definition F1 := { f | List.In f functions1 }.

Definition has_F1 (t : T1) (f : F1) : bool :=
  match t, f with
  | [1], [60] => true
  | _, _ => false
  end.

(** Priority relation *)

Definition prio1 (x y : T1) : Prop :=
  match x, y with
  | [4], [3] => True
  | _, _ => False
  end.

Definition prio1_dec : forall x y : T1, {prio1 x y} + {~prio1 x y}. decide_prio_dec. Defined.

(* SITPN structure *)

Example sitpn1 :=
  @BuildSitpn
    places1 transitions1
    pre1 post1 M01 Is1
    conditions1 actions1 functions1
    has_C1 has_A1 has_F1
    prio1.

(*! Tests !*)

(* Require Import GenerateHVhdl. *)
(* Require Import AbstractSyntax. *)
(* Require Import Sitpn2HVhdlTypes. *)
(* Require Import String. *)

(* Compute (sitpn_to_hvhdl sitpn1 prio1_dec 0 0 2). *)


