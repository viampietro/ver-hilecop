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
Require Import GenerateHVhdl.

Import ErrMonadNotations.

Open Scope string_scope.

Set Implicit Arguments.

Local Notation "[ e ]" := (exist _ e _).

(** ** An simple instance of [Sitpn]. *)

Definition places_simpl := [ 0; 1; 2].
Definition transs_simpl := [ 0; 1; 2 ].
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

Definition prio_simpl_dec : forall x y : T sitpn_simpl, {x >~ y} + {~x >~ y}.
  intros; simpl; unfold prio_simpl.
  destruct x as (a, pf). destruct y as (b, pf').
  case a.
  - case b; [auto | intros n; case n; [auto | intros m; case m; auto]]. 
  - intros n; case n; [auto
                      | intros m; case m; case b;
                        [auto | intros o; case o; auto | auto | auto ]
                      ].
    case b; [auto | intros m; case m; auto]. 
Defined.

(* Initial SitpnInfo structure *)

Definition init_infos sitpn := MkSitpnInfo sitpn [] [] [] [] [].

(*! ** Tests ** !*)

Definition mbyinhib (x y : Tsimpl) := 
  do _ <- generate_sitpn_infos sitpn_simpl prio_simpl_dec;
  mutex_by_inhib sitpn_simpl x y.

Definition mbycconds (x y : Tsimpl) :=
  do _ <- generate_sitpn_infos sitpn_simpl prio_simpl_dec;
  mutex_by_cconds sitpn_simpl x y.

Definition mbyditvals (x y : Tsimpl) :=
  do sitpninfos <- generate_sitpn_infos sitpn_simpl prio_simpl_dec;
  mutex_by_disjoint_itval sitpn_simpl x y.

Definition nexists_mutex (x y : Tsimpl) :=
  do sitpninfos <- generate_sitpn_infos sitpn_simpl prio_simpl_dec;
  not_exists_mutex sitpn_simpl x y.
  
Definition all_conflicts_of_t_solved (t : Tsimpl) (cgoft : list Tsimpl) :=
  do _ <- generate_sitpn_infos sitpn_simpl prio_simpl_dec;
  all_conflicts_of_t_solved sitpn_simpl t cgoft.

Definition all_conflicts_solved (cg : list (Tsimpl)) :=
  do _ <- generate_sitpn_infos sitpn_simpl prio_simpl_dec;
  all_conflicts_solved_by_mutex sitpn_simpl cg.

Compute (RedV (generate_sitpn_infos sitpn_simpl prio_simpl_dec (init_infos sitpn_simpl))).

sitpn_2_hvhdl
