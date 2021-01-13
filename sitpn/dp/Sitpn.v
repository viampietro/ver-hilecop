(** * Sitpn and Sitpn state definitions. *)

Require Import Coqlib.
Require Import GlobalTypes.
Require Import NatSet.
Require Import SitpnTypes.
Require Import Datatypes.

Import ListNotations.

Set Implicit Arguments.

(** ** Sitpn structure definition. *)

(** Defines the Sitpn structure as a record. *)

Record Sitpn  :=
  BuildSitpn {
      
      (* A list of nat representing the finite set of places.

         To fully implement a finite set, the [Nodup] constraint comes
         from the [IsWellDefined] predicate, found in the
         [SitpnWellDefined.v] file.  *)
      places : list nat;
                 
      (* A list of nat representing the finite set of transitions. 
         
         To fully implement a finite set, the [Nodup] constraint comes
         from the [IsWellDefined] predicate, found in the
         [SitpnWellDefined.v] file.

       *)
      transitions : list nat;
      
      (* Alias for the set of elements that belong to the finite set [places]. *)
      In_P := (fun p => In p places);
      P := { p | In_P p };
      
      (* Alias for the set of elements that belong to the finite set [transitions]. *)
      In_T := (fun t => In t transitions);
      T := { t | In_T t };

      (* Given a place p ∈ P and t ∈ T:

         Yields a couple (a, n) where a is the type of the input arc
         between p and t, and n is the weight of the arc (therefore,
         strictly more than zero).
         
         Yields None if there is no arc between p and t.
         
       *)
      pre : P -> T -> option (ArcT * natstar);
      
      (* The function associating a weight to transition-place edges. *)
      post : T -> P -> option natstar;

      (* The initial marking of the SITPN. *)
      M0 : P -> nat;

      (* Associates a static time interval to certain transitions 
       * of the SITPN.
       *
       * For a given sitpn : Sitpn, and a transition t : Trans, 
       * Is sitpn t = None if no time interval
       * is associated with t in sitpn. *)
      Is : T -> option TimeInterval;

      (* Finite sets of conditions, actions and functions. *)
      conditions : list nat;
      actions : list nat;
      functions : list nat;

      (* Aliases for the set of elements that belong to the finite set
         [conditions] (resp. [actions] and [functions]). *)
      In_C := (fun c => In c conditions);
      C := { c | In_C c };
      
      In_A := (fun a => In a actions);
      A := { a | In_A a };

      In_F := (fun f => In f functions);
      F := { f | In_F f };
      
      (* The function associating conditions to transitions. *)
      has_C : T -> C -> MOneZeroOne; 

      (* The function associating actions to places. *)
      has_A : P -> A -> bool;

      (* The function associating interpretation functions to
         transitions. *)
      has_F : T -> F -> bool;

      (* Priority relation between transitions. *)

      pr : T -> T -> Prop;
      
    }.

(** Notations for Sitpn. *)

Notation "a '>~' b" := (pr a b) (at level 0).

(** ** Subsets of P and T, and misc. casting functions. *)

Definition Psubset sitpn Q := { p : P sitpn | Q p }.
Definition Psubset_in_P sitpn (Q : P sitpn -> Prop) (p : Psubset Q) := proj1_sig p.

Definition Tsubset sitpn Q := { t : T sitpn | Q t }.
Definition Tsubset_in_T sitpn (Q : T sitpn -> Prop) (t : Tsubset Q) := proj1_sig t.
Definition Ti (sitpn : Sitpn) := Tsubset (fun t : T sitpn => (Is t) <> None).
Definition Ti_in_T (sitpn : Sitpn) (t : Ti sitpn) := proj1_sig t.

Definition T_in_nat sitpn (t : T sitpn) : nat := proj1_sig t.
Definition P_in_nat sitpn (p : P sitpn) : nat := proj1_sig p.
Definition C_in_nat sitpn (c : C sitpn) : nat := proj1_sig c.
Definition A_in_nat sitpn (a : A sitpn) : nat := proj1_sig a.
Definition F_in_nat sitpn (f : F sitpn) : nat := proj1_sig f.

Definition nat_to_P {sitpn} p := (fun (pf : In_P sitpn p) => exist _ p pf).
Definition nat_to_T {sitpn} t := (fun (pf : In_T sitpn t) => exist _ t pf).
Definition nat_to_C {sitpn} c := (fun (pf : In_C sitpn c) => exist _ c pf).
Definition nat_to_A {sitpn} a := (fun (pf : In_A sitpn a) => exist _ a pf).
Definition nat_to_F {sitpn} f := (fun (pf : In_F sitpn f) => exist _ f pf).

(** Coercions for Sitpn. *)

Coercion P_in_nat : P >-> nat.
Coercion T_in_nat : T >-> nat.
Coercion C_in_nat : C >-> nat.
Coercion A_in_nat : A >-> nat.
Coercion F_in_nat : F >-> nat.

Coercion Psubset_in_P : Psubset >-> P.
Coercion Tsubset_in_T : Tsubset >-> T.
Coercion Ti_in_T : Ti >-> T. 

(** ** Sitpn state definition. *)

(** Defines the Sitpn state structure as a record. *)

Record SitpnState (sitpn : Sitpn) :=
  BuildSitpnState {

      (* Current marking of the Sitpn. *)
      
      M : P sitpn -> nat;

      (* Current state of time counters. *)
      
      I : Ti sitpn -> nat;

      (* Orders to reset time counters. *)
      
      reset : Ti sitpn -> bool;

      (* Current condition (boolean) values. *)
      
      cond : C sitpn -> bool;

      (* Current activation state for actions and functions. *)
      
      ex : A sitpn + F sitpn -> bool;

    }.

