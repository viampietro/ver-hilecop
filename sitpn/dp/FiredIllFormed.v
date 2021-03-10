(** * Definition of the fired set of transitions *)

(** Ill-formed definitions; i.e, not accepted but the Coq core. *)

Require Import CoqLib.
Require Import dp.Sitpn.
Require Import SitpnTypes.
Require Import GlobalTypes.
Require Import SitpnSemanticsDefs.

Set Implicit Arguments.

Local Unset Positivity Checking.

(** ** Remark *)

(** The definitions of the [Fired] and the [HasAllAuth] predicates,
    present in the section [FiredMiscImplementation] are here for
    informative purpose only (they are not used elsewhere in the
    project). Indeed, the two definitions result in the "non-strictly
    positive occurence" checking failure. *)

Section FiredMiscImplementation.

  (** Trying to implement the Fired predicate as an
    inductive predicate, but result in the non-strictly positive
    occurence of the predicate. Indeed, Fired is used to define the
    residual marking, and in its turn the residual marking is used to
    defined Fired. *)

  Inductive FiredSimpl (sitpn : Sitpn) (s : SitpnState sitpn) (t : T sitpn) : Prop :=
  | FiredSimpl_cons :
      forall m,
        Firable s t ->
        MarkingSubPreSum (fun t' => t' >~ t /\ FiredSimpl s t') (M s) m ->
        Sens m t ->
        FiredSimpl s t.

  (** Another attempt to implement the Fired predicate, closer to the
    VHDL implementation (based on authorization from place to output
    transitions). The [HasAllAuth] predicate states that a given
    transition t has got all the authorizations from its input places
    and is therefore ready to be fired. Again, result in the
    non-strictly positive occurence of the predicate. *)

  Definition OutputOfP {sitpn} (p : P sitpn) := { t | pre p t <> None }.
  Definition InputofP {sitpn} (p : P sitpn) := { t | post t p <> None }.
  Definition OutputOfT {sitpn} (t : T sitpn) := { p | post t p <> None }.
  Definition InputOfT {sitpn} (t : T sitpn) := { p | pre p t <> None }.

  Inductive HasAuthToFire {sitpn} (s : SitpnState sitpn) (t : T sitpn) : Prop :=
    HasAuthToFire_ : Firable s t /\ (forall p, @HasAuthFromPlace sitpn s t p) -> HasAuthToFire s t
                                                                                               
  with HasAuthFromPlace {sitpn} (s : SitpnState sitpn) (t : T sitpn) : InputOfT t -> Prop :=
    HasAuthFromPlace_ :
      forall m (p : InputOfT t),
        MarkingSubPreSum (fun t' => t' >~ t /\ pre (proj1_sig p) t' <> None /\ HasAuthToFire s t') (M s) m ->
        Sens m t ->
        @HasAuthFromPlace sitpn s t p.
  
End FiredMiscImplementation.
