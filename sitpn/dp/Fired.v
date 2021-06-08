(** * Definition of the fired set of transitions *)

Require Import common.CoqLib.
Require Import dp.Sitpn.
Require Import dp.SitpnTypes.
Require Import common.GlobalTypes.
Require Import dp.SitpnSemanticsDefs.
Require Import common.ListPlus.
Require Import dp.SitpnFacts.

Set Implicit Arguments.

(** ** Operational Implementation of the Fired set. *)

(** A more operational implementation of the set of fired transitions
    at a given SITPN state s. *)

(** Qualifies the sublist of transitions that are of top priority
    (i.e, [tp]) in a given list of transitions (i.e, [lofT]). *)

Inductive IsTopPriorityListAux sitpn :
  list (T sitpn) -> list (T sitpn) -> list (T sitpn) -> list (T sitpn) -> Prop :=
| IsTopPriorityList_nil :
    forall lofT__b tp, IsTopPriorityListAux [] lofT__b tp tp
| IsTopPriorityList_cons :
    forall t lofT__a lofT__b tp tp',
      ~(exists t', In t' (lofT__a ++ lofT__b) /\ t' >~ t) ->
      IsTopPriorityListAux lofT__a (lofT__b ++ [t]) (tp ++ [t]) tp' ->
      IsTopPriorityListAux (t :: lofT__a) lofT__b tp tp'
| IsTopPriorityList_not_top :
    forall t lofT__a lofT__b tp tp',
      (exists t', In t' (lofT__a ++ lofT__b) /\ t' >~ t) ->
      IsTopPriorityListAux lofT__a (lofT__b ++ [t]) tp tp' ->
      IsTopPriorityListAux (t :: lofT__a) lofT__b tp tp'.

(** Wrapper around the IsTopPriorityListAux.  [tp] is the top-priority
    list of transitions of the list [lofT].  *)

Definition IsTopPriorityList sitpn (lofT : list (T sitpn)) (tp : list (T sitpn)) : Prop :=
  IsTopPriorityListAux lofT [] [] tp.

(** Elects the fired transitions from a list of transitions [tp];
    the election is based on the firability status of transitions at
    state [s] and their sensitization status at marking [m].
 *)

Inductive ElectFired sitpn (s : SitpnState sitpn) (fired : list (T sitpn)) :
  list (T sitpn) -> list (T sitpn) -> Prop :=
| ElectFired_nil :
    ElectFired s fired [] fired
| ElectFired_cons :
    forall tp t msub fired',
      Firable s t ->
      MarkingSubPreSum (fun t' => t' >~ t /\ InA Teq t' fired) (M s) msub ->
      Sens msub t ->
      ElectFired s (fired ++ [t]) tp fired' ->
      ElectFired s fired (t :: tp) fired'
| ElectFired_not_fired :
    forall tp t msub fired',
      MarkingSubPreSum (fun t' => t' >~ t /\ InA Teq t' fired) (M s) msub ->
      ~(Firable s t /\ Sens msub t) ->
      ElectFired s fired tp fired' ->
      ElectFired s fired (t :: tp) fired'.

(** States that a list [d] is the result of the difference between two
    lists [l] and [m]; i.e, d = l\m is set theory notation. *)

Definition IsDiff {A} (l m d : list A) :=
  NoDup l /\ NoDup m /\ NoDup d /\ forall a, In a d <-> (In a l /\ ~In a m).

(** Builds the list of fired transitions from the list [lofT], the
    list of already elected fired transitions [fired], and the
    residual marking [m]. *)

Inductive IsFiredListAux sitpn (s : SitpnState sitpn) (fired : list (T sitpn)) :
  list (T sitpn) -> list (T sitpn) -> Prop :=
| IsFiredListAux_nil :
      IsFiredListAux s fired [] fired 
| IsFiredListAux_cons :
    forall lofT tp fired' lofT' fired'',

      (* [tp] is the list of top-priority transitions contained in [lofT]. *)
      IsTopPriorityList lofT tp ->

      (* [fired'] is the list of fired transitions built from the
         previous list of fired transitions [fired], and the list of
         top-priority transitions [tp]. *)
      ElectFired s fired tp fired' ->

      (* lofT' = lofT \ tp *)
      IsDiff lofT tp lofT' ->
      
      IsFiredListAux s fired' lofT' fired'' ->
      
      IsFiredListAux s fired lofT fired''.

(** Wrapper around the IsFiredListAux predicate.  

    Adds that [Tlist] must implement the set (T sitpn).
 *)

Inductive IsFiredList sitpn (s : SitpnState sitpn) (fired : list (T sitpn)) : Prop :=
  IsFiredList_ :
    forall Tlist,
      Set_in_ListA Teq (fun t => True) Tlist ->
      IsFiredListAux s [] Tlist fired ->
      IsFiredList s fired.

(** Final definition of the set of [fired] transitions at state [s]
    and the fact that a transition [t] belongs to the set. *)

Definition Fired sitpn (s : SitpnState sitpn) (fired : list (T sitpn)) (t : T sitpn) : Prop :=
  IsFiredList s fired /\ In t fired.


