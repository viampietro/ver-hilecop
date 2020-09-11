(** * Definition of the fired set of transitions *)

Require Import Coqlib.
Require Import dp.Sitpn.
Require Import SitpnTypes.
Require Import GlobalTypes.
Require Import SitpnSemanticsDefs.

Set Implicit Arguments.

(** ** Operational Implementation of the Fired set. *)

(** A more operational implementation of the set of fired transitions
    at a given SITPN state s. *)

(** Qualifies the sublist of transitions that are of top priority
    (i.e, [tp]) in a given list of transitions (i.e, [lofT]). *)

Inductive IsTopPriorityListAux sitpn :
  list (T sitpn) -> list (T sitpn) -> list (T sitpn) -> Prop :=
| IsTopPriorityList_nil :
    forall tp, IsTopPriorityListAux [] tp tp
| IsTopPriorityList_cons :
    forall lofT tp t tp',
      ~(exists t', In t' lofT -> t' >~ t = true) ->
      IsTopPriorityListAux lofT (tp ++ [t]) tp' ->
      IsTopPriorityListAux (t :: lofT) tp tp'
| IsTopPriorityList_not_top :
    forall lofT tp t tp',
      (exists t', In t' lofT -> t' >~ t = true) ->
      IsTopPriorityListAux lofT tp tp' ->
      IsTopPriorityListAux (t :: lofT) tp tp'.

(** Wrapper around the IsTopPriorityListAux.  [tp] is the top-priority
    list of transitions of the list [lofT].  *)

Definition IsTopPriorityList sitpn (lofT : list (T sitpn)) (tp : list (T sitpn)) : Prop :=
  IsTopPriorityListAux lofT [] tp.

(** Elects the fired transitions from a list of transitions [lofT];
    the election is based on the firability status of transitions at
    state [s] and their sensitization status at marking [m].
 *)

Inductive ElectFired sitpn (s : SitpnState sitpn) :
  list (T sitpn) ->
  ((P sitpn) -> nat) ->
  list (T sitpn) ->
  ((P sitpn -> nat) * (list (T sitpn))) -> Prop :=
| ElectFired_nil :
    forall m fired, ElectFired s [] m fired (m, fired)
| ElectFired_cons :
    forall m fired lofT t msub m' fired',
      Firable s t ->
      Sens m t ->
      (* Singleton set {t}. *)
      MarkingSubPreSum (fun t' => t' = t) m msub ->
      ElectFired s lofT msub (fired ++ [t]) (m', fired') ->
      ElectFired s (t :: lofT) m fired (m', fired')
| ElectFired_not_fired :
    forall m fired lofT t m' fired',
      ~(Firable s t /\ Sens m t) ->
      ElectFired s lofT m fired (m', fired') ->
      ElectFired s (t :: lofT) m fired (m', fired').

(** States that a list [d] is the result of the difference between two
    lists [l] and [m]; i.e, d = l\m is set theory notation. *)

Definition IsDiff {A} (l m d : list A) :=
  forall a, In a d <-> (In a l /\ ~In a m).

(** Builds the list of fired transitions from the list [lofT], the
    list of already elected fired transitions [fired], and the
    residual marking [m]. *)

Inductive IsFiredListAux sitpn (s : SitpnState sitpn) :
  list (T sitpn) -> (P sitpn -> nat) -> list (T sitpn) -> list (T sitpn) -> Prop :=
| IsFiredListAux_nil :
    forall m fired,
      IsFiredListAux s [] m fired fired
| IsFiredListAux_cons :
    forall lofT m fired tp m' fired' lofT' fired'',

      (* [tp] is the list of top-priority transitions contained in [lofT]. *)
      IsTopPriorityList lofT tp ->

      (* [fired'] is the list of fired transitions built from the
         previous list of fired transitions [fired], the residual marking
         [m], and the list of top-priority transitions [tp].

         [m'] is the new residual marking. *)
      ElectFired s tp m fired (m', fired') ->

      (* lofT' = lofT \ tp *)
      IsDiff lofT tp lofT' ->
      
      IsFiredListAux s lofT' m' fired' fired'' ->      
      IsFiredListAux s lofT m fired fired''.

Scheme Induction for IsFiredListAux Sort Prop.

(** Wrapper around the IsFiredListAux predicate.  

    Remove from the definition of the IsFiredList predicate that 
    lofT must implement the T set of transitions of the sitpn.

    [lofT] is a potentially ill-formed list of transitions (i.e, with duplicates...).

    The calling context must ensure its well-formedness.
 *)

Inductive IsFiredList sitpn (s : SitpnState sitpn) (fired : list (T sitpn)) : Prop :=
  IsFiredList_ :
    forall lofT,
      IsFiredListAux s lofT (M s) [] fired ->
      IsFiredList s fired.

(** Final definition of the set of [fired] transitions at state [s]
    and the fact that a transition [t] belongs to the set. *)

Definition Fired sitpn (s : SitpnState sitpn) (fired : list (T sitpn)) (t : T sitpn) : Prop :=
  IsFiredList s fired /\ In t fired.


