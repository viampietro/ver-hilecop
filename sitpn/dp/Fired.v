(** * Sitpn semantics definition *)

Require Import Coqlib.
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
        MarkingSubPreSum (fun t' => t' >~ t = true /\ FiredSimpl s t') (M s) m ->
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

  Inductive HasAllAuth {sitpn} (s : SitpnState sitpn) (t : T sitpn) : Prop :=
    HasAllAuth_ : Firable s t /\ (forall p, @HasAuth sitpn s t p) -> HasAllAuth s t
                                                                                
  with HasAuth {sitpn} (s : SitpnState sitpn) (t : T sitpn) : InputOfT t -> Prop :=
    HasAuth_ :
      forall m (p : InputOfT t),
        MarkingSubPreSum (fun t' => t' >~ t = true /\ pre (proj1_sig p) t' <> None /\ HasAllAuth s t') (M s) m ->
        Sens m t ->
        @HasAuth sitpn s t p.
  
End FiredMiscImplementation.

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

(** Wrapper around the IsFiredListAux predicate.  *)

Definition IsFiredList sitpn (s : SitpnState sitpn) (fired : list (T sitpn)) :=
  forall l,
    @Set_in_List (T sitpn) l -> 
    IsFiredListAux s l (M s) [] fired.

(** Final definition of the set of fired transitions at state [s]. *)

Definition Fired sitpn (s : SitpnState sitpn) (t : T sitpn) : Prop :=
  forall fired, IsFiredList s fired /\ In t fired.
