(** * Misc. definitions for the SITPN semantics. *)

Require Import Coqlib.
Require Import dp.Sitpn.
Require Import SitpnTypes.
Require Import GlobalTypes.

Set Implicit Arguments.

Local Notation "| e |" := (exist _ e _) (at level 50).

(** ∀ sitpn ∈ SITPN, ∀ t ∈ T, ∀ s ∈ S, 
    AllConditionsTrue(t) iff ∀ c ∈ C, has_C(t,c) ⇒ cond(c) = true
 *)

Definition AllConditionsEnabled (sitpn : Sitpn) (s : SitpnState sitpn) (t : (T sitpn)) :=
  forall c, has_C t c = one -> cond s c = true /\ has_C t c = mone -> cond s c = false.

(** ∀ t ∈ T, marking m, t ∈ sens(m) iff
    ∀ p ∈ P, m(p) ≥ Pre(p, t) ∧ m(p) ≥ Test(p, t) ∧ (m(p) < Inhib(p, t) ∨ Inhib(p, t) = 0) *)

Definition Sens (sitpn : Sitpn) (M : (P sitpn) -> nat) (t : (T sitpn)) :=
  forall p n,
    (pre p t = Some (test, n) \/ pre p t = Some (basic, n) -> (M p) >= n) /\
    (pre p t = Some (inhibitor, n) -> (M p) < n).

(** ∀ optn ∈ N ⊔ {ψ}, n ∈ i iff n ≠ ψ ∧ i = [a; b] ∧ a ≤ n ≤ b *)

Definition InItval (optn : option nat) (i : StaticTimeInterval) : Prop :=
  match optn with
  | None => False
  | Some n =>   (a (itval i)) <= n /\ forall bnotinf, le_nat_natinf n (b (itval i)) bnotinf
  end.
  
(** t ∉ Ti ∨ 0 ∈ I(t) *)

Definition HasReachedTimeWindow (sitpn : Sitpn) (s : SitpnState sitpn) (t : T sitpn) :=
  match Is t with
  | None => True
  | Some itval => forall t_is_timet, InItval (I s (exist _ t t_is_timet)) itval
  end.

(** t ∈ Ti ∧ I(t) = upper(Is(t)) *)

Definition HasReachedUpperBound sitpn (s : SitpnState sitpn) : {t | @Is sitpn t <> None} -> Prop.
  refine (fun tex => (let '(exist _ t pf) := tex in _));
  destruct Is;
    [ refine (match I s tex with
              | None => True
              | Some n => forall pf_bnotinf, eq_nat_natinf n (b (itval s0)) pf_bnotinf
              end)
    |
    contradiction].
Defined.

(** ∀ t ∈ T, ∀ s ∈ S, t ∈ firable(s) iff
    t ∈ Sens(M) ∧ (t ∉ Ti ∨ 0 ∈ I(t)) ∧ AllConditionsTrue(t). 
 *)

Definition Firable (sitpn : Sitpn) (s : SitpnState sitpn) (t : T sitpn) :=
  Sens (M s) t /\ HasReachedTimeWindow s t /\ AllConditionsEnabled s t.

(** States that a given Set S is implemented by a list l.  As a side
    effect, states that a given set is finite and enumerable. *)

Definition Set_in_List (S : Set) (l : list S) : Prop := (forall s : S, In s l) /\ NoDup l.

(** Sums the weight of the pre-edges between the place [p] 
    and the transitions of a list given in parameter.

    ∑ pre(t, p), ∀ t ∈ some list of transitions.
 *)

Inductive PreSumList (sitpn : Sitpn) (p : P sitpn) (P : T sitpn -> Prop) : list {t | P t} -> nat -> Prop :=
| PreSumListNil : PreSumList p P [] 0
| PreSumListCons :
    forall t l n m a gt_m_O,
      PreSumList p P l n ->
      pre p (proj1_sig t) = Some (a, exist _ m gt_m_O) ->
      PreSumList p P (t :: l) (n + m).

(** For all list [l] and natural [n] such that: 

    - [l] implements the subset of transitions verifying predicate [P] (i.e, {t' | P t'})
    - and, ∑ pre(p,t) = n, ∀ t ∈ l 
    
    then ∑ pre(p, t) = n, ∀ t ∈ {t' | P t'}    
*)

Inductive PreSum (sitpn : Sitpn) (p : P sitpn) (P : T sitpn -> Prop) : nat -> Prop :=
| PreSum_ : forall l n, @Set_in_List {t | P t} l -> PreSumList p P l n -> PreSum p P n.

Inductive MarkingSubPreSum (sitpn : Sitpn) (tSet : T sitpn -> Prop) (m m' : P sitpn -> nat) : Prop :=
| MarkingSubPreSum_ : (forall p n, PreSum p tSet n -> m' p = m p - n) -> MarkingSubPreSum tSet m m'.

(** Sums the weight of the post-edges between the place [p] 
    and the transitions of a list given in parameter.

    ∑ post(t, p), ∀ t ∈ some list of transitions.
 *)

Inductive PostSumList (sitpn : Sitpn) (p : P sitpn) (P : T sitpn -> Prop) : list {t | P t} -> nat -> Prop :=
| PostSumListNil : PostSumList p P [] 0
| PostSumListCons :
    forall t l n m gt_m_O,
      PostSumList p P l n ->
      post (proj1_sig t) p = Some (exist _ m gt_m_O) ->
      PostSumList p P (t :: l) (n + m).

(** For all list [l] and natural [n] such that: 

    - [l] implements the subset of transitions verifying predicate [P] (i.e, {t' | P t'})
    - and, ∑ post(p,t) = n, ∀ t ∈ l 
    
    then ∑ post(p, t) = n, ∀ t ∈ {t' | P t'}    
*)

Inductive PostSum (sitpn : Sitpn) (p : P sitpn) (P : T sitpn -> Prop) : nat -> Prop :=
| PostSum_ : forall l n, @Set_in_List {t | P t} l -> PostSumList p P l n -> PostSum p P n.

Inductive MarkingSubPreSumAddPostSum (sitpn : Sitpn) (tSet : T sitpn -> Prop) (m m' : P sitpn -> nat) : Prop :=
| MarkingSubPreSumAddPostSum_ :
    (forall p n n', PreSum p tSet n -> PostSum p tSet n' -> m' p = m p - n + n') -> MarkingSubPreSumAddPostSum tSet m m'.
