(** * Misc. definitions for the SITPN semantics. *)

Require Import common.CoqLib.
Require Import common.GlobalTypes.
Require Import common.GlobalFacts.
Require Import common.ListPlus.
Require Import dp.Sitpn.
Require Import dp.SitpnTypes.

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

(** States that transition [t] is sensitized by marking [M] only
    considering its basic and test input arcs.  *)

Definition Sensbt (sitpn : Sitpn) (M : (P sitpn) -> nat) (t : T sitpn) :=
  forall p n,
    (pre p t = Some (test, n) \/ pre p t = Some (basic, n) -> (M p) >= n).

(** ∀ n ∈ N, n ∈ i iff i = [a; b] ∧ a ≤ n ≤ b *)

Definition InItval (n : nat) (i : TimeInterval) : Prop :=
  (a i) <= n /\ forall bnotinf, le_nat_natinf n (b i) bnotinf.
  
(** t ∉ Ti ∨ 0 ∈ I(t) *)

Definition HasReachedTimeWindow (sitpn : Sitpn) (s : SitpnState sitpn) (t : T sitpn) : Prop.
  case_eq (Is t);
    [
      lazymatch goal with
      | [ _ : _ |- forall i : TimeInterval, _ -> _ ] =>
        let i := fresh in
        intros i t_is_timet; refine (InItval (I s (exist _ t (some_to_nnone t_is_timet))) i)
      end
    | intros; exact True].
Defined.

(** States that the time counter of transition [t] is less than or
    equal to the upper bound of the time interval associated to [t],
    i.e, I(t) ≤ upper(Is(t)) *)

Definition TcLeUpper sitpn (s : SitpnState sitpn) : {t | @Is sitpn t <> None} -> Prop.
  refine (fun tex => (let '(exist _ t pf) := tex in _));
    destruct Is;
    [ match goal with
      | [ i: TimeInterval |- _ ] =>
        refine (forall pf_bnotinf, le_nat_natinf (I s tex) (b i) pf_bnotinf)
      end
    | contradiction].
Defined.

(** States that the time counter of transition [t] is strictly greater
    than the upper bound of the time interval associated to [t], i.e,
    I(t) > upper(Is(t)) *)

Definition TcGtUpper sitpn (s : SitpnState sitpn) : Ti sitpn -> Prop.
  refine (fun tex => (let '(exist _ t pf) := tex in _));
  destruct Is;
    [ match goal with
      | [ i: TimeInterval |- _ ] =>
        refine (gt_nat_natinf (I s tex) (b i))
      end
    | contradiction].
Defined.

(* Returns the upper bound of the time interval associated with time
   transition [t]. *)

Definition upper sitpn : {t | @Is sitpn t <> None} -> natinf.
  refine (fun tex => (let '(exist _ t pf) := tex in _)).
    destruct Is;
    [ match goal with
      | [ i: TimeInterval |- _ ] => refine (b i)
      end
    | contradiction].
Defined.

Definition it_of_Ti sitpn (t__i : Ti sitpn) : { i : TimeInterval | Is t__i = Some i}.
  refine (let '(exist _ t pf) := t__i in _);
    destruct Is;
    [ exact (exist _ t0 eq_refl)
    | contradiction].
Defined.

Definition TcLeUpper2 sitpn (s : SitpnState sitpn) : {t | @Is sitpn t <> None} -> Prop.
  refine (fun tex => (let '(exist _ t pf) := tex in _));
    destruct Is;
    [ match goal with
      | [ i: TimeInterval |- _ ] =>
        refine (forall pf_bnotinf, le_nat_natinf (I s tex) (b i) pf_bnotinf)
      end
    | contradiction].
Defined.

Definition upper2 sitpn (t__i : Ti sitpn) : natinf := b (proj1_sig (it_of_Ti t__i)).

(** States that the time counter of transition [t] is strictly greater
    than the upper bound of the time interval associated to [t], i.e,
    I(t) > upper(Is(t)) *)

Definition TcGtUpper2 sitpn (s : SitpnState sitpn) (t__i : Ti sitpn) : Prop :=
  gt_nat_natinf (I s t__i) (b (proj1_sig (it_of_Ti t__i))).

(** States that the time counter of transition [t] is less than or
    equal to the lower bound of the time interval associated to [t],
    i.e, I(t) ≤ lower(Is(t)) *)

Definition TcLeLower sitpn (s : SitpnState sitpn) : {t | @Is sitpn t <> None} -> Prop.
  refine (fun tex => (let '(exist _ t pf) := tex in _));
    destruct Is;
    [ match goal with
      | [ i: TimeInterval |- _ ] =>
        refine (I s tex <= a i)
      end
    | contradiction].
Defined.

(** States that the time counter of transition [t] is strictly greater
    than the lower bound of the time interval associated to [t], i.e,
    I(t) > lower(Is(t)) *)

Definition TcGtLower sitpn (s : SitpnState sitpn) : {t | @Is sitpn t <> None} -> Prop.
  refine (fun tex => (let '(exist _ t pf) := tex in _));
  destruct Is;
    [ match goal with
      | [ i: TimeInterval |- _ ] =>
        refine (I s tex > a i)
      end
    | contradiction].
Defined.

(* Returns the lower bound of the time interval associated with time
   transition [t]. *)

Definition lower sitpn : {t | @Is sitpn t <> None} -> natstar.
  refine (fun tex => (let '(exist _ t pf) := tex in _)).
    destruct Is;
    [ match goal with
      | [ i: TimeInterval |- _ ] => refine (a i)
      end
    | contradiction].
Defined.

(** ∀ t ∈ T, ∀ s ∈ S, t ∈ firable(s) iff
    t ∈ Sens(M) ∧ (t ∉ Ti ∨ 0 ∈ I(t)) ∧ AllConditionsTrue(t). 
 *)

Definition Firable (sitpn : Sitpn) (s : SitpnState sitpn) (t : T sitpn) :=
  Sens (M s) t /\ HasReachedTimeWindow s t /\ AllConditionsEnabled s t.

(** Sums the weight of the pre-edges between the place [p] 
    and the transitions of a list given in parameter.

    ∑ pre(t, p), ∀ t ∈ some list of transitions.
 *)

Definition PreSumList (sitpn : Sitpn) (p : P sitpn) (lofTs : list (T sitpn)) (sum : nat) : Prop :=
  FoldL (fun acc t => match pre p t with | Some (basic, |ω|) => acc + ω | _ => acc end) lofTs 0 sum.

(** For all list [l] and natural [n] such that: 

    - [l] implements the subset of transitions verifying predicate [P] (i.e, {t' | P t'})
    - and, ∑ pre(p,t) = n, ∀ t ∈ l 
    
    then ∑ pre(p, t) = n, ∀ t ∈ {t' | P t'}    
*)

Inductive PreSum (sitpn : Sitpn) (p : P sitpn) (P : T sitpn -> Prop) : nat -> Prop :=
| PreSum_ : forall l n, Set_in_List P l -> PreSumList p l n -> PreSum p P n.

Inductive MarkingSubPreSum (sitpn : Sitpn) (Q : T sitpn -> Prop) (m m' : P sitpn -> nat) : Prop :=
| MarkingSubPreSum_ : (forall p sum__pre, PreSum p Q sum__pre -> m' p = m p - sum__pre) -> MarkingSubPreSum Q m m'.

(** Sums the weight of the post-edges between the place [p] 
    and the transitions of a list given in parameter.

    ∑ post(t, p), ∀ t ∈ some list of transitions.
 *)

Definition PostSumList (sitpn : Sitpn) (p : P sitpn) (lofTs : list (T sitpn)) (sum : nat) : Prop :=
  FoldL (fun acc t => match post t p with | Some (exist _ ω _) => acc + ω | _ => acc end) lofTs 0 sum.

(** For all list [l] and natural [n] such that: 

    - [l] implements the subset of transitions verifying predicate [P] (i.e, {t' | P t'})
    - and, ∑ post(p,t) = n, ∀ t ∈ l 
    
    then ∑ post(p, t) = n, ∀ t ∈ {t' | P t'}    
*)

Inductive PostSum (sitpn : Sitpn) (p : P sitpn) (Q : T sitpn -> Prop) : nat -> Prop :=
| PostSum_ : forall l n, Set_in_List Q l -> PostSumList p l n -> PostSum p Q n.

Inductive MarkingSubPreSumAddPostSum (sitpn : Sitpn) (Q : T sitpn -> Prop) (m m' : P sitpn -> nat) : Prop :=
| MarkingSubPreSumAddPostSum_ :
    (forall p sum__pre sum__post,
        PreSum p Q sum__pre ->
        PostSum p Q sum__post ->
        m' p = m p - sum__pre + sum__post) ->
    MarkingSubPreSumAddPostSum Q m m'.
