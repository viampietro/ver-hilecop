Require Import MSets.
Require Import MSets.MSetList.
Require Import Arith.PeanoNat.
Require Import Lists.List.
Require Import Arith.
Require Import Datatypes.

Import ListNotations.
Set Implicit Arguments.

Inductive PositiveIntervalBound : Set :=
| pos_inf : PositiveIntervalBound
| pos_val (n : nat) : PositiveIntervalBound.

Coercion pos_val : nat >-> PositiveIntervalBound.
Notation "i+" := pos_inf (at level 0).

(** Defines the time interval structure associated with transitions. *)

Structure TimeInterval : Set :=
  mk_TimeItval {
      min_t : nat;
      max_t : PositiveIntervalBound;
    }.

Notation "'<|' a , b '|>'" := (mk_TimeItval a b) (b at level 69).

Definition dec_itval (i : TimeInterval) : TimeInterval :=
  match i with
  | <| a, pos_val b |> => <| (a - 1), (b - 1) |>
  | <| a, i+ |> => <| (a - 1), i+ |>
  end.

Notation "i '--'" := (dec_itval i) (at level 0).

(** Defines the Sitpn structure as a record. *)

Record Sitpn  :=
  BuildSitpn {

      (* Finite set of places. *)
      P : Set;

      (* Finite set of transitions. *)
      T : Set;
      
      (* The function associating a weight to place-transition edges
         that are not inhibitor or test edges. *)
      pre : P -> T -> nat;

      (* The function associating a weight to test edges. *)
      test : P -> T -> nat;

      (* The function associating a weight to inhibitor edges. *)
      inhib : P -> T -> nat;

      (* The function associating a weight to transition-place edges. *)
      post : P -> T -> nat;

      (* The initial marking of the SITPN. *)
      M0 : P -> nat;

      (* Associates a static time interval to certain transitions 
       * of the SITPN.
       *
       * For a given sitpn : Sitpn, and a transition t : Trans, 
       * sitpn.(s_intervals) t = None if no time interval
       * is associated with t in sitpn. *)
      Is : T -> option TimeInterval;

      (* Sets of conditions, actions and functions. *)
      C : Set;
      A : Set;
      F : Set;
      
      (* The function associating conditions to transitions. *)
      has_C : T -> C -> Prop;

      (* The function associating actions to places. *)
      has_A : P -> A -> Prop;

      (* The function associating interpretation functions to
         transitions. *)
      has_F : T -> F -> Prop;

      (* Priority relation between transitions. *)

      pr : T -> T -> Prop;
      pr_irrefl : forall t, ~pr t t;
      pr_antisym : forall t t', pr t t' -> ~pr t' t;
      pr_trans : forall t t' t'', pr t t' -> pr t' t'' -> pr t t'';
      
    }.

Notation "a '>~' b" := (pr _ a b) (at level 0).

(* Definition of SitpnState. *)

Inductive DynamicTimeInterval : Set :=
| active : TimeInterval -> DynamicTimeInterval
| blocked : DynamicTimeInterval.

Coercion active : TimeInterval >-> DynamicTimeInterval.

Definition Ti (sitpn : Sitpn) : Set := { t | (Is sitpn t) <> None }.
Definition Ti_in_T (sitpn : Sitpn) (t : Ti sitpn) := proj1_sig t.
Coercion Ti_in_T : Ti >-> T.

Structure SitpnState (sitpn : Sitpn) :=
  BuildSitpnState {
        
      (* Current marking of the Sitpn. *)
      
      M : (P sitpn) -> nat;

      (* Current state of time intervals. *)
      
      I : (Ti sitpn) -> DynamicTimeInterval;

      (* - On falling edge: orders to reset time counters at this
           cycle.  
         - On rising edge: orders to reset time counters at the
           next cycle. *)
      
      reset : (Ti sitpn) -> bool;

      (* Current condition (boolean) values. *)
      
      cond : (C sitpn) -> bool;

      (* Current activation state for continuous actions. *)
      
      exa : (A sitpn) -> bool;

      (* Current activation state for interpretation functions. *)
      
      exf : (F sitpn) -> bool;
    }.

Inductive Clk := rising_edge | falling_edge.

(** ∀ sitpn ∈ SITPN, ∀ t ∈ T, ∀ s ∈ S, 
    AllConditionsTrue(t) iff
    ∀ c ∈ C, has_C(t,c) ⇒ cond(c) = true
 *)

Definition AllConditionsTrue (sitpn : Sitpn) (s : SitpnState sitpn) (t : (T sitpn)) :=
  forall c, has_C sitpn t c -> cond s c = true.

(** ∀ t ∈ T, marking m, t ∈ sens(m) iff
    ∀ p ∈ P, m(p) ≥ Pre(p, t) ∧ 
             m(p) ≥ Test(p, t) ∧ 
             (m(p) < Inhib(p, t) ∨ Inhib(p, t) = 0) *)

Definition Sens (sitpn : Sitpn) (M : (P sitpn) -> nat) (t : (T sitpn)) :=
  forall p,
    (M p) >= (pre sitpn p t)
    /\ (M p) >= (test sitpn p t)
    /\ ((M p) < (inhib sitpn p t) \/ (inhib sitpn p t) = 0).

(** ∀ n ∈ N, ∀ i ∈ I+ ⊔ {ψ}, n ∈ i iff
    i = [a; b] ∧ a ≤ n ≤ b
 *)

Definition InItval (n : nat) (i : DynamicTimeInterval) :=
  exists a b, i = <| a, pos_val b |> /\ a <= n <= b.

(** t ∉ Ti ∨ 0 ∈ I(t) *)

Definition HasReachedTimeWindow (sitpn : Sitpn) (s : SitpnState sitpn) (t : T sitpn) :=
  match Is sitpn t with
  | None => True
  | Some i => InItval 0 i
  end.

(** ∀ t ∈ T, ∀ s ∈ S, t ∈ firable(s) iff
    t ∈ Sens(M) ∧ (t ∉ Ti ∨ 0 ∈ I(t)) ∧ AllConditionsTrue(t). 
 *)

Definition Firable (sitpn : Sitpn) (s : SitpnState sitpn) (t : T sitpn) :=
  Sens sitpn (M s) t /\ HasReachedTimeWindow s t /\ AllConditionsTrue s t.

(** ∀ t, t' ∈ T, ∀ s ∈ S, t' ∈ Pr(t) iff
    t' ≻ t ∧ t' ∈ Firable(s)
 *)

Definition IsPriorityAndFirable (sitpn : Sitpn) (s : SitpnState sitpn) (t t' : T sitpn) :=
  t' >~ t /\ Firable s t'.

(** Subset of transitions that are firable and have a higher firing
    priority than [t]. *)

Definition Pr (sitpn : Sitpn) (s : SitpnState sitpn) (t : T sitpn) := { t' | IsPriorityAndFirable s t t'}.

(** [Pr] is a subset of the set of transitions [T]. *)

Definition Pr_in_T (sitpn : Sitpn) (s : SitpnState sitpn) (t : T sitpn) (t' : Pr s t) : T sitpn := proj1_sig t'.
Coercion Pr_in_T : Pr >-> T.

(** States that a given Set S is implemented by a list l. *)

Definition Set_in_List (S : Set) (l : list S) : Prop := (forall s : S, In s l) /\ NoDup l.

(** Sums the weight of the pre-edges between the place [p] 
    and the transitions belonging to [Pr(t)].

    ∑ pre(ti, p), ∀ ti ∈ Pr(t).

 *)

Inductive PreSumList (sitpn : Sitpn) (s : SitpnState sitpn) (t : T sitpn) (p : P sitpn) :
  list (Pr s t) -> nat -> Prop :=
| PreSumListNil : PreSumList p [] 0
| PreSumListCons : forall l n t', PreSumList p l n -> PreSumList p (t' :: l) (n + pre sitpn p t').

Inductive PreSum (sitpn : Sitpn) (s : SitpnState sitpn) (t : T sitpn) (p : P sitpn) : nat -> Prop :=
| PreSum_ : forall l n, @Set_in_List (Pr s t) l -> PreSumList p l n -> PreSum s t p n.

Inductive MarkingSubPreSum (sitpn : Sitpn) (s : SitpnState sitpn) (t : T sitpn) (MSub : P sitpn -> nat) : Prop :=
| MarkingSubPreSum_ : (forall p n, PreSum s t p n -> MSub p = M s p - n) -> MarkingSubPreSum s t MSub.

(** ∀ t ∈ T, ∀ s ∈ S, t ∈ Fired(s) iff 
    t ∈ Firable(s) ∧ t ∈ Sens(M - ∑ pre(ti), ∀ ti ∈ Pr(t)) *)

Definition Fired (sitpn : Sitpn) (s : SitpnState sitpn) (t : T sitpn) :=
  Firable s t /\ forall MSub, MarkingSubPreSum s t MSub -> Sens sitpn MSub t.

(** Sitpn semantics. *)

Inductive SitpnSemantics (sitpn : Sitpn) (s s' : SitpnState sitpn) (env : C sitpn -> nat -> bool) (tau : nat) : Clk -> Prop :=
| SitpnSemantics_falling :
    (forall c, (cond s' c) = (env c tau)) ->
    (forall a, (exists p, (M s p) > 0 /\ has_A sitpn p a) -> (exa s' a) = true) ->
    (forall a, (forall p, (M s p) = 0 \/ ~has_A sitpn p a) -> (exa s' a) = false) ->    
    (forall (t : Ti sitpn) i, Sens sitpn (M s) t -> (reset s t = true \/ Fired s t) -> Is sitpn t = Some i -> I s' t = i--) ->
    (forall (t : Ti sitpn) i, Sens sitpn (M s) t -> reset s t = false -> ~Fired s t -> I s t = active i -> I s' t = i--) ->
    (forall (t : Ti sitpn), Sens sitpn (M s) t -> reset s t = false -> ~Fired s t -> I s t = blocked -> I s' t = blocked) ->
    SitpnSemantics s s' env tau falling_edge.    




