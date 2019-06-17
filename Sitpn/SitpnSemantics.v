(*! =============================== !*)
(*! ======= SITPN SEMANTICS ======= !*)
(*! =============================== !*)

Require Import Omega.
Require Import Classical_Prop.

Set Implicit Arguments.

(** Import Sitpn and SitpnState structures. *)

Require Import Hilecop.Sitpn.Sitpn.

(** * General preliminary definitions.  *)

(** ** Predicates IsDecListCons, IsDecListApp and facts. *)

Section DecreasedList.

  Variable A : Type.
  
  (** List l is a decreased or equal version of list l'. 
      l' is built from l by adding elements in the front (cons).
       
      Useful for proof involving recursion on lists.  *)
  
  Inductive IsDecListCons : list A -> list A -> Prop :=
  | IsDecListCons_refl : forall l : list A, IsDecListCons l l
  | IsDecListCons_eq : forall (a : A) (l : list A), IsDecListCons l (a :: l)
  | IsDecListCons_cons :
      forall (a : A) (l l' : list A),
      IsDecListCons l l' ->      
      IsDecListCons l (a :: l').

  (** Facts about IsDecListCons. *)
  
  Lemma is_dec_list_cons_nil :
    forall (l : list A), IsDecListCons [] l.
  Proof.
    induction l.
    - apply IsDecListCons_refl.
    - apply IsDecListCons_cons; assumption.
  Qed.
  
  Lemma is_dec_list_cons_incl :
    forall l' l : list A, IsDecListCons l l' -> incl l l'.
  Proof.
    induction l'.
    - intros l His_dec x Hin_l.
      inversion His_dec.
      rewrite H0 in Hin_l.
      inversion Hin_l.
    - intros l His_dec; inversion His_dec.
      + apply incl_refl.
      + intros x Hin_l'; apply in_cons; assumption.
      + apply IHl' in H1.
        intros x Hin_l.
        apply H1 in Hin_l.
        apply in_cons with (a := a) in Hin_l.
        assumption.      
  Qed.

  Lemma is_dec_list_cons_cons :
    forall (a : A) (l' l : list A), IsDecListCons (a :: l) l' -> IsDecListCons l l'.
  Proof.
    intros a l'.
    induction l'.
    - intros l His_dec; inversion His_dec.
    - intros l His_dec; inversion His_dec.
      + apply IsDecListCons_eq.
      + apply IsDecListCons_cons; apply IsDecListCons_eq.
      + apply IsDecListCons_cons; apply (IHl' l H1).
  Qed.

  (** List l is a decreased or equal version of list l'. 
      l' is built from l by adding elements in the front (cons).
       
      Useful for proof involving recursion on lists.  *)

  Inductive IsDecListApp : list A -> list A -> Prop :=
  | IsDecListApp_refl : forall l : list A, IsDecListApp l l
  | IsDecListApp_eq : forall (a : A) (l : list A), IsDecListApp l (l ++ [a])
  | IsDecListApp_cons :
      forall (a : A) (l l' : list A),
        IsDecListApp l l' ->
        IsDecListApp l (l' ++ [a]).
  
End DecreasedList.

(** * Predicates for priority definitions between transitions. *)

(** ** Predicate IsPredInList and facts. *)

Section PredInList.

  Variable A : Type.
    
  (** Tells if x is a predecessor of y in list l. 
      x and y are possibly equal and list l
      possibly contains duplicates. *)
  
  Inductive IsPredInList (x y : A) : list A -> Prop :=
  | IsPredInList_eq :
      forall l : list A, IsPredInList x y (x :: y :: l)
  | IsPredInList_rm_snd :
      forall (a : A) (l : list A), IsPredInList x y (x :: l) ->
                                   IsPredInList x y (x :: a :: l)
  | IsPredInList_rm_fst : 
      forall (a : A) (l : list A), IsPredInList x y l ->
                                   IsPredInList x y (a :: l).

  (** IsPredInList with no duplicates in list l, x and y different. *)
  
  Definition IsPredInNoDupList (x y : A) (l : list A) :=
    x <> y /\ NoDup l /\ IsPredInList x y l.

  (** Facts about IsPredInList and IsPredInNoDuplist. *)
  
  Lemma not_is_pred_in_list_nil :
    forall (x y : A), ~IsPredInList x y [].
  Proof.
    intros x y His_pred.
    inversion His_pred.
  Qed.

  Lemma is_pred_in_list_in_tail :
    forall (x y : A) (l : list A), In y l -> IsPredInList x y (x :: l).
  Proof.
    induction l.
    - intro Hnot_in; inversion Hnot_in.
    - intro Hin_y_l; inversion Hin_y_l.
      + rewrite H; apply IsPredInList_eq.
      + apply IsPredInList_rm_snd; apply (IHl H).
  Qed.
  
  Theorem is_pred_in_dec_list :
    forall (l l' : list A) (x y : A),
      IsPredInList x y l -> IsDecListCons l l' -> NoDup l' -> IsPredInList x y l'.
  Proof.
    induction l'.
    - intros x y His_pred His_dec Hnodup.
      induction l.
      + inversion His_pred.
      + inversion His_dec.
    - intros x y His_pred His_dec Hnodup.
      inversion His_dec.
      + rewrite <- H0; assumption.
      + rewrite <- H2; apply IsPredInList_rm_fst; assumption. 
      + apply IsPredInList_rm_fst.
        -- apply NoDup_cons_iff in Hnodup; apply proj2 in Hnodup.
           apply (IHl' x y His_pred H1 Hnodup).
  Qed.

  Lemma is_pred_cons_diff :
    forall (l : list A) (x y a : A) , IsPredInList x y (a :: l) ->
                                      x <> a ->
                                      IsPredInList x y l.
  Proof.
    induction l; intros x y a' His_pred Hdiff.
    - inversion His_pred; inversion H0.
    - inversion His_pred.
      + contradiction.
      + contradiction.
      + assumption.
  Qed.

  Lemma is_pred_in_tail :
    forall (l : list A) (x y : A) , IsPredInNoDupList x y (x :: l) -> In y l.
  Proof.
    induction l; intros x y His_pred;
      unfold IsPredInNoDupList in His_pred; decompose [and] His_pred.
    - inversion H2; inversion H3.
    - inversion H2.
      + apply in_eq.
      + apply NoDup_remove with (l := [x]) in H1.
        apply proj1 in H1.
        unfold IsPredInNoDupList in IHl.
        specialize (IHl x y (conj H (conj H1 H3))) as Hin_y_l.
        apply in_cons.
        assumption.
      + inversion H1.
        apply not_in_cons in H7.
        apply proj1 in H7.
        specialize (is_pred_cons_diff H3 H7) as His_pred_in_l.
        apply IsPredInList_rm_fst with (a := x) in His_pred_in_l.
        apply in_cons.
        apply NoDup_remove with (l := [x]) in H1.
        apply proj1 in H1.
        unfold IsPredInNoDupList in IHl.
        specialize (IHl x y (conj H (conj H1 His_pred_in_l))) as Hin_y_l.
        assumption.
  Qed.

  Theorem not_is_pred_in_list_if_hd :
    forall (l : list A) (x y : A) , ~IsPredInNoDupList x y (y :: l).
  Proof.
    induction l; intros x y His_pred.
    - unfold IsPredInNoDupList in His_pred.
      decompose [and] His_pred.
      inversion H2; inversion H3.
    - unfold IsPredInNoDupList in His_pred.
      decompose [and] His_pred.
      inversion H2.
      + contradiction.
      + contradiction.
      + assert (Hvee := classic (x = a)).
        elim Hvee.
        -- intro Heq_xa.
           rewrite Heq_xa in H3.
           rewrite Heq_xa in H.
           apply NoDup_cons_iff in H1.
           elim H1; intros Hnot_in_y Hnodup.
           specialize (is_pred_in_tail (conj H (conj Hnodup H3))) as Hin_y_l.
           apply in_cons with (a := a) in Hin_y_l.
           contradiction.
        -- intro Hneq_xa.
           specialize (is_pred_cons_diff H3 Hneq_xa) as His_pred_in_l.
           apply IsPredInList_rm_fst with (a := y) in His_pred_in_l.
           apply NoDup_remove with (l := [y]) in H1.
           apply proj1 in H1.
           unfold IsPredInNoDupList in IHl.
           apply (IHl x y (conj H (conj H1 His_pred_in_l))).
  Qed.

  Theorem not_is_pred_in_dec_list :
    forall (l' l : list A) (x y : A),
      IsDecListCons (y :: l) l' ->
      In x l ->
      ~IsPredInNoDupList x y l'.
  Proof.
    induction l'; intros l x y His_dec Hin_x_l.
    - inversion His_dec.
    - intro His_pred.
      unfold IsPredInNoDupList in His_pred; decompose [and] His_pred.
      rename H into Hneq_xy; rename H1 into Hnodup; clear His_pred; rename H2 into His_pred.
      inversion His_pred.
      + inversion His_dec.
        -- rewrite <- H3 in H0; contradiction.
        -- rewrite <- H4 in Hnodup.
           rewrite <- H0 in Hnodup.
           apply in_cons with (a := y) in Hin_x_l.
           apply NoDup_cons_iff in Hnodup.
           apply proj1 in Hnodup; contradiction.
        -- apply is_dec_list_cons_cons in H3.
           apply is_dec_list_cons_incl in H3.
           apply H3 in Hin_x_l.
           rewrite <- H0 in Hnodup.
           apply NoDup_cons_iff in Hnodup.
           apply proj1 in Hnodup; contradiction.
      + inversion His_dec.
        -- rewrite <- H4 in H; contradiction.
        -- rewrite <- H5 in Hnodup.
           rewrite <- H in Hnodup.
           apply in_cons with (a := y) in Hin_x_l.
           apply NoDup_cons_iff in Hnodup.
           apply proj1 in Hnodup; contradiction.
        -- apply is_dec_list_cons_cons in H4.
           apply is_dec_list_cons_incl in H4.
           apply H4 in Hin_x_l.
           rewrite <- H in Hnodup.
           apply NoDup_cons_iff in Hnodup.
           apply proj1 in Hnodup; contradiction.
      + inversion His_dec.
        -- assert (Hnot_is_pred : ~IsPredInNoDupList x y (y :: l))
            by apply not_is_pred_in_list_if_hd.
           rewrite <- H4 in His_pred; rewrite <- H4 in Hnodup.
           rewrite <- H5 in His_pred; rewrite <- H5 in Hnodup.
           specialize (conj Hneq_xy (conj Hnodup His_pred)) as His_pred'.
           contradiction.
        -- assert (Hnot_is_pred : ~IsPredInNoDupList x y (y :: l))
            by apply not_is_pred_in_list_if_hd.
           rewrite <- H5 in Hnodup; rewrite <- H5 in H0.
           apply NoDup_cons_iff in Hnodup.
           apply proj2 in Hnodup.
           specialize (conj Hneq_xy (conj Hnodup H0)) as His_pred'.
           contradiction.
        -- apply NoDup_cons_iff in Hnodup.
           apply proj2 in Hnodup.
           apply (IHl' l x y H4 Hin_x_l (conj Hneq_xy (conj Hnodup H0))).
  Qed.
  
End PredInList.

(** Defines a priority relation between a transition t and t', where t
    has a higher priority than t', i.e: ∀ t ∈ T, t' ∈ T/{t}, t ≻ t' *)

Definition HasHigherPriority
           (t t' : Trans)
           (pgroup : list Trans) :=
  In t pgroup /\
  In t' pgroup /\
  IsPredInNoDupList t t' pgroup.

(** Defines [pr] as the set (therefore, with no duplicates) of
    transitions that are in the [fired] list and have a higher
    priority than transition [t] in [pgroup]. *)

Definition IsPrioritySet
           (fired pgroup : list Trans)
           (t : Trans)
           (pr : list Trans) :=
  NoDup pr /\
  (forall t' : Trans,
      HasHigherPriority t' t pgroup /\ In t' fired <-> In t' pr).

(** * Functions for marking update and facts. *)

(** Sums edge weight from place p to transitions of the l list. *)

Fixpoint pre_sum (sitpn : Sitpn) (p : Place) (l : list Trans) {struct l} : nat :=
  match l with
  | t :: tail => (pre sitpn t p) + pre_sum sitpn p tail
  | [] => 0
  end.

Functional Scheme pre_sum_ind := Induction for pre_sum Sort Prop.

(** pre_sum sitpn p l + pre_sum sitpn p [t] = pres_um sitpn p (l ++ [t]) *)

Lemma pre_sum_app_add :
  forall (sitpn : Sitpn) (p : Place) (l : list Trans) (t : Trans),
    pre_sum sitpn p l + pre_sum sitpn p [t] = pre_sum sitpn p (l ++ [t]).
Proof.
  intros sitpn p l; functional induction (pre_sum sitpn p l) using pre_sum_ind; intro t'.
  - simpl; reflexivity.
  - simpl.
    rewrite <- (IHn t').
    simpl.
    rewrite plus_assoc_reverse.
    reflexivity.
Qed.

(** Sums edge weight from transitions of the l list to place p. *)

Fixpoint post_sum (sitpn : Sitpn) (p : Place) (l : list Trans) {struct l} : nat :=
  match l with
  | t :: tail => (post sitpn t p) + post_sum sitpn p tail
  | [] => 0
  end.

Functional Scheme post_sum_ind := Induction for post_sum Sort Prop.

(** Marking m and m' apply to the same set of places. *)

Definition MarkingHaveSameStruct (m m' : list (Place * nat)) :=
  fst (split m) = fst (split m').

(** * Sensitization definition. *)

(** ∀ t ∈ T, marking m, t ∈ sens(m) if
    ∀ p ∈ P, m(p) ≥ Pre(p, t) ∧ 
             m(p) ≥ Pre_t(p, t) ∧ 
             (m(p) < Pre_i(p, t) ∨ Pre_i(p, t) = 0) *)

Definition IsSensitized
           (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans) : Prop :=
  forall (p : Place)
         (n : nat),
    In (p, n) marking ->
    (pre sitpn t p) <= n  /\
    (test sitpn t p) <= n  /\
    (n < (inhib sitpn t p) \/ (inhib sitpn t p) = 0).

(** * Predicates for Time Petri nets semantics. *)

(** Tests if [t] is associated in [d_intervals] with is an active time
    interval with [min_t] = 0 (≡ 0 ∈ I) or if t has no static time
    interval in sitpn. *)

Definition HasEnteredTimeWindow
           (sitpn : Sitpn)
           (d_intervals : list (Trans * DynamicTimeInterval))
           (t : Trans) :=
  s_intervals sitpn t = None \/
  forall (upper_bound : PositiveIntervalBound),
    In (t, active {| min_t := 0; max_t := upper_bound |}) d_intervals.

(** Tests if the upper bound of a time interval equals 0. 
    Useful when determining if a dynamic time interval 
    should be blocked. *)

Definition HasReachedUpperBound (dyn_itval : DynamicTimeInterval) :=
  dyn_itval = active {| min_t := 0; max_t := pos_val 0 |} \/ dyn_itval = blocked.

(** Decrements the bounds of a time interval. *)

Definition dec_itval (itval : TimeInterval) :=
  match itval with
  | {| min_t := n; max_t := pos_val m |} =>
    {| min_t := n - 1; max_t := pos_val (m - 1) |}
  | {| min_t := n; max_t := pos_inf |} =>
    {| min_t := n - 1; max_t := pos_inf |}
  end.

(** * Predicates for Interpreted Petri nets semantics. *)

(** Tests if transition [t] is only associated with conditions
    evaluated to true in [cond_values]. *)

Definition HasReachedAllConditions
           (sitpn : Sitpn)
           (cond_values : list (Condition * bool))
           (t : Trans) :=
  forall (c : Condition),
    In c sitpn.(conditions) ->
    (has_condition sitpn t c) = true ->
    In (c, true) cond_values.

(** * Firability definition. *)

(** Expresses the firability of transition t at state s of SITPN
    sitpn.
    
    [t] is firable at state [s] of SITPN [sitpn] if m sensitizes [t], [t]
    has entered a specific time window, and all conditions associated to
    [t] are true, i.e: 

    ∀ t ∈ T, s = (Fired, M, cond, ex, I, reset), t ∈ firable(s) if 
    t ∈ sens(M) ∧ 0 ∈ I(t) ∧ (∀ c ∈ conditions, C(t, c) = 1 ⇒ cond(c) = 1). *)

Definition SitpnIsFirable
           (sitpn : Sitpn)
           (s : SitpnState)
           (t : Trans) :=
  IsSensitized sitpn s.(marking) t /\
  HasEnteredTimeWindow sitpn s.(d_intervals) t /\
  HasReachedAllConditions sitpn s.(cond_values) t.

(** * Sitpn Semantics definition.
    
      Inductive structure describing the rules regulating the
      evolution of a SITPN.

      Here, a given SITPN [sitpn] is moving from state [s] to state
      [s'] at a certain [time_value] (discrete time value
      corresponding to the count of clock cycles since the beginning).
      
      The [env] function gives the boolean value of conditions through
      time. It simulates the information coming from the environment
      of the SITPN.
      
      An instance of [Clock] parameterized the inductive structure,
      telling if the state changing is due to the occurence of a
      rising or a falling edge of a clock signal.  *)

(** Represents the two clock events regulating the Sitpn evolution. *)

Inductive Clock : Set :=
| falling_edge : Clock
| rising_edge : Clock.

(** Represents the Sitpn semantics. *)

Inductive SitpnSemantics
          (sitpn : Sitpn)
          (s s' : SitpnState)
          (time_value : nat)
          (env : Condition -> nat -> bool) : Clock -> Prop :=

(* ↓clock : s = (Fired, m, cond, ex, I, reset) ⇝ s' = (Fired', m, cond', ex', I', reset) *)
  
| SitpnSemantics_falling_edge :

    IsWellDefinedSitpn sitpn ->
    IsWellDefinedSitpnState sitpn s ->
    IsWellDefinedSitpnState sitpn s' ->

    (* Marking stays the same between state s and s'. *)
    s.(marking) = s'.(marking) ->

    (* Conditions values in s' receive new values from the
       environment, i.e: 

       ∀ c ∈ conditions, cond'(c) = env(c). *)
    
    (forall (c : Condition),
        In c sitpn.(conditions) ->
        In (c, (env c time_value)) s'.(cond_values)) ->
    
    (* Actions associated to places with a non-zero marking are
       activated, i.e: 
       
       ∀ a ∈ actions, ∃ p ∈ P, m(p) > 0 ∧ A(p, a) = 1 ⇒ ex'(a) = 1. *)
    
    (forall (a : Action),
        In a sitpn.(actions) ->
        (exists (p : Place) (n : nat),
            In (p, n) s.(marking) /\ n > 0 /\ (has_action sitpn p a) = true) ->
        In (a, true) s'.(exec_a)) ->
    
    (* Actions only associated with unmarked places (no tokens) 
       are deactivated, i.e: 
       
       ∀ a ∈ actions, ∀ p ∈ P, m(p) = 0 ∨ A(p, a) = 0 ⇒ ex'(a) = 0. *)

    (forall (a : Action),
        In a sitpn.(actions) ->
        (forall (p : Place) (n : nat),
            In (p, n) s.(marking) -> n = 0 \/ (has_action sitpn p a) = false) ->
        In (a, false) s'.(exec_a)) ->
                   
    (* Time intervals are reset for all transitions sensitized by m
       and that received a reset order or were previously fired, i.e:
      
       ∀ t ∈ Ti, t ∈ sens(m) ∧ (reset(t) = 1 ∨ t ∈ Fired) ⇒ 
       I'(t) = Is(t) - 1 
       where Ti = { ti | I(ti) ≠ ∅ } *)
    
    (forall (t : Trans)
            (itval : TimeInterval),
        In t (fst (split s.(d_intervals))) ->
        IsSensitized sitpn s.(marking) t ->
        (In (t, true) s.(reset) \/ In t s.(fired)) ->
        Some itval = (s_intervals sitpn t) ->
        In (t, active (dec_itval itval)) s'.(d_intervals)) ->

    (* Time intervals evolve normally for all transitions sensitized
       by m, having an active time interval, that didn't receive a reset
       order and were not fired at the last clock cycle, i.e:
      
       ∀ t ∈ Ti, t ∈ sens(m) ∧ reset(t) = 0 ∧ t ∉ Fired ∧ I(t) ≠ ψ ⇒
       I'(t) = I(t) - 1 *)

    (forall (t : Trans)
            (itval : TimeInterval),
        In (t, active itval) s.(d_intervals) ->
        IsSensitized sitpn s.(marking) t ->
        In (t, false) s.(reset) ->
        ~In t s.(fired) ->
        In (t, active (dec_itval itval)) s'.(d_intervals)) ->
    
    (* Time intervals stay the same for all transitions with a blocked
       time interval that are sensitized by m, didn't receive a reset
       order and were not fired at the last clock cycle, i.e:
      
       ∀ t ∈ Ti, t ∈ sens(m) ∧ reset(t) = 0 ∧ t ∉ Fired ∧ I(t) = ψ ⇒
       I'(t) = I(t) *)

    (forall (t : Trans),
        In (t, blocked) s.(d_intervals) ->
        IsSensitized sitpn s.(marking) t ->
        In (t, false) s.(reset) ->
        ~In t s.(fired) ->
        In (t, blocked) s'.(d_intervals)) ->
        
    (* Time intervals are reset for all transitions with a time
       interval (either active or blocked) that are not sensitized by
       m, i.e:
      
       ∀ t ∈ Ti, t ∉ sens(m) ⇒ I'(t) = Is(t) - 1 *)
    
    (forall (t : Trans)
            (itval : TimeInterval),
        In t (fst (split s.(d_intervals))) ->
        ~IsSensitized sitpn s.(marking) t ->
        Some itval = (s_intervals sitpn t) ->
        In (t, active (dec_itval itval)) s'.(d_intervals)) ->

    (* Reset orders stay the same. *)
    
    s.(reset) = s'.(reset) ->
    
    (* All transitions that are not firable are not fired, i.e:

       ∀ t ∉ firable(s') ⇒ t ∉ Fired' *)
    
    (forall (pgroup : list Trans)
            (t : Trans),
        In pgroup sitpn.(priority_groups) ->
        In t pgroup ->
        ~SitpnIsFirable sitpn s' t ->
        ~In t s'.(fired)) ->

    (* If t is firable and sensitized by the residual marking, result
       of the firing of all higher priority transitions, then t is
       fired, i.e: 

       ∀ t ∈ firable(s'), t ∈ sens(M - ∑ pre(t'), ∀ t'∈ Pr(t)) ⇒ t ∈ Fired' 
       where Pr(t) = {ti | ti ≻ t /\ ti ∈ Fired'} *)
    
    (forall (pgroup : list Trans)
            (t : Trans)
            (residual_marking : list (Place * nat)),
        In pgroup sitpn.(priority_groups) ->
        In t pgroup ->
        SitpnIsFirable sitpn s' t ->
        (forall (pr : list Trans),
            IsPrioritySet s'.(fired) pgroup t pr ->
            (forall (p : Place)
                    (n : nat),
                In (p, n) s.(marking) ->
                In (p, n - pre_sum sitpn p pr) residual_marking)) ->
        IsSensitized sitpn residual_marking t ->
        In t s'.(fired)) ->
    
    (* If t is firable and not sensitized by the residual marking then
       t is not fired, i.e:

       ∀ t ∈ firable(s'), t ∉ sens(M - ∑ pre(t'), ∀ t' ∈ Pr(t)) ⇒ t ∉
       Fired' *)
    
    (forall (pgroup : list Trans)
            (t : Trans)
            (residual_marking : list (Place * nat)),
        In pgroup sitpn.(priority_groups) ->
        In t pgroup ->
        SitpnIsFirable sitpn s' t ->
        (forall (pr : list Trans),
            IsPrioritySet s'.(fired) pgroup t pr ->
            (forall (p : Place)
                    (n : nat),
                In (p, n) s'.(marking) ->
                In (p, n - pre_sum sitpn p pr) residual_marking)) ->
        ~IsSensitized sitpn residual_marking t ->
        ~In t s'.(fired)) ->

    SitpnSemantics sitpn s s' time_value env falling_edge
    
(* ↑clock : s = (Fired, m, cond, ex, I, reset) ⇝ s' = (Fired, m', cond, ex', I', reset') *)
                  
| SitpnSemantics_rising_edge :

    IsWellDefinedSitpn sitpn ->
    IsWellDefinedSitpnState sitpn s ->
    IsWellDefinedSitpnState sitpn s' ->
    
    (* Fired stays the same between state s and s'. *)
    s.(fired) = s'.(fired) ->
    
    (* M' = M - ∑ (pre(t_i) - post(t_i)), ∀ t_i ∈ Fired *)
    (forall (p : Place)
            (n : nat),
        In (p, n) s.(marking) ->
        In (p, n - (pre_sum sitpn p s.(fired)) + (post_sum sitpn p s.(fired)))
           s'.(marking)) ->

    (* All transitions disabled by the transient marking, result of
       the withdrawal of tokens in the input places of the fired
       transitions, receive a reset order, i.e: 
     
       ∀ t ∉ sens(m - ∑ pre(ti), ∀ ti ∈ Fired) ⇒ reset'(t) = 1 *)

    (forall (t : Trans)
            (transient_marking : list (Place * nat)),
        (forall (p : Place) (n : nat),
            In (p, n) s.(marking) ->
            In (p, n - pre_sum sitpn p s.(fired)) transient_marking) ->
        In t sitpn.(transs) ->
        ~IsSensitized sitpn transient_marking t ->
        In (t, true) s'.(reset)) ->

    (* All transitions enabled by the transient marking receive no
       reset order, i.e: 

       ∀ t ∈ sens(m - ∑ pre(ti), ∀ ti ∈ Fired) ⇒ reset'(t) = 0 *)

    (forall (t : Trans)
            (transient_marking : list (Place * nat)),
        (forall (p : Place) (n : nat),
            In (p, n) s.(marking) ->
            In (p, n - pre_sum sitpn p s.(fired)) transient_marking) ->
        In t sitpn.(transs) ->
        IsSensitized sitpn transient_marking t ->
        In (t, false) s'.(reset)) ->

    (* Time intervals are blocked for all transitions that have
       reached the upper bound of their time intervals and were not
       fired at this clock cycle, i.e:  
     
       ∀ t ∈ T, ↑I(t) = 0 ∧ t ∉ Fired ⇒ I'(t) = ψ *)
    
    (forall (t : Trans)
            (dyn_itval : DynamicTimeInterval),
        In (t, dyn_itval) s.(d_intervals) ->
        HasReachedUpperBound dyn_itval ->
        ~In t s.(fired) ->
        In (t, blocked) s'.(d_intervals)) ->

    (* Time intervals stay the same for all transitions that haven't
       reached the upper bound of their time intervals or were
       fired at this clock cycle, i.e:  
     
       ∀ t ∈ T, ↑I(t) ≠ 0 ∨ t ∈ Fired ⇒ I'(t) = I(t) *)
    
    (forall (t : Trans)
            (dyn_itval : DynamicTimeInterval),
        In (t, dyn_itval) s.(d_intervals) ->
        (~HasReachedUpperBound dyn_itval \/ In t s.(fired)) ->
        In (t, dyn_itval) s'.(d_intervals)) ->

    (* Condition values stay the same. *)

    s.(cond_values) = s'.(cond_values) ->

    (* Action activation states stay the same. *)

    s.(exec_a) = s'.(exec_a) ->
    
    (* All functions associated with fired transitions are executed, i.e: 

       ∀ f ∈ functions, ∃ t ∈ Fired | F(t, f) = 1 ⇒ ex'(f) = 1. *)

    (forall (f : IFunction),
        In f sitpn.(functions) ->
        exists (t : Trans),
          In t s.(fired) /\ (has_function sitpn t f) = true ->
          In (f, true) s'.(exec_f)) ->

    (* All functions not associated with fired transitions not are
       executed, i.e:

       ∀ f ∈ functions, ∀ t ∈ Fired | F(t, f) = 0 ⇒ ex'(f) = 0. *)

    (forall (f : IFunction)
            (t : Trans),
        In f sitpn.(functions) ->
        In t s.(fired) /\ (has_function sitpn t f) = false ->
        In (f, false) s'.(exec_f)) ->
    
    SitpnSemantics sitpn s s' time_value env rising_edge.



