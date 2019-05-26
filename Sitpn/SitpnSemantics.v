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
           (sitpn : Sitpn)
           (t t' : Trans)
           (pgroup : list Trans) :=
  In pgroup sitpn.(priority_groups) /\
  In t pgroup /\
  In t' pgroup /\
  IsPredInNoDupList t t' pgroup.

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
    interval with [min_t] = 0 (≡ 0 ∈ I). *)

Definition HasReachedTimeWindow
           (d_intervals : list (Trans * DynamicTimeInterval))
           (t : Trans) :=
  forall (upper_bound : PositiveIntervalBound),
    In (t, active {| min_t := 0; max_t := upper_bound |}) d_intervals.

(** Tests if the upper bound of a time interval equals 0. 
    Useful when determining if a dynamic time interval 
    should be blocked. *)

Definition HasReachedMaxBound (itval : TimeInterval) :=
  itval = {| min_t := 0; max_t := pos_val 0 |}.

(** Decrements the bounds of a time interval. *)

Definition dec_itval (itval : TimeInterval) :=
  match itval with
  | {| min_t := n; max_t := pos_val m |} =>
    {| min_t := n - 1; max_t := pos_val (m - 1) |}
  | {| min_t := n; max_t := pos_inf |} =>
    {| min_t := n - 1; max_t := pos_inf |}
  end.

(** * Sitpn Semantics definition
    
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

(** Represents the two clock events regulating the Spn evolution. *)

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
    
    (* Time intervals are reset for all transitions with a time
       interval (either active or blocked) that are sensitized by m
       and either received a reset order or were previously fired.
      
       ∀ t ∈ Ti, t ∈ sens(m) ∧ (reset(t) = 1 ∨ t ∈ Fired) ⇒ I'(t) =
       Is(t) - 1 where Ti = { ti | I(ti) ≠ ∅ } *)
    
    (forall (t : Trans)
            (itval : TimeInterval),
        In (t, Some itval) sitpn.(static_intervals) ->
        IsSensitized sitpn s.(marking) t ->
        (In (t, true) s.(reset) \/ In t s.(fired)) ->
        In (t, Some (active (dec_itval itval))) s'.(intervals)) ->

    (* Time intervals evolve normally for all transitions with an 
       active time interval that are sensitized by m, didn't receive a reset order 
       and were not fired at the last clock cycle. 
      
       ∀ t ∈ Ti, t ∈ sens(m) ∧ reset(t) = 0 ∧ t ∉ Fired ∧ I(t) ≠ ψ ⇒ 
       I'(t) = I(t) - 1 *)

    (forall (t : Trans)
            (itval : TimeInterval),
        In (t, Some (active itval)) s.(intervals) ->
        IsSensitized sitpn s.(marking) t ->
        In (t, false) s.(reset) ->
        ~In t s.(fired) ->
        In (t, Some (active (dec_itval itval))) s'.(intervals)) ->

    (* Time intervals stay the same for all transitions with a blocked
       time interval that are sensitized by m, didn't receive a reset
       order and were not fired at the last clock cycle.
      
       ∀ t ∈ Ti, t ∈ sens(m) ∧ reset(t) = 0 ∧ t ∉ Fired ∧ I(t) = ψ ⇒
       I'(t) = I(t) *)

    (forall (t : Trans),
        In (t, Some blocked) s.(intervals) ->
        IsSensitized sitpn s.(marking) t ->
        In (t, false) s.(reset) ->
        ~In t s.(fired) ->
        In (t, Some blocked) s'.(intervals)) ->

    (* Time intervals are reset for all transitions with a time
       interval (either active or blocked) that are not sensitized by
       m.
      
       ∀ t ∈ Ti, t ∉ sens(m) ⇒ I'(t) = Is(t) - 1 *)
    
    (forall (t : Trans)
            (itval : TimeInterval),
        In (t, Some itval) sitpn.(static_intervals) ->
        ~IsSensitized sitpn s.(marking) t ->
        In (t, Some (active (dec_itval itval))) s'.(intervals)) ->

    (* Transitions with no time intervals at state s 
       have still no time intervals at state s'. *)
    
    (forall (t : Trans),
        In (t, None) s.(intervals) ->
        In (t, None) s'.(intervals)) ->
    
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
       ∀ t ∈ firable(s'), t ∈ sens(M - ∑ pre(t'), ∀ t'∈ Pr(t)) ⇒ t ∈ Fired' *)
    
    (forall (pgroup : list Trans)
            (t : Trans)
            (residual_marking : list (Place * nat)),
        In pgroup sitpn.(priority_groups) ->
        In t pgroup ->
        MarkingHaveSameStruct sitpn.(initial_marking) residual_marking ->
        SitpnIsFirable sitpn s' t ->
        (forall (pr : list Trans),
            NoDup pr ->
            (forall t' : Trans,
                HasHigherPriority sitpn t' t pgroup /\ In t' s'.(fired) <-> In t' pr) ->
            (forall (p : Place)
                    (n : nat),
                In (p, n) s'.(marking) ->
                In (p, n - pre_sum sitpn p pr) residual_marking)) ->
        IsSensitized sitpn residual_marking t ->
        In t s'.(fired)) ->
    
    (* If t is firable and not sensitized by the residual marking then t is not fired, i.e: 
       ∀ t ∈ firable(s'), t ∉ sens(M - ∑ pre(t'), ∀ t' ∈ Pr(t)) ⇒ t ∉ Fired' *)
    
    (forall (pgroup : list Trans)
            (t : Trans)
            (residual_marking : list (Place * nat)),
        In pgroup sitpn.(priority_groups) ->
        In t pgroup ->
        MarkingHaveSameStruct sitpn.(initial_marking) residual_marking ->
        SitpnIsFirable sitpn s' t ->
        (forall (pr : list Trans),
            NoDup pr ->
            (forall t' : Trans,
                HasHigherPriority sitpn t' t pgroup /\ In t' s'.(fired) <-> In t' pr) ->
            (forall (p : Place)
                    (n : nat),
                In (p, n) s'.(marking) ->
                In (p, n - pre_sum sitpn p pr) residual_marking)) ->
        ~IsSensitized sitpn residual_marking t ->
        ~In t s'.(fired)) ->
    
    SitpnSemantics sitpn s s' falling_edge

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
        MarkingHaveSameStruct s.(marking) transient_marking ->
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
        MarkingHaveSameStruct s.(marking) transient_marking ->
        In t sitpn.(transs) ->
        IsSensitized sitpn transient_marking t ->
        In (t, false) s'.(reset)) ->

    (* Time intervals are blocked for all transitions that have
       reached the upper bound of their time intervals and were not
       fired at this clock cycle, i.e:  
     
       ∀ t ∈ T, ↑I(t) = 0 ∧ t ∉ Fired ⇒ I'(t) = ψ *)
    
    (forall (t : Trans)
            (itval : TimeInterval),
        In (t, Some (active itval)) s.(intervals) ->
        HasReachedMaxBound itval ->
        ~In t s.(fired) ->
        In (t, Some blocked) s'.(intervals)) ->

    (* Time intervals stay the same for all transitions that haven't
       reached the upper bound of their time intervals or were
       fired at this clock cycle, i.e:  
     
       ∀ t ∈ T, ↑I(t) ≠ 0 ∨ t ∈ Fired ⇒ I'(t) = I(t) *)
    
    (forall (t : Trans)
            (itval : TimeInterval),
        In (t, Some (active itval)) s.(intervals) ->
        (~HasReachedMaxBound itval \/ In t s.(fired)) ->
        In (t, Some (active itval)) s'.(intervals)) ->
    
    SitpnSemantics sitpn s s' rising_edge.



