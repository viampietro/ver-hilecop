(* Import SPN, STPN types modules. *)

Require Import Hilecop.Spn.Spn.
Require Import Hilecop.Stpn.Stpn.

(* Import SPN semantics module. *)

Require Import Hilecop.Spn.SpnSemantics.

(** HasReachedTimeWindow: 

    True if [t] is associated with an optional
    time interval in [intervals] that is either
    equal to [None], or is an active time
    interval with [min_t] = 0 (≡ 0 ∈ I). *)

Definition HasReachedTimeWindow
           (intervals : list (Trans * option DynamicTimeInterval))
           (t : Trans) :=
  forall opt_itval : option DynamicTimeInterval,
    In (t, opt_itval) intervals ->
    match opt_itval with
    | None => True
    | Some dyn_itval =>
      match dyn_itval with
      | active {| min_t := 0; max_t := _ |} => True
      | _ => False
      end 
    end.           
    
(** StpnIsFirable: expresses the firability of transition t for STPN
                   stpn at state s.
 
    ∀ t ∈ T, s = (Fired, M, I, reset), t ∈ firable(s) if 
    t ∈ sens(M) ∧ 0 ∈ I(t).
    
    t is firable at state s of STPN stpn if M sensitizes t, and if t
    has reached a specific time window. *)

Definition StpnIsFirable
           (stpn : Stpn)
           (s : StpnState)
           (t : Trans) :=
  IsSensitized stpn s.(marking) t /\
  HasReachedTimeWindow s.(intervals) t.

(** Decrements the bounds of a time interval. *)

Definition dec_itval (itval : TimeInterval) :=
  match itval with
  | {| min_t := n; max_t := pos_val m |} =>
    {| min_t := n - 1; max_t := pos_val (m - 1) |}
  | {| min_t := n; max_t := pos_inf |} =>
    {| min_t := n - 1; max_t := pos_inf |}
  end.

(* Tests if the upper bound of a time interval equals 0. 
   Useful when determining if a dynamic time interval 
   should be blocked. *)

Definition HasReachedMaxBound (itval : TimeInterval) :=
  match itval with
  | {| min_t := _; max_t := pos_val 0 |} => True
  | _ => False
  end.

(** * Stpn Semantics definition *)

Inductive StpnSemantics (stpn : Stpn) (s s' : StpnState) : Clock -> Prop :=

(* ↓clock : s = (Fired, m, I, reset) ⇝ s' = (Fired', m, I', reset) *)
  
| StpnSemantics_falling_edge :

    IsWellDefinedStpn stpn ->
    IsWellDefinedStpnState stpn s ->
    IsWellDefinedStpnState stpn s' ->

    (* Marking stays the same between state s and s'. *)
    s.(marking) = s'.(marking) ->
    
    (* Time intervals are reset for all transitions with a time
       interval (either active or blocked) that are sensitized by m
       and either received a reset order or were previously fired.
      
       ∀ t ∈ Ti, t ∈ sens(m) ∧ (reset(t) = 1 ∨ t ∈ Fired) ⇒ I'(t) =
       Is(t) - 1 where Ti = { ti | I(ti) ≠ ∅ } *)
    
    (forall (t : Trans)
            (itval : TimeInterval),
        In (t, Some itval) stpn.(static_intervals) ->
        IsSensitized stpn s.(marking) t ->
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
        IsSensitized stpn s.(marking) t ->
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
        IsSensitized stpn s.(marking) t ->
        In (t, false) s.(reset) ->
        ~In t s.(fired) ->
        In (t, Some blocked) s'.(intervals)) ->

    (* Time intervals are reset for all transitions with a time
       interval (either active or blocked) that are not sensitized by
       m.
      
       ∀ t ∈ Ti, t ∉ sens(m) ⇒ I'(t) = Is(t) - 1 *)
    
    (forall (t : Trans)
            (itval : TimeInterval),
        In (t, Some itval) stpn.(static_intervals) ->
        ~IsSensitized stpn s.(marking) t ->
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
        In pgroup stpn.(priority_groups) ->
        In t pgroup ->
        ~StpnIsFirable stpn s' t ->
        ~In t s'.(fired)) ->

    (* If t is firable and sensitized by the residual marking, result
       of the firing of all higher priority transitions, then t is
       fired, i.e: 
       ∀ t ∈ firable(s'), t ∈ sens(M - ∑ pre(t'), ∀ t'∈ Pr(t)) ⇒ t ∈ Fired' *)
    
    (forall (pgroup : list Trans)
            (t : Trans)
            (residual_marking : list (Place * nat)),
        In pgroup stpn.(priority_groups) ->
        In t pgroup ->
        MarkingHaveSameStruct stpn.(initial_marking) residual_marking ->
        StpnIsFirable stpn s' t ->
        (forall (pr : list Trans),
            NoDup pr ->
            (forall t' : Trans,
                HasHigherPriority stpn t' t pgroup /\ In t' s'.(fired) <-> In t' pr) ->
            (forall (p : Place)
                    (n : nat),
                In (p, n) s'.(marking) ->
                In (p, n - pre_sum stpn p pr) residual_marking)) ->
        IsSensitized stpn residual_marking t ->
        In t s'.(fired)) ->
    
    (* If t is firable and not sensitized by the residual marking then t is not fired, i.e: 
       ∀ t ∈ firable(s'), t ∉ sens(M - ∑ pre(t'), ∀ t' ∈ Pr(t)) ⇒ t ∉ Fired' *)
    
    (forall (pgroup : list Trans)
            (t : Trans)
            (residual_marking : list (Place * nat)),
        In pgroup stpn.(priority_groups) ->
        In t pgroup ->
        MarkingHaveSameStruct stpn.(initial_marking) residual_marking ->
        StpnIsFirable stpn s' t ->
        (forall (pr : list Trans),
            NoDup pr ->
            (forall t' : Trans,
                HasHigherPriority stpn t' t pgroup /\ In t' s'.(fired) <-> In t' pr) ->
            (forall (p : Place)
                    (n : nat),
                In (p, n) s'.(marking) ->
                In (p, n - pre_sum stpn p pr) residual_marking)) ->
        ~IsSensitized stpn residual_marking t ->
        ~In t s'.(fired)) ->
    
    StpnSemantics stpn s s' falling_edge

(* ↑clock : s = (Fired, m, I, reset) ⇝ s' = (Fired, m', I', reset') *)
                  
| StpnSemantics_rising_edge :

    IsWellDefinedStpn stpn ->
    IsWellDefinedStpnState stpn s ->
    IsWellDefinedStpnState stpn s' ->
    
    (* Fired stays the same between state s and s'. *)
    s.(fired) = s'.(fired) ->
    
    (* M' = M - ∑ (pre(t_i) - post(t_i)), ∀ t_i ∈ Fired *)
    (forall (p : Place)
            (n : nat),
        In (p, n) s.(marking) ->
        In (p, n - (pre_sum stpn p s.(fired)) + (post_sum stpn p s.(fired))) s'.(marking)) ->

    (* All transitions disabled by the transient marking, result of
       the withdrawal of tokens in the input places of the fired
       transitions, receive a reset order, i.e: 
     
       ∀ t ∉ sens(m - ∑ pre(ti), ∀ ti ∈ Fired) ⇒ reset'(t) = 1 *)

    (forall (t : Trans)
            (transient_marking : list (Place * nat)),
        (forall (p : Place) (n : nat),
          In (p, n) s.(marking) ->
          In (p, n - pre_sum stpn p s.(fired)) transient_marking) ->
        MarkingHaveSameStruct s.(marking) transient_marking ->
        In t stpn.(transs) ->
        ~IsSensitized stpn transient_marking t ->
        In (t, true) s'.(reset)) ->

    (* All transitions enabled by the transient marking receive no
       reset order, i.e: 

       ∀ t ∈ sens(m - ∑ pre(ti), ∀ ti ∈ Fired) ⇒ reset'(t) = 0 *)

    (forall (t : Trans)
            (transient_marking : list (Place * nat)),
        (forall (p : Place) (n : nat),
            In (p, n) s.(marking) ->
            In (p, n - pre_sum stpn p s.(fired)) transient_marking) ->
        MarkingHaveSameStruct s.(marking) transient_marking ->
        In t stpn.(transs) ->
        IsSensitized stpn transient_marking t ->
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
    
    StpnSemantics stpn s s' rising_edge.

    
