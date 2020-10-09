(** * Sitpn semantics definition. *)

Require Import Coqlib.
Require Import dp.Sitpn.
Require Import SitpnTypes.
Require Import GlobalTypes.
Require Import SitpnSemanticsDefs.
Require Import Fired.

Local Set Implicit Arguments.

Local Notation "| e |" := (exist _ e _) (at level 50).

(** States that marking [m] is the residual marking resulting of the
    withdrawal of the tokens from the input places of transitions that
    belong to the [Fired] field of state s.  *)

Definition IsTransientMarking (sitpn : Sitpn) (s : SitpnState sitpn) (fired : list (T sitpn)) (m : P sitpn -> nat) :=
  MarkingSubPreSum (Fired s fired) (M s) m.

(** States that marking [m] is the residual marking resulting of the
    withdrawal of the tokens from the input places of transitions that
    belong to the [Fired] field of state s.  *)

Definition IsNewMarking (sitpn : Sitpn) (s : SitpnState sitpn) (fired : list (T sitpn)) (m : P sitpn -> nat) :=
  MarkingSubPreSumAddPostSum (Fired s fired) (M s) m.

(** Defines the Sitpn state transition relation. *)

Inductive SitpnStateTransition sitpn (E : nat -> C sitpn -> bool) (tau : nat) (s s' : SitpnState sitpn) : Clk -> Prop :=
| SitpnStateTransition_falling :

    (** Captures the new value of conditions, and determines the
        activation status for actions.  *)
    (forall c, (cond s' c) = (E tau c)) ->
    (forall a, (exists p, (M s p) > 0 /\ has_A p a = true) -> (exa s' a) = true) ->
    (forall a, (forall p, (M s p) = 0 \/ has_A p a = false) -> (exa s' a) = false) ->    

    (** Updates the dynamic time intervals according to the firing
       status of transitions and the reset orders. *)
    (forall (t : Ti sitpn), ~Sens (M s) t -> I s' t = Some 0) ->
    (forall (t : Ti sitpn), Sens (M s) t -> reset s t = true -> I s' t = Some 1) ->
    (forall (t : Ti sitpn) n, Sens (M s) t -> reset s t = false -> I s t = Some n -> I s' t = Some (S n)) ->
    (forall (t : Ti sitpn), Sens (M s) t -> reset s t = false -> I s t = None -> I s' t = None) ->

    (** Marking stays the same between s and s'. *)
    (forall p, M s p = M s' p) -> 

    (** Reset orders stay the same between s and s'. *)
    (forall t, reset s t = reset s' t) ->

    (** Function states stay the same between s and s'. *)
    (forall f, exf s f = exf s' f) ->
    
    (** Conclusion *)
    SitpnStateTransition E tau s s' falling_edge

| SitpnStateTransition_rising:

    (** Marking at state s' is the new marking resulting of the firing
        of all transitions belonging to the Fired subset at state
        s. *)
    forall fired, IsNewMarking s fired (M s') ->

    (** Computes the reset orders for time counters and fired transitions. *)
    (forall (t : Ti sitpn) fired m, IsTransientMarking s fired m -> (~Sens m t \/ Fired s fired t) -> reset s' t = true) ->
    (forall (t : Ti sitpn) fired m, IsTransientMarking s fired m -> Sens m t -> ~Fired s fired t -> reset s' t = false) ->

    (** Determines if some time counters are blocked. *)
    (forall (t : Ti sitpn) fired, HasReachedUpperBound s t -> ~Fired s fired t -> (I s' t) = None) ->
    (forall (t : Ti sitpn) fired, (~HasReachedUpperBound s t \/ Fired s fired t) -> (I s' t) = (I s t)) ->

    (** Determines if some functions are executed. *)
    (forall f fired, (exists t, Fired s fired t /\ has_F t f = true) -> exf s' f = true) ->
    (forall f fired, (forall t, ~Fired s fired t \/ has_F t f = false) -> exf s' f = true) -> 
    
    (** Condition values stay the same between s and s'. *)
    (forall c, cond s' c = cond s c) -> 
    
    (** Action states stay the same between s and s'. *)
    (forall a, exa s' a = exa s a) ->
    
    (** Conclusion *)
    SitpnStateTransition E tau s s' rising_edge.    

(** ** SITPN Execution Relations *)

(** Defines the SITPN Cycle Relation. 
    Relates two SitpnState over one cycle of execution.
 *)

Definition SitpnCycle sitpn (E : nat -> C sitpn -> bool) (τ : nat) (s s'' : SitpnState sitpn) :=
  exists s', SitpnStateTransition E τ s s' rising_edge /\ SitpnStateTransition E τ s' s'' falling_edge.

(** Defines the SITPN Execution Relation. *)

Inductive SitpnExecute sitpn (E : nat -> C sitpn -> bool) (s : SitpnState sitpn) : nat -> list (SitpnState sitpn) -> SitpnState sitpn -> Prop :=
| SitpnExecute_end : SitpnExecute E s 0 [] s
| SitpnExecute_loop: forall τ θ s' s'',
    SitpnCycle E (S τ) s s' ->
    SitpnExecute E s' τ θ s'' ->
    SitpnExecute E s (S τ) (s' :: θ) s''.

(** Defines the initial state of an SITPN. *)

Definition s0 sitpn : SitpnState sitpn :=
  BuildSitpnState (@M0 sitpn) (fun _ => Some 0) nullb nullb nullb nullb.

(** Defines a complete execution process for an SITPN, i.e, starting
    from the initial state of an SITPN. *)

Inductive SitpnExecWf
          (sitpn : Sitpn)
          (E : nat -> C sitpn -> bool) :
  nat -> list (SitpnState sitpn) -> Prop :=
| SitpnExecWf_0 :
    @SitpnExecWf sitpn E 0 []
| SitpnExecWf_cons :
    forall τ θ s s',

      (* First cycle of execution. Only the falling edge is taken into
         account, since on the first rising edge there are no fired
         transitions. *)
      SitpnStateTransition E (S τ) (s0 sitpn) s falling_edge ->

      (* Executes τ cycles *)
      SitpnExecute E s τ θ s' ->

      (* Conclusion *)
      @SitpnExecWf sitpn E (S τ) θ.


