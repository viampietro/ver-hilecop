(** * Sitpn semantics definition. *)

Require Import common.Coqlib.
Require Import common.GlobalTypes.
Require Import ListsPlus.
Require Import dp.Sitpn.
Require Import dp.SitpnTypes.
Require Import dp.SitpnSemanticsDefs.
Require Import dp.Fired.

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

Inductive SitpnStateTransition sitpn (E : nat -> C sitpn -> bool) (τ : nat) (s s' : SitpnState sitpn) : Clk -> Prop :=
| SitpnStateTransition_falling :

    (** Captures the new value of conditions, and determines the
        activation status for actions.  *)
    (forall c, (cond s' c) = (E τ c)) ->
    (forall a, (exists p, (M s p) > 0 /\ has_A p a = true) -> (ex s' (inl a)) = true) ->
    (forall a, (forall p, (M s p) = 0 \/ has_A p a = false) -> (ex s' (inl a)) = false) ->

    (* Equivalent to the two lines above. *)
    (forall a marked sum, @Set_in_List (P sitpn) (fun p => M s p > 0) marked ->
                          BSum (fun p => has_A p a) marked sum ->
                          ex s' (inl a) = sum) ->

    (** Updates the dynamic time intervals according to the firing
       status of transitions and the reset orders. *)
    (forall (t : Ti sitpn), ~Sens (M s) t -> I s' t = 0) ->
    (forall (t : Ti sitpn), Sens (M s) t -> reset s t = true -> I s' t = 1) ->
    (forall (t : Ti sitpn),
        Sens (M s) t ->
        reset s t = false ->
        (TcLeUpper s t \/ upper t = i+) -> I s' t = S (I s t)) ->
    (forall (t : Ti sitpn),
        Sens (M s) t ->
        reset s t = false ->
        (upper t <> i+ /\ TcGtUpper s t) -> I s' t = S (I s t)) ->

    (** Marking stays the same between s and s'. *)
    (forall p, M s p = M s' p) -> 

    (** Reset orders stay the same between s and s'. *)
    (forall t, reset s t = reset s' t) ->

    (** Function states stay the same between s and s'. *)
    (forall f, ex s (inr f) = ex s' (inr f)) ->
    
    (** Conclusion *)
    SitpnStateTransition E τ s s' falling_edge

| SitpnStateTransition_rising:

    (** Marking at state s' is the new marking resulting of the firing
        of all transitions belonging to the Fired subset at state
        s. *)  
    (forall fired, IsNewMarking s fired (M s')) ->

    (** Computes the reset orders for time counters and fired transitions. *)
    (forall (t : Ti sitpn) fired m,
        IsTransientMarking s fired m ->
        (Sens (M s) t /\ ~Sensbt m t \/ Fired s fired t) -> reset s' t = true) ->
    
    (forall (t : Ti sitpn) fired m,
        IsTransientMarking s fired m ->
        (~Sens (M s) t \/ Sensbt m t) ->
        ~Fired s fired t -> reset s' t = false) ->

    (** Determines if some functions are executed. *)
    (forall f fired, (exists t, Fired s fired t /\ has_F t f = true) -> ex s' (inr f) = true) ->
    (forall f fired, (forall t, ~Fired s fired t \/ has_F t f = false) -> ex s' (inr f) = false) ->

    (* Equivalent to the two lines above. *)
    (forall f fired sum, IsFiredList s fired -> BSum (fun t => has_F t f) fired sum -> ex s' (inr f) = sum) ->
    
    (** Condition values stay the same between s and s'. *)
    (forall c, cond s' c = cond s c) -> 
    
    (** Action states stay the same between s and s'. *)
    (forall a, ex s' (inl a) = ex s (inl a)) ->
    
    (** Conclusion *)
    SitpnStateTransition E τ s s' rising_edge.    

(** ** SITPN Execution Relations *)

(** Defines the SITPN Cycle Relation. 
    Relates two SitpnState over one cycle of execution.
 *)

Definition SitpnCycle sitpn (E : nat -> C sitpn -> bool) (τ : nat) (s s'' : SitpnState sitpn) :=
  exists s', SitpnStateTransition E τ s s' rising_edge /\ SitpnStateTransition E τ s' s'' falling_edge.

(** Defines the SITPN Execution Relation. *)

Inductive SitpnExecute sitpn (E : nat -> C sitpn -> bool) (s : SitpnState sitpn) : nat -> list (SitpnState sitpn) -> Prop :=
| SitpnExecute_end : SitpnExecute E s 0 []
| SitpnExecute_loop: forall τ θ s',
    SitpnCycle E (S τ) s s' ->
    SitpnExecute E s' τ θ ->
    SitpnExecute E s (S τ) (s' :: θ).

(** Defines the initial state of an SITPN. *)

Definition s0 sitpn : SitpnState sitpn :=
  BuildSitpnState (@M0 sitpn) (fun _ => 0) nullb nullb nullb.

(** Defines a full execution relation for an SITPN, i.e, starting from
    the initial state of an SITPN. *)

Inductive SitpnFullExec
          (sitpn : Sitpn)
          (E : nat -> C sitpn -> bool) :
  nat -> list (SitpnState sitpn) -> Prop :=
| SitpnFullExec_0 :
    @SitpnFullExec sitpn E 0 [s0 sitpn]
| SitpnFullExec_cons :
    forall τ θ s,

      (* First cycle of execution. Only the falling edge is taken into
         account, since on the first rising edge there are no fired
         transitions. *)
      SitpnStateTransition E (S τ) (s0 sitpn) s falling_edge ->

      (* Executes τ cycles *)
      SitpnExecute E s τ θ ->

      (* Conclusion *)
      @SitpnFullExec sitpn E (S τ) ((s0 sitpn) :: s :: θ).


