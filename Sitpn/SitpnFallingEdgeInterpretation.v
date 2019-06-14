(* Import Sitpn material. *)

Require Import Hilecop.Sitpn.Sitpn.
Require Import Hilecop.Sitpn.SitpnTokenPlayer.
Require Import Hilecop.Sitpn.SitpnSemantics.

(* Import lemmas on synchronous execution rules. *)

Require Import Hilecop.Sitpn.SitpnFallingEdgeFired.

(* Import Sitpn tactics, and misc. lemmas. *)

Require Import Hilecop.Sitpn.SitpnTactics.
Require Import Hilecop.Utils.HilecopLemmas.

(** * Falling Edge Lemmas about Interpretation-Related Semantics Rules. *) 

(** ** All conditions are referenced in the condition values list. *)

Section SitpnFallingEdgeSameStructCondv.

  (** [get_condition_values] returns a list of condition values
      referencing all conditions defined in [conditions]. *)

  Lemma get_condition_values_same_struct_condv :
    forall (conditions : list Condition)
           (time_value : nat)
           (env : Condition -> nat -> bool)
           (cond_values : list (Condition * bool)),
      (fst (split cond_values)) ++ conditions =
      (fst (split (get_condition_values conditions time_value env cond_values))).
  Proof.
    intros conditions time_value env cond_values;
      functional induction (get_condition_values conditions time_value env cond_values)
                 using get_condition_values_ind.

    (* BASE CASE. *)
    - rewrite app_nil_r; reflexivity.

    (* INDUCTION CASE. *)
    - rewrite <- IHl;
        rewrite fst_split_app;
        simpl;
        rewrite <- app_assoc;
        reflexivity.
  Qed.
  
  (** All conditions defined in [sitpn] are referenced in the
      condition values list [s'.(cond_values)], where [s'] is the
      SitpnState returned by [sitpn_falling_edge] *)

  Lemma sitpn_falling_edge_same_struct_condv :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (time_value : nat)
           (env : Condition -> nat -> bool)
           (s' : SitpnState),
      sitpn_falling_edge sitpn s time_value env = Some s' ->
      (conditions sitpn) = (fst (split (cond_values s'))).
  Proof.
    intros sitpn s time_value env s' Hfun.
    functional induction (sitpn_falling_edge sitpn s time_value env)
               using sitpn_falling_edge_ind;

    (* GENERAL CASE, all went well. *)
    (simpl in Hfun;
     injection Hfun as Heq_s';
     rewrite <- Heq_s';
     simpl;
     rewrite <- (get_condition_values_same_struct_condv
                   (conditions sitpn) time_value env []);
     simpl;
     reflexivity)
      
    (* ERROR CASE *)
    || inversion Hfun.
  Qed.
  
End SitpnFallingEdgeSameStructCondv.

(** ** All actions are referenced in the action states list. *)

Section SitpnFallingEdgeSameStructActions.

  (** [get_action_states] returns a list of couples (action, state)
      referencing all actions defined in [actions]. *)

  Lemma get_action_states_same_struct_actions :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (actions : list Action)
           (a_states : list (Action * bool)),
      (fst (split a_states)) ++ actions =
      (fst (split (get_action_states sitpn s actions a_states))).
  Proof.
    intros sitpn s actions a_states;
      functional induction (get_action_states sitpn s actions a_states)
                 using get_action_states_ind.

    (* BASE CASE. *)
    - rewrite app_nil_r; reflexivity.

    (* INDUCTION CASE. *)
    - rewrite <- IHl;
        rewrite fst_split_app;
        simpl;
        rewrite <- app_assoc;
        reflexivity.
  Qed.
  
  (** All actions defined in [sitpn] are referenced in the
      action states list [s'.(exec_a)], where [s'] is the
      SitpnState returned by [sitpn_falling_edge] *)

  Lemma sitpn_falling_edge_same_struct_actions :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (time_value : nat)
           (env : Condition -> nat -> bool)
           (s' : SitpnState),
      sitpn_falling_edge sitpn s time_value env = Some s' ->
      (actions sitpn) = (fst (split (exec_a s'))).
  Proof.
    intros sitpn s time_value env s' Hfun.
    functional induction (sitpn_falling_edge sitpn s time_value env)
               using sitpn_falling_edge_ind;

    (* GENERAL CASE, all went well. *)
    (simpl in Hfun;
     injection Hfun as Heq_s';
     rewrite <- Heq_s';
     simpl;
     rewrite <- (get_action_states_same_struct_actions sitpn s (actions sitpn) []);
     simpl;
     reflexivity)
      
    (* ERROR CASE *)
    || inversion Hfun.
  Qed.
  
End SitpnFallingEdgeSameStructActions.

(** ** Function states stay the same on falling edge. *)

Section SitpnFallingEdgeSameFunctions.

  (** [sitpn_falling_edge] returns a SitpnState with the same function
      states list [exec_f] as in the starting state. *)

  Lemma sitpn_falling_edge_same_functions :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (time_value : nat)
           (env : Condition -> nat -> bool)
           (s' : SitpnState),
      sitpn_falling_edge sitpn s time_value env = Some s' ->
      (exec_f s) = (exec_f s').
  Proof.
    intros sitpn s time_value env s' Hfun.
    functional induction (sitpn_falling_edge sitpn s time_value env)
               using sitpn_falling_edge_ind;

    (* GENERAL CASE, all went well. *)
    (simpl in Hfun;
     injection Hfun as Heq_s';
     rewrite <- Heq_s';
     simpl;
     reflexivity)
      
    (* ERROR CASE *)
    || inversion Hfun.
  Qed.
  
End SitpnFallingEdgeSameFunctions.

(** ** Condition values are retrieved for all conditions. *)

Section SitpnFallingEdgeGetCondv.

  (** All couple (cond, bool) that are in [cond_values]
      are in the final list returned by [get_condition_values]. *)

  Lemma get_condition_values_in_condv :
    forall (conditions : list Condition)
           (time_value : nat)
           (env : Condition -> nat -> bool)
           (cond_values : list (Condition * bool))
           (c : Condition)
           (b : bool),
      In (c, b) cond_values ->
      In (c, b) (get_condition_values conditions time_value env cond_values).
  Proof.
    intros conditions time_value env cond_values;
      functional induction (get_condition_values conditions time_value env cond_values)
                 using get_condition_values_ind;
      intros cond b Hin_condv.

    (* BASE CASE. *)
    - assumption.

    (* INDUCTION CASE. *)
    - apply or_introl with (B := (In (cond, b) [(c, env c time_value)])) in Hin_condv.
      apply in_or_app in Hin_condv.
      apply (IHl cond b Hin_condv).
  Qed.
      
  (** All conditions in [conditions] are associated to the boolean value
      [env c time_value] in the list returned by [get_condition_values]. *)

  Lemma get_condition_values_cons :
    forall (conditions : list Condition)
           (time_value : nat)
           (env : Condition -> nat -> bool)
           (cond_values : list (Condition * bool))
           (c : Condition),
      In c conditions ->
      In (c, env c time_value) (get_condition_values conditions time_value env cond_values).
  Proof.
    intros conditions time_value env cond_values;
      functional induction (get_condition_values conditions time_value env cond_values)
                 using get_condition_values_ind;
      intros cond Hin_conds.

    (* BASE CASE *)
    - inversion Hin_conds.

    (* INDUCTION CASE *)
    - inversion_clear Hin_conds as [Heq_cond | Hin_tl].

      (* Case c = cond *)
      + rewrite <- Heq_cond.

        (* Builds In (c, env) (cond_values ++ [(c, env)]) *)
        assert (Hin_condv: In (c, env c time_value) (cond_values ++ [(c, env c time_value)]))
          by (apply in_or_app; right; apply in_eq).

        (* Applies get_condition_values_in_condv. *)
        apply (get_condition_values_in_condv
                 tl time_value env (cond_values ++ [(c, env c time_value)])
                 c (env c time_value) Hin_condv).

      (* Case cond ∈ tl *)
      + apply (IHl cond Hin_tl).
  Qed.
        
  (** All condition values at the current time [time_value] are retrieved
      and put in the [s'.(cond_values)] list, where [s'] is the SitpnState
      returned by [sitpn_falling_edge]. *)

  Lemma sitpn_falling_edge_get_condv :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (time_value : nat)
           (env : Condition -> nat -> bool)
           (s' : SitpnState),
      sitpn_falling_edge sitpn s time_value env = Some s' ->
      (forall (c : Condition),
          In c sitpn.(conditions) ->
          In (c, (env c time_value)) s'.(cond_values)).
  Proof.
    intros sitpn s time_value env;
      functional induction (sitpn_falling_edge sitpn s time_value env)
                 using sitpn_falling_edge_ind;
      intros s' Hfun;

    (* GENERAL CASE *)
    (simpl in Hfun;
     injection Hfun as Heq_s';
     rewrite <- Heq_s';
     simpl;
     apply get_condition_values_cons)

    (* ERROR CASE *)
    || inversion Hfun.
  Qed.
  
End SitpnFallingEdgeGetCondv.
