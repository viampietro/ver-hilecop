(*! ================================== !*)
(*! ======= SITPN TOKEN PLAYER ======= !*)
(*! ================================== !*)

(* Import Sitpn and Sitpn state structures. *)

Require Import Hilecop.Sitpn.Sitpn.

(* Import Sitpn semantics. *)

Require Import Hilecop.Sitpn.SitpnSemantics.

Set Implicit Arguments.

(** * General helper functions. *)

Section SitpnHelperFunctions.

  Variable A B : Type.

  (** Returns the value associated to key [key] in list [l],
      or error (None) if [key] is not in [l]. *)
  
  Fixpoint get_value
           (eq_dec : forall (x y : A), {x = y} + {x <> y})
           (key : A)
           (l : list (A * B)) {struct l} : option B :=
    match l with
    | (x, value) :: tl =>
      if eq_dec x key then
        Some value
      else get_value eq_dec key tl
    (* Error, key is not in l. *)
    | [] => None
    end.

  Functional Scheme get_value_ind := Induction for get_value Sort Prop.

  (** Replaces the couple (key, old_value) by the couple (key, value)
      in [l], if [key] is referenced in [l]. Raises an error (None)
      otherwise. *)
  
  Fixpoint set_value
           (eq_dec : forall (x y : A), {x = y} + {x <> y})
           (key : A)
           (value : B)
           (l : list (A * B))
           {struct l} : option (list (A * B)) :=
    match l with
    (* eq_dec is evaluated into a boolean expr
     * thanks to the def Bool.Sumbool.bool_of_sumbool *)
    | (x, v) :: tl =>
      if eq_dec x key then
        Some ((key, value) :: tl)
      else
        match set_value eq_dec key value tl with
        | Some l' => Some ((x, v) :: l')
        (* Inductive call returned an error, then error. *)
        | None => None
        end
    (* Key is not in l, then error. *)
    | [] => None
    end.

  Functional Scheme set_value_ind := Induction for set_value Sort Prop.

  (** Functional implementation of the [In] predicate, declared in the
      Coq Standard Library. *)

  Fixpoint in_list
           (eq_dec : forall (x y : A), {x = y} + {x <> y})
           (l : list A)
           (a : A) {struct l} : bool :=
    match l with
    | x :: tl =>
      if eq_dec x a then
        true
      else in_list eq_dec tl a
    | [] => false
    end.
  
End SitpnHelperFunctions.

(** * Functions for Interpretation. *)

Section InterpretationFunctions.

  (** Returns a list of couples (condition, boolean value) denoting
      the value of conditions at time [time_value] according to the
      [env] function. *)
  
  Fixpoint get_condition_values
           (conditions : list Condition)
           (time_value : nat)
           (env : Condition -> nat -> bool)
           (cond_values : list (Condition * bool)) {struct conditions} :
    list (Condition * bool) :=
    match conditions with
    | c :: tl =>
      get_condition_values tl time_value env (cond_values ++ [(c, env c time_value)])
    | [] => cond_values
    end.

  (** Returns true if there exists a place p in marking 
      with at least one token that is associated to action a
      in sitpn. *)
  
  Fixpoint is_activated
           (sitpn : Sitpn)
           (marking : list (Place * nat))
           (a : Action) {struct marking} : bool :=
    match marking with
    | (p, n) :: tl =>
      if (has_action sitpn p a) && (0 <? n) then
        true
      else
        is_activated sitpn tl a
    | [] => false
    end.

  (** Returns the list of couples (action, activated?) --where
      activated? is a boolean-- denoting the activation state of
      all actions of the actions list at state s of sitpn. *)
  
  Fixpoint get_action_states
           (sitpn : Sitpn)
           (s : SitpnState)
           (actions : list Action)
           (a_states : list (Action * bool)) {struct actions} :
    list (Action * bool) :=
  match actions with
  | a :: tl =>
    get_action_states sitpn s tl (a_states ++ [(a, is_activated sitpn s.(marking) a)])
  | [] => a_states
  end.

  (** Returns true if there exists a transition [t] 
      in list [fired] that is associated to function [f]
      in [sitpn]. *)

  Fixpoint is_executed
           (sitpn : Sitpn)
           (fired : list Trans)
           (f : IFunction) {struct fired} : bool :=
  match fired with
  | t :: tl =>
    if has_function sitpn t f then
      true
    else
      is_executed sitpn tl f
  | [] => false
  end.

  (** Returns a list (function, executed?)--where executed? is a
      boolean-- denoting the execution state of all functions of the
      [functions] list at state s of sitpn. *)

  Fixpoint get_function_states
           (sitpn : Sitpn)
           (s : SitpnState)
           (functions : list IFunction)
           (f_states : list (IFunction * bool)) {struct functions} :
    list (IFunction * bool) :=
  match functions with
  | f :: tl =>
    get_function_states sitpn s tl (f_states ++ [(f, is_executed sitpn s.(fired) f)])
  | [] => f_states
  end.
  
End InterpretationFunctions.

(** * Sensitization functions. *)

Section Sensitization.

  (** Returns [Some true] if M(p) >= pre(p, t), [Some false] otherwise. 
                 
      Raises an error (i.e. None) if [get_value] fail. *)
  
  Definition check_pre
             (sitpn : Sitpn)
             (marking : list (Place * nat))
             (p : Place)
             (t : Trans) : option bool :=
    match get_value eq_nat_dec p marking with
    | Some nboftokens => Some ((pre sitpn t p) <=? nboftokens)
    | None => None
    end.

  Functional Scheme check_pre_ind := Induction for check_pre Sort Prop.

  (** Function : Returns [Some true] if ∀ p ∈ [pre_places], M(p) >= pre(p, t).
                 
                 Raises an error if [get_m] fails. *)
  
  Fixpoint map_check_pre_aux
           (sitpn : Sitpn)
           (marking : list (Place * nat))
           (pre_places : list Place)
           (t : Trans)
           (check_result : bool) {struct pre_places} : option bool :=
    match pre_places with
    | p :: tail =>
      match check_pre sitpn marking p t with
      | None => None
      | Some b =>
        map_check_pre_aux sitpn marking tail t (b && check_result)
      end 
    | [] => Some check_result
    end.  

  Functional Scheme map_check_pre_aux_ind := Induction for map_check_pre_aux Sort Prop.

  (** Wrapper around [map_check_pre_aux]. *)
  
  Definition map_check_pre
             (sitpn : Sitpn)
             (marking : list (Place * nat))
             (pre_places : list Place)
             (t : Trans) : option bool :=
    map_check_pre_aux sitpn marking pre_places t true.

  Functional Scheme map_check_pre_ind := Induction for map_check_pre Sort Prop.
  
  (** Returns [Some true] if M(p) >= test(p, t), [Some false] otherwise. 
                 
      Raises an error (i.e. None) if [get_m] fail. *)
  
  Definition check_test
             (sitpn : Sitpn)
             (marking : list (Place * nat))
             (p : Place)
             (t : Trans) : option bool :=
    match get_value eq_nat_dec p marking with
    | Some nboftokens => Some ((test sitpn t p) <=? nboftokens)
    | None => None
    end.

  Functional Scheme check_test_ind := Induction for check_test Sort Prop.
  
  (** Function : Returns [Some true] if ∀ p ∈ [test_places], M(p) >= test(p, t).
                 
                 Raises an error if [get_m] fails. *)
  
  Fixpoint map_check_test_aux
           (sitpn : Sitpn)
           (marking : list (Place * nat))
           (test_places : list Place)
           (t : Trans)
           (check_result : bool) {struct test_places} : option bool :=
    match test_places with
    | p :: tail =>
      match check_test sitpn marking p t with
      | None => None
      | Some b =>
        map_check_test_aux sitpn marking tail t (b && check_result)
      end 
    | [] => Some check_result
    end.  

  Functional Scheme map_check_test_aux_ind := Induction for map_check_test_aux Sort Prop.

  (** Wrapper around [map_check_test_aux]. *)
  
  Definition map_check_test
             (sitpn : Sitpn)
             (marking : list (Place * nat))
             (test_places : list Place)
             (t : Trans) : option bool :=
    map_check_test_aux sitpn marking test_places t true.

  Functional Scheme map_check_test_ind := Induction for map_check_test Sort Prop.
  
  (** Returns [Some true] if M(p) >= inhib(p, t), [Some false] otherwise. 
                 
      Raises an error (i.e. None) if [get_m] fail. *)
  
  Definition check_inhib
             (sitpn : Sitpn)
             (marking : list (Place * nat))
             (p : Place)
             (t : Trans) : option bool :=
    match get_value eq_nat_dec p marking with
    | Some nboftokens => Some ((nboftokens <? (inhib sitpn t p)) || ((inhib sitpn t p) =? 0))
    (* Error: p is not a key in marking. *)
    | None => None
    end.

  Functional Scheme check_inhib_ind := Induction for check_inhib Sort Prop.
  
  (** Function : Returns [Some true] if ∀ p ∈ [inhib_places], M(p) >= inhib(p, t).
                 
                 Raises an error if [get_m] fails. *)
  
  Fixpoint map_check_inhib_aux
           (sitpn : Sitpn)
           (marking : list (Place * nat))
           (inhib_places : list Place)
           (t : Trans)
           (check_result : bool) {struct inhib_places} : option bool :=
    match inhib_places with
    | p :: tail =>
      match check_inhib sitpn marking p t with
      | Some b =>
        map_check_inhib_aux sitpn marking tail t (b && check_result)
      (* Error: p is not a key in marking. *)
      | None => None
      end 
    | [] => Some check_result
    end.  

  Functional Scheme map_check_inhib_aux_ind := Induction for map_check_inhib_aux Sort Prop.
  
  (** Wrapper around [map_check_inhib_aux]. *)
  
  Definition map_check_inhib
             (sitpn : Sitpn)
             (marking : list (Place * nat))
             (inhib_places : list Place)
             (t : Trans) : option bool :=
    map_check_inhib_aux sitpn marking inhib_places t true.

  Functional Scheme map_check_inhib_ind := Induction for map_check_inhib Sort Prop.

  (** Returns [Some true] if [t] is sensitized in marking [marking], 
      [Some false] otherwise. 
                 
      Raises an error if [map_check_pre], [map_check_test], [map_check_inhib] or
      [get_neighbours] fail. *)
  
  Definition is_sensitized
             (sitpn : Sitpn)
             (marking : list (Place * nat))
             (t : Trans) : option bool :=
    let neighbours_of_t := (lneighbours sitpn t) in
    match map_check_pre sitpn marking (pre_pl neighbours_of_t) t with
    | Some check_pre_result =>  
      match map_check_test sitpn marking (test_pl neighbours_of_t) t with
      | Some check_test_result =>
        match map_check_inhib sitpn marking (inhib_pl neighbours_of_t) t with
        | Some check_inhib_result =>
          Some (check_pre_result && check_test_result && check_inhib_result)
        (* Error: some input place of t was not referenced in marking. *)
        | None => None
        end
      (* Error: some input place of t was not referenced in marking. *)
      | None => None
      end
    (* Error: some input place of t was not referenced in marking. *)
    | None => None
    end.

  Functional Scheme is_sensitized_ind := Induction for is_sensitized Sort Prop.
  
End Sensitization.

(** * Functions for Time. *)

Section TimeFunctions.
  
  (** Builds a new list of couples (Trans, DynamicTimeInterval) based 
      on the state of dynamic intervals in the [d_intervals] list, and
      of current state s of sitpn. *)
  
  Fixpoint update_time_intervals
           (sitpn : Sitpn)
           (s : SitpnState)
           (d_intervals : list (Trans * DynamicTimeInterval))
           (new_d_itvals : list (Trans * DynamicTimeInterval))
           {struct d_intervals} :
    option (list (Trans * DynamicTimeInterval)) :=
  match d_intervals with
  | (t, dyn_itval) :: tl =>
    (* Checks if t is associated with a static time interval in sitpn. *)
    match s_intervals sitpn t with
    (* Normal case, t is associated with a static itval. *)
    | Some stc_itval => 
      (* Checks if t is sensitized by the marking at state s. *)
      match is_sensitized sitpn s.(marking) t with
      (* If t is sensitized, determines its time interval status. *)
      | Some true =>
        (* If t is in the fired list of state s then resets t's itval
           and goes on. *)
        if in_list eq_nat_dec s.(fired) t then
          let reset_itval := dec_itval stc_itval in
          update_time_intervals sitpn s tl (new_d_itvals ++ [(t, active reset_itval)])
        (* Else looks at the reset orders given to t at state s. *)
        else
          match get_value eq_nat_dec t s.(reset) with
          (* If t received a reset order at state s, then resets t's
             itval and goes on. *)
          | Some true =>
            let reset_itval := dec_itval stc_itval in
            update_time_intervals sitpn s tl (new_d_itvals ++ [(t, active reset_itval)])
          (* If t is not in the fired list and didn't receive a reset
             order at state s, then looks at the state of its dynamic
             interval. *)
          | Some false =>
            match dyn_itval with
            (* If the interval is active, then decrements the interval. *)
            | active itval =>
              let new_itval := dec_itval itval in
              update_time_intervals sitpn s tl (new_d_itvals ++ [(t, active new_itval)])
            (* If dyn_itval is blocked, then it stays blocked. *)
            | blocked =>
              update_time_intervals sitpn s tl (new_d_itvals ++ [(t, blocked)])
            end
          (* Error: t is not in the reset list of state s. *)
          | None => None
          end
      (* If t is not sensitized by the current marking 
         then resets t's itval and goes on. *)
      | Some false =>
        let reset_itval := dec_itval stc_itval in
        update_time_intervals sitpn s tl (new_d_itvals ++ [(t, active reset_itval)])
      (* Error: is_sensitized raised an error. *)
      | None => None
      end
    (* Error: t is associated with a dynamic itval in d_intervals, 
              but with no static itval in sitpn. *)
    | None => None
    end
  | [] => Some new_d_itvals
  end.
  
End TimeFunctions.
