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
  
End InterpretationFunctions.

(** * Sensitization functions. *)

Section Sensitization.
  
  (** Returns [Some true] if M(p) >= pre(p, t), [Some false] otherwise. 
                 
      Raises an error (i.e. None) if [get_m] fail. *)
  
  Definition check_pre
             (spn : Spn)
             (marking : list (Place * nat))
             (p : Place)
             (t : Trans) : option bool :=
    match get_m marking p with
    | Some nboftokens => Some ((pre spn t p) <=? nboftokens)
    | None => None
    end.

  Functional Scheme check_pre_ind := Induction for check_pre Sort Prop.

  (** Function : Returns [Some true] if ∀ p ∈ [pre_places], M(p) >= pre(p, t).
                 
                 Raises an error if [get_m] fails. *)
  
  Fixpoint map_check_pre_aux
           (spn : Spn)
           (marking : list (Place * nat))
           (pre_places : list Place)
           (t : Trans)
           (check_result : bool) {struct pre_places} : option bool :=
    match pre_places with
    | p :: tail =>
      match check_pre spn marking p t with
      | None => None
      | Some b =>
        map_check_pre_aux spn marking tail t (b && check_result)
      end 
    | [] => Some check_result
    end.  

  Functional Scheme map_check_pre_aux_ind := Induction for map_check_pre_aux Sort Prop.

  (** Wrapper around [map_check_pre_aux]. *)
  
  Definition map_check_pre
             (spn : Spn)
             (marking : list (Place * nat))
             (pre_places : list Place)
             (t : Trans) : option bool :=
    map_check_pre_aux spn marking pre_places t true.

  Functional Scheme map_check_pre_ind := Induction for map_check_pre Sort Prop.
  
  (** Returns [Some true] if M(p) >= test(p, t), [Some false] otherwise. 
                 
      Raises an error (i.e. None) if [get_m] fail. *)
  
  Definition check_test
             (spn : Spn)
             (marking : list (Place * nat))
             (p : Place)
             (t : Trans) : option bool :=
    match get_m marking p with
    | Some nboftokens => Some ((test spn t p) <=? nboftokens)
    | None => None
    end.

  Functional Scheme check_test_ind := Induction for check_test Sort Prop.
  
  (** Function : Returns [Some true] if ∀ p ∈ [test_places], M(p) >= test(p, t).
                 
                 Raises an error if [get_m] fails. *)
  
  Fixpoint map_check_test_aux
           (spn : Spn)
           (marking : list (Place * nat))
           (test_places : list Place)
           (t : Trans)
           (check_result : bool) {struct test_places} : option bool :=
    match test_places with
    | p :: tail =>
      match check_test spn marking p t with
      | None => None
      | Some b =>
        map_check_test_aux spn marking tail t (b && check_result)
      end 
    | [] => Some check_result
    end.  

  Functional Scheme map_check_test_aux_ind := Induction for map_check_test_aux Sort Prop.

  (** Wrapper around [map_check_test_aux]. *)
  
  Definition map_check_test
             (spn : Spn)
             (marking : list (Place * nat))
             (test_places : list Place)
             (t : Trans) : option bool :=
    map_check_test_aux spn marking test_places t true.

  Functional Scheme map_check_test_ind := Induction for map_check_test Sort Prop.
  
  (** Returns [Some true] if M(p) >= inhib(p, t), [Some false] otherwise. 
                 
      Raises an error (i.e. None) if [get_m] fail. *)
  
  Definition check_inhib
             (spn : Spn)
             (marking : list (Place * nat))
             (p : Place)
             (t : Trans) : option bool :=
    match get_m marking p with
    | Some nboftokens => Some ((nboftokens <? (inhib spn t p)) || ((inhib spn t p) =? 0))
    | None => None
    end.

  Functional Scheme check_inhib_ind := Induction for check_inhib Sort Prop.
  
  (** Function : Returns [Some true] if ∀ p ∈ [inhib_places], M(p) >= inhib(p, t).
                 
                 Raises an error if [get_m] fails. *)
  
  Fixpoint map_check_inhib_aux
           (spn : Spn)
           (marking : list (Place * nat))
           (inhib_places : list Place)
           (t : Trans)
           (check_result : bool) {struct inhib_places} : option bool :=
    match inhib_places with
    | p :: tail =>
      match check_inhib spn marking p t with
      | None => None
      | Some b =>
        map_check_inhib_aux spn marking tail t (b && check_result)
      end 
    | [] => Some check_result
    end.  

  Functional Scheme map_check_inhib_aux_ind := Induction for map_check_inhib_aux Sort Prop.
  
  (** Wrapper around [map_check_inhib_aux]. *)
  
  Definition map_check_inhib
             (spn : Spn)
             (marking : list (Place * nat))
             (inhib_places : list Place)
             (t : Trans) : option bool :=
    map_check_inhib_aux spn marking inhib_places t true.

  Functional Scheme map_check_inhib_ind := Induction for map_check_inhib Sort Prop.

  (** Returns [Some true] if [t] is sensitized in marking [marking], 
      [Some false] otherwise. 
                 
      Raises an error if [map_check_pre], [map_check_test], [map_check_inhib] or
      [get_neighbours] fail. *)
  
  Definition is_sensitized
             (spn : Spn)
             (marking : list (Place * nat))
             (neighbours_of_t : Neighbours)
             (t : Trans) : option bool :=    
    match map_check_pre spn marking (pre_pl neighbours_of_t) t with
    | Some check_pre_result =>  
      match map_check_test spn marking (test_pl neighbours_of_t) t with
      | Some check_test_result =>
        match map_check_inhib spn marking (inhib_pl neighbours_of_t) t with
        | Some check_inhib_result =>
          Some (check_pre_result && check_test_result && check_inhib_result)
        (* Case of error!! *)
        | None => None
        end
      (* Case of error!! *)
      | None => None
      end
    (* Case of error!! *)
    | None => None
    end.

  Functional Scheme is_sensitized_ind := Induction for is_sensitized Sort Prop.
  
End Sensitization.

