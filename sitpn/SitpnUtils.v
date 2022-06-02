(** * Operations and predicates on SITPNs *)

Require Import common.CoqLib.
Require Import common.GlobalTypes.
Require Import common.ListDep.
Require Import common.ListPlus.

Require Import sitpn.Sitpn.
Require Import sitpn.SitpnTypes.
Require Import sitpn.SitpnFacts.

(** ** Operations and predicates on places *)

Section PlaceUtils.

  Variable sitpn : Sitpn.

  (** States that the [tinputs_of_p] list implements the set of input
      transitions of [p]. *)
  
  Definition TInputsOf (p : P sitpn) (tinputs_of_p : list (T sitpn)) :=
    @Set_in_ListA (T sitpn) Teq (fun t => post t p <> None) tinputs_of_p.

  (** States that the [toutputs_of_p] list implements the set of
      output transitions of [p]. *)
  
  Definition TOutputsOf (p : P sitpn) (toutputs_of_p : list (T sitpn)) :=
    @Set_in_ListA (T sitpn) Teq (fun t => pre p t <> None) toutputs_of_p.

  (** Returns the list implementing the set of input transitions of
      [p]. *)
  
  Definition inputs_of_p (p : P sitpn) : list (T sitpn) :=
    let is_input_of_p := (fun t => if post t p then true else false) in
    tfilter is_input_of_p (transitions sitpn) nat_to_T.

  (** Returns the list implementing the set of output transitions of
      [p]. *)
  
  Definition outputs_of_p (p : P sitpn) : list (T sitpn) :=
    let is_output_of_p := (fun t => if pre p t then true else false) in
    tfilter is_output_of_p (transitions sitpn) nat_to_T.

  (** Returns the list implementing the set of conflicting output
      transitions of [p]. *)
  
  Definition coutputs_of_p (p : P sitpn) : list (T sitpn) :=
    let is_coutput_of_p := (fun t => match pre p t with Some (basic, _) => true | _ => false end) in
    tfilter is_coutput_of_p (transitions sitpn) nat_to_T.

  (** Returns the list implementing the set of "structurally"
      non-conflicting (i.e. output transitions connected through a
      inhibitor or test arc) output transitions of [p]. *)
  
  Definition ncoutputs_of_p (p : P sitpn) : list (T sitpn) :=
    let is_ncoutput_of_p :=
      (fun t => match pre p t with Some ((inhibitor | test), _) => true | _ => false end) in
    tfilter is_ncoutput_of_p (transitions sitpn) nat_to_T.

  (** Returns the list implementing the set of actions associated
        with [p]. *)
  
  Definition acts_of_p (p : P sitpn) : list (A sitpn) :=
    tfilter (fun a => has_A p a) (actions sitpn) nat_to_A.
  
End PlaceUtils.

Arguments TInputsOf {sitpn}.
Arguments TOutputsOf {sitpn}.
Arguments inputs_of_p {sitpn}.
Arguments outputs_of_p {sitpn}.
Arguments coutputs_of_p {sitpn}.
Arguments ncoutputs_of_p {sitpn}.
Arguments acts_of_p {sitpn}.

(** ** Operations and predicates on transitions *)

Section TransitionUtils.

  Variable sitpn : Sitpn.

  (** States that the [tinputs_of_t] list implements the set of input
      places of [t]. *)
  
  Definition PInputsOf (t : T sitpn) (tinputs_of_t : list (P sitpn)) :=
    @Set_in_ListA (P sitpn) Peq (fun p => pre p t <> None) tinputs_of_t.

  (** States that the [poutputs_of_t] list implements the set of
      output places of [t]. *)
  
  Definition POutputsOf (t : T sitpn) (poutputs_of_t : list (P sitpn)) :=
    @Set_in_ListA (P sitpn) Peq (fun p => post t p <> None) poutputs_of_t.

  (** Returns the list implementing the set of input places of [t]. *)
  
  Definition inputs_of_t (t : T sitpn) : list (P sitpn) :=
    let is_input_of_t := (fun p => if (pre p t) then true else false) in
    tfilter is_input_of_t (places sitpn) nat_to_P.

  (** Returns the list implementing the set of output places of
      [t]. *)

  Definition outputs_of_t (t : T sitpn) : list (P sitpn) :=
    let is_output_of_t := (fun p => if (post t p) then true else false) in
    tfilter is_output_of_t (places sitpn) nat_to_P.

  (** Returns the list implementing the set of conditions associated
      with [t]. *)

  Definition conds_of_t (t : T sitpn) : list (C sitpn) :=
    let is_cond_of_t := (fun c => match has_C t c with mone | one => true | _ => false end) in
    tfilter is_cond_of_t (conditions sitpn) nat_to_C.

  (** Returns the transition type of t. *)

  Definition get_trans_type (t : T sitpn) : TransitionT :=
    match Is t with
    | Some (MkTItval a (ninat b) _)  =>
        if a =? b then temporal_a_a else temporal_a_b
    | Some (MkTItval a i+ _) => temporal_a_inf
    | None => not_temporal
    end.

  (** Returns maximal time counter value associated to t, depending
        the time counter associated to t.  *)

  Definition get_max_time_counter (t : T sitpn) : nat :=
    match Is t with
    (* Maximal time counter is equal to the upper bound value. *)
    | Some (MkTItval a (ninat b) _)  => b
    (* Or to the lower bound, if static time itval is of the form [a,∞] . *)
    | Some (MkTItval a i+ _)  => a
    (* Or to 1 if no itval is associated to t. *)
    | None => 1
    end.
  
End TransitionUtils.

Arguments PInputsOf {sitpn}.
Arguments POutputsOf {sitpn}.
Arguments inputs_of_t {sitpn}.
Arguments outputs_of_t {sitpn}.
Arguments conds_of_t {sitpn}.
Arguments get_trans_type {sitpn}.
Arguments get_max_time_counter {sitpn}.
