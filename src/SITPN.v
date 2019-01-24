Require Export Hilecop.STPN.

(*** ============================================= ***)
(*** TYPES FOR GENERALIZED, EXTENDED, SYNCHRONOUS, ***)
(*** TEMPORAL AND INTERPRETED PETRI NETS (SITPN).  ***)
(*** ============================================= ***)

(** * Interpreted Petri nets : associating conditions to transitions. *)

(** Defines the type for condition. 
    Condition values (boolean values) are evolving through time. 
    [nat] represents the discrete time value. *)

Definition condition_type := nat -> bool.

(** Defines the SITPN structure. 
 
    Basically, same structure as STPN with condition values associated to transitions.
    (At most one condition value by transition, or None)
 
    The [lconditions] field represents the association between transitions and conditions. *)

Structure SITPN : Set := mk_SITPN { 
                             lconditions : list (trans_type * option condition_type);
                             stpn :> STPN
                           }.

(** ** Properties on SITPN *)

(** All transitions in [sitpn.(transs)] are referenced in [sitpn.(lconditions)]. *)

Definition NoUnknownTransInLconditions (sitpn : SITPN) : Prop :=
  sitpn.(transs) = fst (split sitpn.(lconditions)).

(** A [SITPN] is well-structured if its inner [STPN] is well-structured 
    and no transitions are unknown in the field [lconditions]. *)

Definition IsWellStructuredSitpn (sitpn : SITPN) : Prop :=
  NoUnknownTransInLconditions sitpn /\ IsWellStructuredStpn sitpn.

(** *** Helper properties fir SITPN *)

Definition PriorityGroupsAreRefInLconditions 
           (priority_groups : list (list trans_type))
           (lconditions : list (trans_type * option condition_type)) :=
  (forall pgroup : list trans_type,
      In pgroup priority_groups ->
      (forall t : trans_type, In t pgroup -> In t (fst (split lconditions)))).

(** ** Conditions on transitions for interpreted Petri nets. *)

(*===================================================*)
(*=============== CONDITION SECTION  ================*)
(*===================================================*)

Section Condition.

  (** Returns an [option] to a [condition_type] associated to transition t
      in the list [lconditions]. 
      Returns None if [t] doesn't belong to the list [lconditions]. *)
  
  Fixpoint get_condition
           (lconditions : list (trans_type * option condition_type))
           (t : trans_type) {struct lconditions} : option (option condition_type) :=
    match lconditions with
    | (tr, opt_cond) :: tail => if t =? tr then
                              Some opt_cond
                            else get_condition tail t
    (* Exception : t is not in lconditions. *)
    | [] => None
    end.

  Functional Scheme get_condition_ind := Induction for get_condition Sort Prop.

  (** Formal specification for get_condition *)

  Inductive GetCondition :
    list (trans_type * option condition_type) -> nat -> option (option condition_type) -> Prop :=
  | GetCondition_err :
      forall (t : trans_type), GetCondition [] t None
  | GetCondition_if :
      forall (lconditions : list (trans_type * option condition_type))
        (opt_cond : option condition_type)
        (t tr : trans_type),
        t = tr -> GetCondition ((tr, opt_cond) :: lconditions) t (Some opt_cond)
  | GetCondition_else :
      forall (lconditions : list (trans_type * option condition_type))
             (t tr : trans_type)
             (opt_cond : option condition_type)
             (opt_opt_cond : option (option condition_type)),
        t <> tr ->
        GetCondition lconditions t opt_opt_cond ->
        GetCondition ((tr, opt_cond) :: lconditions) t opt_opt_cond.
                     
  (** Correctness proof : get_condition *)
  
  Theorem get_condition_correct :
    forall (lconditions : list (trans_type * option condition_type))
           (t : trans_type)
           (opt_opt_cond : option (option condition_type)),
      get_condition lconditions t = opt_opt_cond ->
      GetCondition lconditions t opt_opt_cond.
  Proof.
    intros lconditions t; functional induction (get_condition lconditions t)
                                     using get_condition_ind; intros.
    (* Case lconditions = []. *)
    - rewrite <- H; apply GetCondition_err.
    (* Case if is true. *)
    - rewrite <- H.
      apply GetCondition_if;
        rewrite Nat.eqb_sym in e1; apply beq_nat_true in e1; auto.
    (* Case else *)
    - apply GetCondition_else.
      + rewrite Nat.eqb_sym in e1; apply beq_nat_false in e1; auto.
      + rewrite <- H; apply IHo; reflexivity.
  Qed.

  (** Completeness proof : get_condition *)
  
  Theorem get_condition_compl :
    forall (lconditions : list (trans_type * option condition_type))
           (t : trans_type)
           (opt_opt_cond : option (option condition_type)),
      GetCondition lconditions t opt_opt_cond ->
      get_condition lconditions t = opt_opt_cond.
  Proof.
    intros; induction H.
    (* Case GetCondition_0 *)
    - simpl; auto.
    (* Case GetCondition_if *)
    - rewrite H; simpl.
      rewrite Nat.eqb_refl.
      reflexivity.
    (* Case GetCondition_else *)
    - simpl.
      apply Nat.eqb_neq in H.
      rewrite H.
      assumption.
  Qed.
  
  (** For all list [lconditions] and transition [t], (get_condition lconditions t) 
      returns no error if [t] is referenced in [lconditions]. *)
  
  Lemma get_condition_no_error :
    forall (lconditions : list (trans_type * option condition_type))
           (t : trans_type),
      In t (fst (split lconditions)) ->
      exists v : option (condition_type), get_condition lconditions t = Some v.
  Proof.
    intros lconditions t;
      functional induction (get_condition lconditions t) using get_condition_ind;
      intros;
      decide_accessor_no_err.
  Qed.
  
  (** Returns true if [opt_cond] is None, otherwise returns the 
      condition value at time [time_value]. *)
  
  Definition check_condition
             (opt_cond : option condition_type)
             (time_value : nat) : bool :=
    match opt_cond with
    | None => true
    | Some cond => (cond time_value)
    end.

  (** Formal specification : check_condition *)

  Inductive CheckCondition
            (opt_cond : option condition_type)
            (time_value : nat) : Prop :=
  | CheckCondition_none : 
      opt_cond = None -> CheckCondition opt_cond time_value
  | CheckCondition_true : 
      forall (cond : condition_type),
        opt_cond = Some cond ->
        (cond time_value) = true ->
        CheckCondition opt_cond time_value.

  Functional Scheme check_condition_ind :=
    Induction for check_condition Sort Prop.

  (** Correctness proof : check_condition *)
  
  Theorem check_condition_correct :
    forall (opt_cond : option (condition_type))
           (time_value : nat),
      check_condition opt_cond time_value = true -> CheckCondition opt_cond time_value.
  Proof.
    intros opt_cond time_value.
    functional induction (check_condition opt_cond time_value) using check_condition_ind; intros.
    - apply CheckCondition_true with (cond := cond); [reflexivity | assumption]. 
    - apply CheckCondition_none; reflexivity.
  Qed.

  (** Completeness proof : check_condition *)
  
  Theorem check_condition_complete :
    forall (opt_cond : option (condition_type))
           (time_value : nat),
      CheckCondition opt_cond time_value -> check_condition opt_cond time_value = true.
  Proof.
    intros opt_cond time_value H; elim H; intros;
      unfold check_condition.
    - rewrite H0; reflexivity.
    - rewrite H0; rewrite <- H1; reflexivity.
  Qed.

End Condition.
