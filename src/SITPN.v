Require Export Hilecop.STPN.

(*==========================================================================================*)
(*=== TYPES FOR GENERALIZED, EXTENDED, SYNCHRONOUS, TEMPORAL AND INTERPRETED PETRI NETS. ===*)
(*==========================================================================================*)

(********************************************************)
(* CONDITIONS ON TRANSITIONS FOR INTERPRETED PETRI NETS *)
(********************************************************)

(*
 * Defines the SITPN structure. 
 *
 * Basically, same structure as STPN with condition values associated to transitions.
 * (At most one condition value by transition, or None)
 *
 * Conditions evolving through time are represented by 
 * a scenario. 
 *
 * A scenario is a list of functions associating 
 * condition value (bool) to transition (or None if no condition
 * exists for a given transition), for each evolution step of the Petri net. 
 *  
 *)
Structure SITPN : Set := mk_SITPN { 
                             scenario : list (trans_type -> option bool);
                             stpn :> STPN
                           }.

(*===================================================*)
(*=============== CONDITION SECTION  ================*)
(*===================================================*)
Section Condition.

  (* 
   * Function : Return true if no condition is associated
   *            to t, or returns the current value of the condition
   *            if it exists.
   *)
  Definition check_condition
             (conditions : trans_type -> option bool)
             (t : trans_type) : bool :=
    match (conditions t) with
    | None => true
    | Some b => b
    end.

  (*** Formal specification : check_condition ***)
  Inductive CheckCondition
            (conditions : trans_type -> option bool)
            (t : trans_type) : Prop :=
  | CheckCondition_none : 
      (conditions t) = None -> CheckCondition conditions t
  | CheckCondition_true : 
      (conditions t) = Some true -> CheckCondition conditions t.

  Functional Scheme check_condition_ind :=
    Induction for check_condition Sort Prop.

  (*** Correctness proof : check_condition ***)
  Theorem check_condition_correct :
    forall (conditions : trans_type -> option bool)
           (t : trans_type),
      check_condition conditions t = true -> CheckCondition conditions t.
  Proof.
    intros conditions t.
    functional induction (check_condition conditions t) using check_condition_ind; intros.
    - apply CheckCondition_true; rewrite e; rewrite H; reflexivity.
    - apply CheckCondition_none; assumption.
  Qed.

  (*** Completeness proof : check_condition ***)
  Theorem check_condition_complete :
    forall (conditions : trans_type -> option bool)
           (t : trans_type),
      CheckCondition conditions t -> check_condition conditions t = true.    
  Proof.
    intros conditions t H; elim H; intros;
      unfold check_condition; rewrite H0; reflexivity.
  Qed.

End Condition.
