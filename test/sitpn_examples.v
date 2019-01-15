Require Import SITPN stpn_examples.

(*======================================================*)  
(*                  FIRST SITPN EXAMPLE                 *)
(*======================================================*)

(*  Defines conditions functions, and scenario for first SITPN example. *)
Definition ex_conds_cycle1 (t : trans_type) : option bool :=
  match t with
  | 0  => Some true
  | 2  => Some false
  | _ => None
  end.

Definition ex_conds_cycle2 (t : trans_type) : option bool :=
  match t with
  | 0  => Some true
  | 2  => Some true
  | _ => None
  end.

Definition ex_conds_cycle3 (t : trans_type) : option bool :=
  match t with
  | 0  => Some true
  | 2  => Some true
  | 3  => Some false
  | _ => None
  end.

Definition ex_conds_cycle4 (t : trans_type) : option bool :=
  match t with
  | 0  => Some true
  | 2  => Some true
  | 3  => Some false
  | _ => None
  end.

Definition ex_conds_cycle5 (t : trans_type) : option bool :=
  match t with
  | 0  => Some true
  | 2  => Some true
  | 3  => Some false
  | _ => None
  end.

(* A scenario is a list of functions associating, option bool to transitions. *)
(* Here, ex_scenario defines conditions value for 20 cycles. *)
Definition ex_scenario := [ ex_conds_cycle1;
                              ex_conds_cycle2;
                              ex_conds_cycle3;
                              ex_conds_cycle4;
                              ex_conds_cycle5;
                              (fun t => None);
                              (fun t => None);
                              (fun t => None);
                              (fun t => None);
                              (fun t => None);
                              (fun t => None);
                              (fun t => None);
                              (fun t => None);
                              (fun t => None);
                              (fun t => None);
                              (fun t => None);
                              (fun t => None);
                              (fun t => None);
                              (fun t => None);
                              (fun t => None) ].

(* Defines a SITPN instance. *)
Definition sitpn1 := mk_SITPN ex_scenario stpn1.

(*=== ERRORS TESTS. ===*)

(* The following examples must return None, because the number of evolution
 * cycles passed as argument is greater than the size of the scenario list (length scenario = 20).
 *)
Example sitpn_animate_err1 : (sitpn_animate sitpn1 21 []) = None. compute; reflexivity. Qed.
Example sitpn_animate_err2 : (sitpn_animate sitpn1 200 []) = None. compute; reflexivity. Qed.
Example sitpn_animate_err3 : (sitpn_animate sitpn1 2000 []) = None. compute; reflexivity. Qed.

(*==== PERFORMANCE TESTS. ====*)
(* Not easy to do performance tests here, because when have to define 
 * a scenario of significant size to test sitpn_animate with big entries.
 *)

(* Normally, performance test results for sitpn_animate are equivalent
 * to the ones for stpn_animate, since we are only adding a O(1) test (condition test) to
 * the algorithm.
 *)
Time Eval compute in (sitpn_animate sitpn1 20 []).