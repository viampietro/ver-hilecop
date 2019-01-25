Require Import Hilecop.SITPN Hilecop.SITPNAnimator Hilecop.Test.stpn_examples Coq.Arith.Even.

(*! ================================================== !*)  
(*!                  FIRST SITPN EXAMPLE               !*)
(*! ================================================== !*)  

Definition cond1 (time_value : nat) : bool := Nat.even time_value.
Definition cond2 (time_value : nat) : bool := Nat.odd time_value.
Definition cond3 (time_value : nat) : bool := (time_value mod 4) =? 0.

(* Defines conditions on transitions for sitpn1 *)

Definition ex_lconditions :=
  [ (0, Some cond1); (1, Some cond1); (2, Some cond2); (3, Some cond3);
      (4, None); (5, Some cond2); (6, Some cond3); (8, None); (9, None);
        (12, None); (13, None); (14, Some cond1); (16, Some cond2)
  ].

(* Defines a SITPN instance. *)

Definition sitpn1 := mk_SITPN ex_lconditions stpn1.

(*! ==================================== !*)
(*! PROVING ISWELLSTRUCTUREDSITPN SITPN1 !*)
(*! ==================================== !*)

Lemma no_unknown_trans_in_lconditions_sitpn1 :
  NoUnknownTransInLconditions sitpn1.
Proof.
  unfold NoUnknownTransInLconditions; auto.
Qed.

Lemma is_well_structured_sitpn1 :
  IsWellStructuredSitpn sitpn1.
Proof.
  unfold IsWellStructuredSitpn.
  assert (H := (conj no_unknown_trans_in_lconditions_sitpn1
                     is_well_structured_stpn1)).
  auto.
Qed.

(*! ========================== !*)
(*! === PERFORMANCE TESTS. === !*)
(*! ========================== !*)

(** Some functions to display the evolution of the [SITPN] being animated.  *)

Fixpoint sitpn_display_evolution_aux (sitpn_evolution : list (list trans_type * SITPN)) {struct sitpn_evolution} :
  list (list trans_type * marking_type * list (trans_type * option chrono_type)) :=
  match sitpn_evolution with
  | (fired, sitpn) :: tail => [(fired, (marking sitpn), (chronos sitpn))] ++ sitpn_display_evolution_aux tail
  | [] => []
  end.

Definition sitpn_display_evolution
           (opt_sitpn_evolution : option (list (list trans_type * SITPN))) :
  list (list trans_type * marking_type * list (trans_type * option chrono_type)) :=
  match opt_sitpn_evolution with
  | Some evolution_list => sitpn_display_evolution_aux evolution_list
  | None => []
  end.

Definition test_sitpn_animate := sitpn_animate sitpn1 1000.

(* Time Compute sitpn_display_evolution (sitpn_animate sitpn1 9). *)
(* Time Compute sitpn_display_evolution (sitpn_animate sitpn1 50). *)
(* Time Compute sitpn_display_evolution (sitpn_animate sitpn1 100). *)
(* Time Compute sitpn_display_evolution (sitpn_animate sitpn1 500). *)
(* Time Compute sitpn_display_evolution (sitpn_animate sitpn1 1000). *)
(* Time Compute sitpn_display_evolution (sitpn_animate sitpn1 2000). *)
(* Time Compute sitpn_display_evolution (sitpn_animate sitpn1 400). *)