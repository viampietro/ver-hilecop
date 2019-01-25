Require Export Hilecop.STPN Hilecop.STPNAnimator Hilecop.Utils.STPNTactics Hilecop.Test.spn_examples.

(*! ================================================= !*)  
(*!                FIRST STPN EXAMPLE                 !*)
(*! ================================================= !*)

Lemma pos1 : 1 > 0. omega. Qed.
Lemma pos2 : 2 > 0. omega. Qed.
Lemma pos3 : 3 > 0. omega. Qed.
Lemma pos4 : 4 > 0. omega. Qed.
Lemma le24 : 2 <= 4. omega. Qed.
Lemma le12 : 1 <= 2. omega. Qed. 
Lemma le23 : 2 <= 3. omega. Qed.

(* Defines some chronos for stpn1. *)

Definition chr1 := {| cnt := 0;
                      min_t := {| int := 1; posi := pos1 |};
                      max_t := pos_val {| int := 2; posi := pos2 |};
                   |}.

Definition chr2 := {| cnt := 0;
                      min_t := {| int := 2; posi := pos2 |};
                      max_t := pos_val {| int := 3; posi := pos3 |};
                   |}.

Definition chr3 := {| cnt := 0;
                      min_t := {| int := 2; posi := pos2 |};
                      max_t := pos_inf;
                   |}.

(* List of (trans_type, option chrono_type). *)

Definition ex_chronos := [(0, None);
                            (1, Some chr1);
                            (2, Some chr2);
                            (3, Some chr3);
                            (4, None);
                            (5, None);
                            (6, None);
                            (8, None);
                            (9, None);
                            (12, None);
                            (13, None);
                            (14, None);
                            (16, None)
                         ].

(* Defines a STPN instance. *)

Definition stpn1 := mk_STPN ex_chronos spn1.

(*! ================================== !*)
(*! PROVING ISWELLSTRUCTUREDSTPN STPN1 !*)
(*! ================================== !*)

Lemma are_well_formed_chronos_stpn1 :
  AreWellFormedChronos stpn1.
Proof.
  decide_are_well_formed_chronos.
Qed.

Lemma no_unknown_transs_in_chronos_stpn1 :
  NoUnknownTransInChronos stpn1.
Proof.
  unfold NoUnknownTransInChronos; auto.
Qed.

Lemma is_well_structured_stpn1 :
  IsWellStructuredStpn stpn1.
Proof.
  unfold IsWellStructuredStpn.
  assert (H := (conj are_well_formed_chronos_stpn1
                     (conj no_unknown_transs_in_chronos_stpn1
                           is_well_structured_spn1))).
  auto.
Qed.

(*! ========================== !*)
(*! === PERFORMANCE TESTS. === !*)
(*! ========================== !*)

(** Some functions to display the evolution of the [STPN] being animated.  *)

Fixpoint stpn_display_evolution_aux (stpn_evolution : list (list trans_type * STPN)) {struct stpn_evolution} :
  list (list trans_type * marking_type * list (trans_type * option chrono_type)) :=
  match stpn_evolution with
  | (fired, stpn) :: tail => [(fired, (marking stpn), (chronos stpn))] ++ stpn_display_evolution_aux tail
  | [] => []
  end.

Definition stpn_display_evolution
           (opt_stpn_evolution : option (list (list trans_type * STPN))) :
  list (list trans_type * marking_type * list (trans_type * option chrono_type)) :=
  match opt_stpn_evolution with
  | Some evolution_list => stpn_display_evolution_aux evolution_list
  | None => []
  end.    

(* FORMER stpn_animate : 9 steps takes 19.843 secs! *)
(* ACTUAL stpn_animate : 9 steps takes 0.53 secs! *)

(* Time Eval compute in stpn_display_evolution (stpn_animate stpn1 9). *)
(* Time Eval compute in stpn_display_evolution (stpn_animate stpn1 50). *)
(* Time Eval compute in stpn_display_evolution (stpn_animate stpn1 100). *)
(* Time Eval compute in stpn_display_evolution (stpn_animate stpn1 500). *)
(* Time Eval compute in stpn_display_evolution (stpn_animate stpn1 1000). *)

