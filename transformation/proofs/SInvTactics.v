(** * Tactics for state invariants *)

Require Import common.StateAndErrorMonad.
Require Import common.proofs.StateAndErrorMonadTactics.
Require Import common.proofs.ListMonadFacts.
Require Import common.proofs.ListMonadTactics.

Require Import transformation.Sitpn2HVhdlTypes.
Require Import transformation.GenerateInfos.
Require Import transformation.GenerateArchitecture.

Require Import String.
Require Import FunInd.

Ltac check_is_state_record S :=
  match S with
  | MkS2HState _ _ _ _ _ _ _ _ _ _ _ _ => idtac
  end.

Ltac destr_match_monad H G := 
  case_eq G; [
      let msg := fresh "msg" in
      let EQ := fresh "EQ" in
      intros msg EQ; rewrite EQ in H;
      discriminate
    |
      let x := fresh "x" in
      let S := fresh "s" in
      let EQ := fresh "EQ" in
      intros x S EQ; rewrite EQ in H; inversion H; clear H; subst
    ].

Ltac destr_bind1 F G X S1 S2 H :=
  let x := fresh "x" in
  let s := fresh "s" in
  let EQ1 := fresh "EQ" in
  let EQ2 := fresh "EQ" in
  destruct (Bind_inversion _ _ _ F G X S1 S2 H) as [x [s [EQ1 EQ2]]];
  transitivity s.

Ltac destr_bind2 F G X S1 S2 H A :=
  let x := fresh "x" in
  let s := fresh "s" in
  let EQ1 := fresh "EQ" in
  let EQ2 := fresh "EQ" in
  destruct (Bind_inversion _ _ _ F G X S1 S2 H) as [x [s [EQ1 EQ2]]];
  transitivity (A s).

Lemma inject_t_inv_state :
  forall {sitpn decpr t lofTs s v s'},
    inject_t sitpn decpr t lofTs s = OK v s' ->
    s = s'.
Proof.
  intros until s;
  functional induction (inject_t sitpn decpr t lofTs) using inject_t_ind;
    intros until s'; intros f; minv f; auto.
  eapply IHc; eauto. 
Qed.

(* Solves lemmas about the invariance of the state through the call to
   monadic functions, in the context of the state-and-error monad.
   The invariance properties take the form of equality properties.  *)

Ltac solve_sinv :=
  lazymatch goal with
  (* Solves the simplest forms of goals in the tactic *)
  | [ |- ?S1 = ?S1 ] => reflexivity
  | [ |- ?F ?S1 = ?F ?S1 ] => reflexivity
                                
  (* Substitutes [S1] by [S2] before solving the goal with
     reflexivity *)
  | [ H: OK _ ?S1 = OK _ ?S2 |- ?S1 = ?S2 ] =>
      inversion H; clear H; subst; reflexivity
  | [ H: OK _ ?S1 = OK _ ?S2 |- ?F ?S1 = ?F ?S2 ] =>
      inversion H; clear H; subst; reflexivity
                                     
  (* If [S3] is an instance of a [Sitpn2HVhdlState] record type,
     i.e. of the form (MkS2HState _), and the goal is of the form [F
     S1 = F S2], then tries to convert [F S1] with [F S3] *)
  | [ H: OK _ ?S3 = OK _ ?S2 |- ?F ?S1 = ?F ?S2 ] =>
      tryif (check_is_state_record S3) then
        tryif (change (F S1)  with (F S3)) then solve_sinv
        else (fail 0 F S1 "and" F S3 "are not convertible")
      else
        tryif (change S1 with S3) then solve_sinv
        else (fail 0 S1 "and" S3 "are not convertible")
               
  (* In the case of [Ret], [Put] or [Get], S1 = S2.  Then, [inversion
     H] followed by [subst] must lead to a tautology. *)
  | [ H: Ret _ ?S1 = OK _ ?S2 |- ?S1 = ?S2 ] =>
      inversion H; clear H; subst; solve_sinv
  | [ H: Ret _ ?S1 = OK _ ?S2 |- ?F ?S1 = ?F ?S2 ] =>
      inversion H; clear H; subst; solve_sinv
  | [ H: Get ?S1 = OK _ ?S2 |- ?S1 = ?S2 ] =>
      inversion H; clear H; subst; solve_sinv
  | [ H: Get ?S1 = OK _ ?S2 |- ?F ?S1 = ?F ?S2 ] =>
      inversion H; clear H; subst; solve_sinv
  | [ H: Put ?S1 _ = OK _ ?S2 |- ?S1 = ?S2 ] =>
      inversion H; clear H; subst; solve_sinv
  | [ H: Put ?S1 _ = OK _ ?S2 |- ?F ?S1 = ?F ?S2 ] =>
      inversion H; clear H; subst; solve_sinv
                                     
  (* If one hypothesis is of the form [Err = OK] or [Error = OK], then
     solves the goal with the [discriminate] tactic. *)
  | [ H: Err _ _ = OK _ _ |- _ ] => discriminate
  | [ H: Error _ = OK _ _ |- _ ] => discriminate
                                      
  (*  *)
  | [ H: Bind ?F ?G ?S1 = OK ?X ?S2 |- ?S1 = ?S2 ] =>
      let x := fresh "x" in
      let s := fresh "s" in
      let EQ1 := fresh "EQ" in
      let EQ2 := fresh "EQ" in
      destruct (Bind_inversion _ _ _ F G X S1 S2 H) as [x [s [EQ1 EQ2]]];
      transitivity s;
      [ clear EQ2; try solve_sinv | clear EQ1; try solve_sinv ]
  | [ H: Bind ?F ?G ?S1 = OK ?X ?S2 |- ?A ?S1 = ?A ?S2 ] =>
      let x := fresh "x" in
      let s := fresh "s" in
      let EQ1 := fresh "EQ" in
      let EQ2 := fresh "EQ" in
      destruct (Bind_inversion _ _ _ F G X S1 S2 H) as [x [s [EQ1 EQ2]]];
      transitivity (A s);
      [ clear EQ2; try solve_sinv | clear EQ1; try solve_sinv ]
                                                                        
  (* If [H] is of the form [(match G with | Error _ => _ OK _ _ => _
     end) = OK X S2] where [G] is a function identifier, then solve
     the case where [Error = OK] with [discriminate], and tries to
     solve the remaining case (i.e. where [G = OK]) with
     [solve_sinv]. *)
  | [ H: (match ?G with | Error _ => _ | OK _ _ => _ end = OK _ ?S2) |- ?F ?S1 = ?F ?S2 ]  =>
      destr_match_monad H G; try solve_sinv
  | [ H: (match ?G with | Error _ => _ | OK _ _ => _ end = OK _ ?S2) |- ?S1 = ?S2 ]  =>
      destr_match_monad H G; try solve_sinv
  | [ H: (match ?O with _ => _ end) ?S1 = OK ?X ?S2 |- ?F ?S1 = ?F ?S2 ] =>
      case O in H; try solve_sinv                                 
  | [ H: (match ?O with _ => _ end) ?S1 = OK ?X ?S2 |- ?S1 = ?S2 ] =>
      case O in H; try solve_sinv                                 
                      
  (* If [H] is of the form [(if C then _ else _) S1 = OK X S2], then
     calls [solve_sinv] in the two if branches. *)                        
  | [ H: (if ?C then _ else _) ?S1 = OK _ ?S2 |- ?F ?S1 = ?F ?S2 ] =>                                 
      case C in H; try solve_sinv
  | [ H: (if ?C then _ else _) ?S1 = OK _ ?S2 |- ?S1 = ?S2 ] =>                                 
      case C in H; try solve_sinv                      
  | [ H: (let _ := ?G in _) ?S1 = OK ?X ?S2 |- ?F ?S1 = ?F ?S2 ] =>
      destruct G; try solve_sinv
  | [ H: (let (_, _) := ?G in _) ?S1 = OK ?X ?S2 |- ?F ?S1 = ?F ?S2 ] =>
      destruct G; try solve_sinv
  | [ H: (let (_, _, _) := ?G in _) ?S1 = OK ?X ?S2 |- ?F ?S1 = ?F ?S2 ] =>
      destruct G; try solve_sinv
  | [ H: (let _ := ?G in _) _ ?S1 = OK ?X ?S2 |- ?F ?S1 = ?F ?S2 ] =>
      destruct G; try solve_sinv
  | [ H: (let (_, _) := ?G in _) _ ?S1 = OK ?X ?S2 |- ?F ?S1 = ?F ?S2 ] =>
      destruct G; try solve_sinv
  | [ H: (let (_, _, _) := ?G in _) _ ?S1 = OK ?X ?S2 |- ?F ?S1 = ?F ?S2 ] =>
      destruct G; try solve_sinv
  | [ H: (let _ := ?G in _) ?S1 = OK ?X ?S2 |- ?S1 = ?S2 ] =>
      destruct G; try solve_sinv
  | [ H: (let (_, _) := ?G in _) ?S1 = OK ?X ?S2 |- ?S1 = ?S2 ] =>
      destruct G; try solve_sinv
  | [ H: (let (_, _, _) := ?G in _) ?S1 = OK ?X ?S2 |- ?S1 = ?S2 ] =>
      destruct G; try solve_sinv
  | [ H: (let _ := ?G in _) _ ?S1 = OK ?X ?S2 |- ?S1 = ?S2 ] =>
      destruct G; try solve_sinv
  | [ H: (let (_, _) := ?G in _) _ ?S1 = OK ?X ?S2 |- ?S1 = ?S2 ] =>
      destruct G; try solve_sinv
  | [ H: (let (_, _, _) := ?G in _) _ ?S1 = OK ?X ?S2 |- ?S1 = ?S2 ] =>
      destruct G; try solve_sinv                      
                      
  (* Deduces the equality between S1 and S2 (or F S1 and F S2) based
     for specific case of generic functions over lists (monadic
     version). *)

  (* CASE [tmap] and [map] functions *)
  | [ H: ListMonad.tmap _ _ _ ?S1 = OK _ ?S2 |- ?F ?S1 = ?F ?S2 ] =>
      pattern S1, S2; eapply (tmap_inv_state H); intros; eauto with typeclass_instances;
      try solve_sinv
  | [ H: ListMonad.tmap _ _ _ ?S1 = OK _ ?S2 |- ?S1 = ?S2 ] =>
      pattern S1, S2; eapply (tmap_inv_state H); intros; eauto with typeclass_instances;
      try solve_sinv
  | [ H: ListMonad.map _ _ ?S1 = OK _ ?S2 |- ?F ?S1 = ?F ?S2 ] =>
      pattern S1, S2; eapply (map_inv_state H); intros; eauto with typeclass_instances;
      try solve_sinv
  | [ H: ListMonad.map _ _ ?S1 = OK _ ?S2 |- ?S1 = ?S2 ] =>
      pattern S1, S2; eapply (map_inv_state H); intros; eauto with typeclass_instances;
      try solve_sinv
  (* CASE [fold_left] function *)
  | [ H: ListMonad.fold_left _ _ _ ?S1 = OK _ ?S2 |- ?F ?S1 = ?F ?S2 ] =>
      pattern S1, S2; eapply (foldl_inv_state H); intros; eauto with typeclass_instances;
      try solve_sinv
  | [ H: ListMonad.fold_left _ _ _ ?S1 = OK _ ?S2 |- ?S1 = ?S2 ] =>
      pattern S1, S2; eapply (foldl_inv_state H); intros; eauto with typeclass_instances;
      try solve_sinv
  (* CASE [iter] function *)
  | [ H: ListMonad.iter _ _ ?S1 = OK _ ?S2 |- ?F ?S1 = ?F ?S2 ] =>
      pattern S1, S2; eapply (iter_inv_state H); intros; eauto with typeclass_instances;
      try solve_sinv
  | [ H: ListMonad.iter _ _ ?S1 = OK _ ?S2 |- ?S1 = ?S2 ] =>
      pattern S1, S2; eapply (iter_inv_state H); intros; eauto with typeclass_instances;
      try solve_sinv
  (* CASE [find] function *)
  | [ H: ListMonad.find _ _ ?S1 = OK _ ?S2 |- ?F ?S1 = ?F ?S2 ] =>
      pattern S1, S2; eapply (find_inv_state H); intros; eauto with typeclass_instances;
      try solve_sinv
  | [ H: ListMonad.find _ _ ?S1 = OK _ ?S2 |- ?S1 = ?S2 ] =>
      pattern S1, S2; eapply (find_inv_state H); intros; eauto with typeclass_instances;
      try solve_sinv
  (* CASE [getv] function *)
  | [ H: ListMonad.getv _ _ _ ?S1 = OK _ ?S2 |- ?F ?S1 = ?F ?S2 ] =>
      rewrite (getv_inv_state H); clear H; reflexivity
  | [ H: ListMonad.getv _ _ _ ?S1 = OK _ ?S2 |- ?S1 = ?S2 ] =>
      rewrite (getv_inv_state H); clear H; reflexivity
  (* CASE [inject_t] function (this function is not a generic list
     function but a specific case found in the HILECOP
     transformation). It is added here as a convenient way to solve
     state invariance goals. *)
  | [ H: inject_t _ _ _ _ ?S1 = OK _ ?S2 |- ?F ?S1 = ?F ?S2 ] =>
      pattern S1, S2; erewrite (inject_t_inv_state H); eauto
  | [ H: inject_t _ _ _ _ ?S1 = OK _ ?S2 |- ?S1 = ?S2 ] =>
      pattern S1, S2; erewrite (inject_t_inv_state H); eauto
  (* CASE [foreach] function *)
  | [ H: ListMonad.foreach _ _ ?S1 = OK _ ?S2 |- ?F ?S1 = ?F ?S2 ] =>
      pattern S1, S2; eapply (foreach_inv_state H); intros; eauto with typeclass_instances;
      try solve_sinv
  | [ H: ListMonad.foreach _ _ ?S1 = OK _ ?S2 |- ?S1 = ?S2 ] =>
      pattern S1, S2; eapply (foreach_inv_state H); intros; eauto with typeclass_instances;
      try solve_sinv                                                                       
  (* If [H] is of the form [G A1 ... A__n S1 = OK X S2] where [G] is a
     function identifier, then calls the [cbn] tactic on [H]. *)
  | [ H: ?G _ _ _ _ _ _ ?S1 = OK ?X ?S2 |- ?S1 = ?S2 ] =>
      ((progress cbn in H) || (unfold G in H)); try solve_sinv
  | [ H: ?G _ _ _ _ _ _ ?S1 = OK ?X ?S2 |- ?F ?S1 = ?F ?S2 ] =>
      ((progress cbn in H) || (unfold G in H)); try solve_sinv
  | [ H: ?G _ _ _ _ _ ?S1 = OK ?X ?S2 |- ?S1 = ?S2 ] =>
      ((progress cbn in H) || (unfold G in H)); try solve_sinv
  | [ H: ?G _ _ _ _ _ ?S1 = OK ?X ?S2 |- ?F ?S1 = ?F ?S2 ] =>
      ((progress cbn in H) || (unfold G in H)); try solve_sinv                                                                       
  | [ H: ?G _ _ _ _ ?S1 = OK ?X ?S2 |- ?S1 = ?S2 ] =>
      ((progress cbn in H) || (unfold G in H)); try solve_sinv
  | [ H: ?G _ _ _ _ ?S1 = OK ?X ?S2 |- ?F ?S1 = ?F ?S2 ] =>
      ((progress cbn in H) || (unfold G in H)); try solve_sinv                                                                       
  | [ H: ?G _ _ _ ?S1 = OK ?X ?S2 |- ?S1 = ?S2 ] =>
      ((progress cbn in H) || (unfold G in H)); try solve_sinv
  | [ H: ?G _ _ _ ?S1 = OK ?X ?S2 |- ?F ?S1 = ?F ?S2 ] =>
      ((progress cbn in H) || (unfold G in H)); try solve_sinv
  | [ H: ?G _ _ ?S1 = OK ?X ?S2 |- ?S1 = ?S2 ] =>
      ((progress cbn in H) || (unfold G in H)); try solve_sinv
  | [ H: ?G _ _ ?S1 = OK ?X ?S2 |- ?F ?S1 = ?F ?S2 ] =>
      ((progress cbn in H) || (unfold G in H)); try solve_sinv
  | [ H: ?G _ ?S1 = OK ?X ?S2 |- ?S1 = ?S2 ] =>
      ((progress cbn in H) || (unfold G in H)); try solve_sinv
  | [ H: ?G _ ?S1 = OK ?X ?S2 |- ?F ?S1 = ?F ?S2 ] =>
      ((progress cbn in H) || (unfold G in H)); try solve_sinv
  | [ H: ?G ?S1 = OK ?X ?S2 |- ?S1 = ?S2 ] =>
      ((progress cbn in H) || (unfold G in H)); try solve_sinv
  | [ H: ?G ?S1 = OK ?X ?S2 |- ?F ?S1 = ?F ?S2 ] =>
      ((progress cbn in H) || (unfold G in H)); try solve_sinv
  end.

(* Applies [lem] on the goal, where [lem] 
   is intended to be of the form:
   - (map_inv_state H)
   - (tmap_inv_state H)
   - (foldl_inv_state H)
 *)

Ltac eapp_inv_state1 lem :=
  eapply lem; [
      eauto with typeclass_instances |
      eauto with typeclass_instances |
      let b := fresh "b" in
      let a := fresh "a" in
      let x := fresh "x" in
      let S := fresh "s" in
      let S' := fresh "s'" in
      let EQ := fresh "EQ" in
      intros b a S x S' EQ;
      pattern S, S'
    ].

(* Applies [lem] on the goal, where [lem] 
   is intended to be of the form:
   - (find_inv_state H)
   - (iter_inv_state H)
 *)

Ltac eapp_inv_state2 lem :=
  eapply lem; [
      eauto with typeclass_instances |
      eauto with typeclass_instances |
      let a := fresh "a" in
      let x := fresh "x" in
      let S := fresh "s" in
      let S' := fresh "s'" in
      let EQ := fresh "EQ" in
      intros a S x S' EQ;
      pattern S, S'
    ].

Ltac solve_sinv_pattern :=
  lazymatch goal with

  (* Solves the simplest forms of goals in the tactic *)
  | [ |- ?P ?S1 ?S1 ] => try (assumption || reflexivity); auto
    
  (* Substitutes [S1] by [S2] before solving the goal with [auto] *)
  | [ H: OK _ ?S1 = OK _ ?S2 |- ?P ?S1 ?S2 ] =>
      inversion H; clear H; subst; try (assumption || reflexivity); auto
                                     
  (* If [S3] is an instance of a [Sitpn2HVhdlState] record type,
     i.e. of the form (MkS2HState _), and the goal is of the form [P
     S1 S2], then tries to convert [P S1 S2] with [P S3 S2]. *)
  | [ H: OK _ ?S3 = OK _ ?S2 |- ?P ?S1 ?S2 ] => (* idtac "Cut case" *)
      tryif (check_is_state_record S3) then
        tryif (change (P S1 S2)  with (P S3 S2)) then solve_sinv_pattern
        else (fail 0 P S1 S2 "and" P S3 S2 "are not convertible")
      else
        tryif (change S1 with S3) then solve_sinv_pattern
        else (fail 0 S1 "and" S3 "are not convertible")
               
  (*  *)
  | [ H: Ret _ ?S1 = OK _ ?S2 |- ?P ?S1 ?S2 ] =>
      inversion H; clear H; subst; try (assumption || reflexivity); auto
  | [ H: Get ?S1 = OK _ ?S2 |- ?P ?S1 ?S2 ] =>
      inversion H; clear H; subst; try (assumption || reflexivity); auto
                                     
  (*  *)
  | [ H: Put ?S1 _ = OK _ ?S2 |- ?P ?S1 ?S2 ] =>
      inversion H; clear H; subst; try (assumption || reflexivity); auto
                                     
  (* If one hypothesis is of the form [Err = OK] or [Error = OK], then
     solves the goal with the [discriminate] tactic. *)
  | [ H: Err _ _ = OK _ _ |- _ ] => discriminate
  | [ H: Error _ = OK _ _ |- _ ] => discriminate
                                      
  (*  *)
  | [ H: Bind ?F ?G ?S1 = OK ?X ?S2 |- ?P ?S1 ?S2 ] =>
      let x := fresh "x" in
      let s := fresh "s" in
      let EQ1 := fresh "EQ" in
      let EQ2 := fresh "EQ" in
      destruct (Bind_inversion _ _ _ F G X S1 S2 H) as [x [s [EQ1 EQ2]]];
      cut (RelationClasses.Transitive P); [
          let trans := fresh "trans" in
          intros trans; apply (trans S1 s S2);
          [ clear EQ2; pattern S1, s; try solve_sinv_pattern
          | clear EQ1; pattern s, S2; try solve_sinv_pattern ]
        | try (eauto with typeclass_instances) ]

  (* If [H] is of the form [(if C then _ else _) S1 = OK X S2], then
     calls [solve_sinv_pattern] in the two if branches. *)                        
  | [ H: (if ?C then _ else _) ?S1 = OK _ ?S2 |- ?P ?S1 ?S2 ] =>                                 
      case C in H; pattern S1, S2; try solve_sinv_pattern
        
  (* If [H] is of the form [(match G with | Error _ => _ OK _ _ => _
     end) = OK X S2] where [G] is a function identifier, then solve
     the case where [Error = OK] with [discriminate], and tries to
     solve the remaining case (i.e. where [G = OK]) with [solve_sinv_pattern]. *)
  | [ H: (match ?G with | Error _ => _ | OK _ _ => _ end = OK _ ?S2) |- ?P ?S1 ?S2 ]  =>
      case_eq G; [
        let msg := fresh "msg" in
        let EQ := fresh "EQ" in
        intros msg EQ; rewrite EQ in H;
        discriminate
      |
        let x := fresh "x" in
        let S := fresh "s" in
        let EQ := fresh "EQ" in
        intros x S EQ; rewrite EQ in H; inversion H; clear H; subst
      ]; pattern S1, S2; try solve_sinv_pattern
  | [ H: (match ?O with _ => _ end) ?S1 = OK ?X ?S2 |- ?P ?S1 ?S2 ] =>
      case O in H; pattern S1, S2; try solve_sinv_pattern                                 
  | [ H: (let _ := ?G in _) ?S1 = OK ?X ?S2 |- ?P ?S1 ?S2 ] =>
      destruct G; pattern S1, S2; try solve_sinv_pattern
  | [ H: (let (_, _) := ?G in _) ?S1 = OK ?X ?S2 |- ?P ?S1 ?S2 ] =>
      destruct G; pattern S1, S2; try solve_sinv_pattern
  | [ H: (let (_, _, _) := ?G in _) ?S1 = OK ?X ?S2 |- ?P ?S1 ?S2 ] =>
      destruct G; pattern S1, S2; try solve_sinv_pattern
  | [ H: (let _ := ?G in _) _ ?S1 = OK ?X ?S2 |- ?P ?S1 ?S2 ] =>
      destruct G; pattern S1, S2; try solve_sinv_pattern
  | [ H: (let (_, _) := ?G in _) _ ?S1 = OK ?X ?S2 |- ?P ?S1 ?S2 ] =>
      destruct G; pattern S1, S2; try solve_sinv_pattern
  | [ H: (let (_, _, _) := ?G in _) _ ?S1 = OK ?X ?S2 |- ?P ?S1 ?S2 ] =>
      destruct G; pattern S1, S2; try solve_sinv_pattern
                      
  (* CASE [tmap] function *)
  | [ H: ListMonad.tmap _ _ _ ?S1 = OK _ ?S2 |- ?P ?S1 ?S2 ] =>
      eapp_inv_state1 (tmap_inv_state P H); try solve_sinv_pattern
  (* CASE [map] function *)
  | [ H: ListMonad.map _ _ ?S1 = OK _ ?S2 |- ?P ?S1 ?S2 ] =>
      eapp_inv_state1 (map_inv_state P H); try solve_sinv_pattern
  (* CASE [fold_left] function *)
  | [ H: ListMonad.fold_left _ _ _ ?S1 = OK _ ?S2 |- ?P ?S1 ?S2 ] =>
      eapp_inv_state1 (foldl_inv_state P H); try solve_sinv_pattern
  (* CASE [iter] function *)
  | [ H: ListMonad.iter _ _ ?S1 = OK _ ?S2 |- ?P ?S1 ?S2 ] =>
      eapply (iter_inv_state P H); [
        eauto with typeclass_instances |
        eauto with typeclass_instances |
        let a := fresh "a" in
        let x := fresh "x" in
        let S := fresh "s" in
        let S' := fresh "s'" in
        let EQ := fresh "EQ" in
        intros a S x S' EQ;
        pattern S, S'
      ]; try solve_sinv_pattern
      
      (* eapp_inv_state2 (iter_inv_state P H); try solve_sinv_pattern *)
  (* CASE [find] function *)
  | [ H: ListMonad.find _ _ ?S1 = OK _ ?S2 |- ?P ?S1 ?S2 ] =>
      eapp_inv_state2 (find_inv_state P H); try solve_sinv_pattern
                                                
  (* CASE [getv] function *)
  | [ H: ListMonad.getv _ _ _ ?S1 = OK _ ?S2 |- ?P ?S1 ?S2 ] =>
      rewrite (getv_inv_state H); clear H; auto
  (* CASE [inject_t] function *)
  | [ H: inject_t _ _ _ _ ?S1 = OK _ ?S2 |- ?P ?S1 ?S2 ] =>
      erewrite (inject_t_inv_state H); eauto
                                         
  (* CASE [foreach] function *)
  | [ H: ListMonad.foreach _ _ ?S1 = OK _ ?S2 |- ?P ?S1 ?S2 ] =>
      eapp_inv_state1 (foreach_inv_state P H); try solve_sinv_pattern

  (* If [H] is of the form [G A1 ... A__n S1 = OK X S2] where [G] is a
     function identifier, then calls the [cbn] tactic on [H]. *)
  | [ H: ?G _ _ _ _ _ _ ?S1 = OK ?X ?S2 |- ?P ?S1 ?S2 ] =>
      ((progress cbn in H) || (unfold G in H)); try solve_sinv_pattern
  | [ H: ?G _ _ _ _ _ ?S1 = OK ?X ?S2 |- ?P ?S1 ?S2 ] =>
      ((progress cbn in H) || (unfold G in H)); try solve_sinv_pattern  
  | [ H: ?G _ _ _ _ ?S1 = OK ?X ?S2 |- ?P ?S1 ?S2 ] =>
      ((progress cbn in H) || (unfold G in H)); try solve_sinv_pattern
  | [ H: ?G _ _ _ ?S1 = OK ?X ?S2 |- ?P ?S1 ?S2 ] =>
      ((progress cbn in H) || (unfold G in H)); try solve_sinv_pattern
  | [ H: ?G _ _ ?S1 = OK ?X ?S2 |- ?P ?S1 ?S2 ] =>
      ((progress cbn in H) || (unfold G in H)); try solve_sinv_pattern
  | [ H: ?G _ ?S1 = OK ?X ?S2 |- ?P ?S1 ?S2 ] =>
      ((progress cbn in H) || (unfold G in H)); try solve_sinv_pattern
  | [ H: ?G ?S1 = OK ?X ?S2 |- ?P ?S1 ?S2 ] =>
      ((progress cbn in H) || (unfold G in H)); try solve_sinv_pattern
  end.

(* Unit tests on [solve_sinv]. *)

Require Import Sitpn.
Require Import common.ListPlus.
Require Import RelationClasses.

Lemma gen_tinfos_inv_γ :
  forall {sitpn s v s'},
    generate_trans_infos sitpn s = OK v s' ->
    γ s = γ s'.
Proof. intros; pattern s, s'; solve_sinv_pattern. Qed.                                                                                         

Lemma gen_tinfos_inv_sil_lofps :
  forall {sitpn s v s'},
    generate_trans_infos sitpn s = OK v s' ->
    Sig_in_List (lofPs s) ->
    Sig_in_List (lofPs s').
Proof. intros *; intros H; pattern s, s'; solve_sinv_pattern.
       Set Ltac Backtrace.
       Set Ltac Debug.
       solve_sinv_pattern.
Qed.

Lemma gen_pinfos_inv_γ :
  forall {sitpn decpr s v s'},
    generate_place_infos sitpn decpr s = OK v s' ->
    γ s = γ s'.
Proof. intros; pattern s, s'; solve_sinv_pattern. Qed.

Lemma gen_pinfos_inv_sil_lofps :
  forall {sitpn decpr s v s'},
    generate_place_infos sitpn decpr s = OK v s' ->
    Sig_in_List (lofPs s) ->
    Sig_in_List (lofPs s').
Proof. intros *; intros H; pattern s, s'; solve_sinv_pattern. Qed.

Lemma gen_cinfos_inv_γ :
  forall {sitpn s v s'},
    generate_cond_infos sitpn s = OK v s' ->
    γ s = γ s'.
Proof. intros *; intros H; pattern s, s'; solve_sinv_pattern. Qed.

Lemma gen_sitpn_infos_inv_γ :
  forall {sitpn decpr s v s'},
    generate_sitpn_infos sitpn decpr s = OK v s' ->
    γ s = γ s'.
Proof. 
