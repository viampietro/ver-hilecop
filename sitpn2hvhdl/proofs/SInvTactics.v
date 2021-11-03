(** * Tactics for state invariants *)

Require Import common.StateAndErrorMonad.
Require Import common.proofs.StateAndErrorMonadTactics.
Require Import common.proofs.ListMonadFacts.
Require Import common.proofs.ListMonadTactics.

Require Import sitpn2hvhdl.Sitpn2HVhdlTypes.
Require Import sitpn2hvhdl.GenerateInfos.

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
               
  (*  *)
  | [ H: Ret _ ?S1 = OK _ ?S2 |- ?S1 = ?S2 ] =>
      inversion H; clear H; subst; solve_sinv
  | [ H: Ret _ ?S1 = OK _ ?S2 |- ?F ?S1 = ?F ?S2 ] =>
      inversion H; clear H; subst; solve_sinv
  | [ H: Get ?S1 = OK _ ?S2 |- ?S1 = ?S2 ] =>
      inversion H; clear H; subst; solve_sinv
  | [ H: Get ?S1 = OK _ ?S2 |- ?F ?S1 = ?F ?S2 ] =>
      inversion H; clear H; subst; solve_sinv
                                     
  (*  *)
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
      destr_bind1 F G X S1 S2; try solve_sinv
  | [ H: Bind ?F ?G ?S1 = OK ?X ?S2 |- ?A ?S1 = ?A ?S2 ] =>
      destr_bind2 F G X S1 S2 H A; try solve_sinv
                                                                        
  (* If [H] is of the form [(match G with | Error _ => _ OK _ _ => _
     end) = OK X S2] where [G] is a function identifier, then solve
     the case where [Error = OK] with [discriminate], and tries to
     solve the remaining case (i.e. where [G = OK]) with [solve_sinv]
     . *)
  | [ H: (match ?G with | Error _ => _ | OK _ _ => _ end = OK _ ?S2) |- ?F ?S1 = ?F ?S2 ]  =>
      destr_match_monad H G; try solve_sinv
  | [ H: (match ?L with | nil => _ | cons _ _ => _ end) ?S1 = OK ?X ?S2 |- ?F ?S1 = ?F ?S2 ] =>
      destruct L; try solve_sinv
                      
  (* If [H] is of the form [(if C then _ else _) S1 = OK X S2], then
     calls [solve_sinv] in the two if branches. *)                        
  | [ H: (if ?C then _ else _) ?S1 = OK _ ?S2 |- ?F ?S1 = ?F ?S2 ] =>                                 
      destruct C; try solve_sinv
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
                      
  (*  *)
  | [ H: ListMonad.fold_left _ _ _ ?S1 = OK _ ?S2 |- ?F ?S1 = ?F ?S2 ] =>
      pattern S1, S2; eapply (foldl_inv_state H); intros; eauto with typeclass_instances;
      try solve_sinv
  | [ H: ListMonad.iter _ _ ?S1 = OK _ ?S2 |- ?F ?S1 = ?F ?S2 ] =>
      pattern S1, S2; eapply (iter_inv_state H); intros; eauto with typeclass_instances;
      try solve_sinv
  | [ H: ListMonad.find _ _ ?S1 = OK _ ?S2 |- ?F ?S1 = ?F ?S2 ] =>
      pattern S1, S2; eapply (find_inv_state H); intros; eauto with typeclass_instances;
      try solve_sinv
  | [ H: ListMonad.getv _ _ _ ?S1 = OK _ ?S2 |- ?F ?S1 = ?F ?S2 ] =>
      rewrite (getv_inv_state H); clear H; reflexivity
  | [ H: inject_t _ _ _ _ ?S1 = OK _ ?S2 |- ?F ?S1 = ?F ?S2 ] =>
      pattern S1, S2; erewrite (inject_t_inv_state H); eauto
                                           
  (* If [H] is of the form [G A1 ... A__n S1 = OK X S2] where [G] is a
     function identifier, then calls the [cbn] tactic on [H]. *)
  | [ H: ?G _ _ _ ?S1 = OK ?X ?S2 |- ?S1 = ?S2 ] =>
      ((progress cbn in H) || (unfold G in H)); solve_sinv
  | [ H: ?G _ _ _ ?S1 = OK ?X ?S2 |- ?F ?S1 = ?F ?S2 ] =>
      ((progress cbn in H) || (unfold G in H)); solve_sinv
  | [ H: ?G _ _ ?S1 = OK ?X ?S2 |- ?S1 = ?S2 ] =>
      ((progress cbn in H) || (unfold G in H)); solve_sinv
  | [ H: ?G _ _ ?S1 = OK ?X ?S2 |- ?F ?S1 = ?F ?S2 ] =>
      ((progress cbn in H) || (unfold G in H)); solve_sinv
  | [ H: ?G _ ?S1 = OK ?X ?S2 |- ?S1 = ?S2 ] =>
      ((progress cbn in H) || (unfold G in H)); solve_sinv
  | [ H: ?G _ ?S1 = OK ?X ?S2 |- ?F ?S1 = ?F ?S2 ] =>
      ((progress cbn in H) || (unfold G in H)); solve_sinv
  | [ H: ?G ?S1 = OK ?X ?S2 |- ?S1 = ?S2 ] =>
      ((progress cbn in H) || (unfold G in H)); solve_sinv
  | [ H: ?G ?S1 = OK ?X ?S2 |- ?F ?S1 = ?F ?S2 ] =>
      ((progress cbn in H) || (unfold G in H)); solve_sinv
  end.

(* Unit tests on [solve_sinv]. *)

Lemma sinv_get_lofPs : forall sitpn x s1 s2, @get_lofPs sitpn s1 = OK x s2 -> s1 = s2. intros; solve_sinv. Defined.
Lemma sinv_lofTs_set_lofPs : forall sitpn Plist s1 x s2, @set_lofPs sitpn Plist s1 = OK x s2 -> lofTs s1 = lofTs s2.
  intros; solve_sinv.
Defined.

Lemma sinv_bind_action_lofPs :
  forall sitpn a id__a s1 x s2,
    @bind_action sitpn a id__a s1 = OK x s2 -> lofPs s1 = lofPs s2.
  intros; solve_sinv.
Defined.

Lemma sinv_set_finfos_lofPs :
  forall sitpn finfo s1 x s2, @set_finfo sitpn finfo s1 = OK x s2 -> lofPs s1 = lofPs s2.
  intros; solve_sinv.
Defined.

Lemma sinv_generate_trans_infos_lofTs :
  forall sitpn s1 x s2, generate_trans_infos sitpn s1 = OK x s2 -> lofTs s1 = lofTs s2.
  intros; solve_sinv.
Defined.

Lemma sinv_generate_place_infos_lofTs :
  forall sitpn decpr s1 x s2, @generate_place_infos sitpn decpr s1 = OK x s2 -> lofTs s1 = lofTs s2.
  intros; solve_sinv.
Defined.

Lemma sinv_generate_place_infos_lofPs :
  forall sitpn decpr s1 x s2, @generate_place_infos sitpn decpr s1 = OK x s2 -> lofPs s1 = lofPs s2.
  intros; solve_sinv.
Defined.

Lemma sinv_generate_action_infos_lofPs :
  forall sitpn s1 x s2, @generate_action_infos sitpn s1 = OK x s2 -> lofPs s1 = lofPs s2.
  intros; solve_sinv.
Defined.

Lemma sinv_generate_cond_infos_lofPs :
  forall sitpn s1 x s2, @generate_cond_infos sitpn s1 = OK x s2 -> lofPs s1 = lofPs s2.
  intros; solve_sinv.
Defined.

Lemma sinv_generate_fun_infos_lofPs :
  forall sitpn s1 x s2, @generate_fun_infos sitpn s1 = OK x s2 -> lofPs s1 = lofPs s2.
  intros; solve_sinv.
Defined.
