(** * Facts about H-VHDL Semantical Domains *)

Require Import common.CoqLib.
Require Import common.ListPlus.
Require Import hvhdl.SemanticalDomains.

(* Lemma BProd_aofv_false :  *)
(*   forall aofv n m, *)
(*     (exists i, n <= i < m /\ get_bool_at aofv i = false) -> *)
(*     BProd (get_bool_at aofv) (seq n m) false. *)
(* Admitted. *)

(** ** Facts about [IsOfType] *)

Lemma arrisoftype_inv_set_at :
  forall aofv n t,
    ArrIsOfType aofv n t ->
    forall i in_bounds v,
      IsOfType v t ->
      ArrIsOfType (set_at v i aofv in_bounds) n t.
Proof.
  induction 1.
  - intro; destruct i; cbn; [ constructor; assumption | lia ].
  - intro; destruct i; cbn.
    constructor; assumption.
    constructor. assumption.
    eapply IHArrIsOfType; eauto.
Qed.

Lemma IsOfType_inv_set_at :
  forall aofv i v in_bounds t l u,
    IsOfType (Varr aofv) (Tarray t l u) ->
    IsOfType v t ->
    IsOfType (Varr (set_at v i aofv in_bounds)) (Tarray t l u).
Proof.
  (* induction aofv; destruct i. *)
  (* (* CASE aofv = [v0] and i = 0 *) *)
  (* - inversion_clear 1; constructor; auto. *)
  (*   cbn. *)
  (*   match goal with *)
  (*   | H: ArrIsOfType _ _ _ |- _ => *)
  (*       inversion_clear H; constructor; assumption *)
  (*   end. *)
  (* (* CASE aofv = v0 :: tl and i = 0 *) *)
  (* - inversion_clear 1; constructor; auto. *)
  (*   match goal with *)
  (*   | H: ArrIsOfType _ _ _ |- _ => *)
  (*       inversion_clear H; constructor(* ; assumption *) *)
  (*   end. *)
  (* (* CASE aofv = [v0] and i > 0 *) *)
  (* - cbn in H; lia. *)
  (* (* CASE aofv = v0 :: tl and i > 0 *) *)
  (* - inversion_clear 1; constructor; auto. *)
  (*   match goal with *)
  (*   | H: ArrIsOfType _ _ _ |- _ => *)
  (*       inversion_clear H; constructor; *)
  (*       [ assumption | eapply arrisoftype_inv_set_at; eauto ] *)
  (*   end. *)
Admitted.

(** ** Facts about [OVEq] *)

Lemma OVEq_eq_1 :
  forall val1 val2, OVEq val1 val2 (Some true) -> val1 = val2.
Proof.
  apply (value_ind_mut
           (fun v => forall val2, OVEq v val2 (Some true) -> v = val2)
           (fun aofv => forall val2, OVEq (Varr aofv) val2 (Some true) -> (Varr aofv) = val2));
    try ((inversion 1; subst; reflexivity) || auto).
  do 2 intro.
  apply (value_ind_mut
           (fun v2 => OVEq (Varr (Arr_one v)) v2 (Some true) -> (Varr (Arr_one v)) = v2)
           (fun aofv2 => OVEq (Varr (Arr_one v)) (Varr aofv2) (Some true) -> Arr_one v = aofv2)).
  1,2: inversion 1.
  intros a e1 e2; erewrite e1; eauto.
  inversion 2; subst.
  inversion H4; subst; erewrite H; eauto.
  inversion 3; inversion H5.
  do 4 intro.
  apply (value_ind_mut
           (fun v2 => OVEq (Varr (Arr_cons v a)) v2 (Some true) -> (Varr (Arr_cons v a)) = v2)
           (fun aofv2 => OArrOfVEq (Arr_cons v a) aofv2 (Some true) -> (Arr_cons v a) = aofv2)).
  1,2: inversion 1.
  inversion 2; erewrite H1; eauto.
  inversion 2; subst; inversion H5.
  inversion_clear 3.
  assert (OVEq (Varr a) (Varr a0) (Some true)) by (eapply OVEq_ArrT; eauto).
  erewrite H; eauto.
  assert (e : Varr a = Varr a0) by (eapply H0; eauto).
  inject_left e; reflexivity.
Qed.

Lemma OVEq_eq_2 :
  forall val1 val2, val1 = val2 -> OVEq val1 val2 (Some true).
Proof. intros val1 val2 e; rewrite e.
       apply (value_ind_mut
                (fun v => OVEq v v (Some true))
                (fun aofv => OArrOfVEq aofv aofv (Some true)));
         eauto with hvhdl.
Qed.


