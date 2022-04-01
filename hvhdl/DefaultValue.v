(** * Default values of types. *)

(** Defines the relation yielding the implicit default value 
    associated to a type. 
    
    This relation is useful to determine the default value
    associated to declared signals and variables during the
    elaboration phase.
 
 *)

Require Import common.CoqLib.
Require Import common.GlobalTypes.

Require Import hvhdl.SemanticalDomains.

Open Scope N_scope.

(** The [DefaultV] relation states that a type is associated 
    to an implicit default value. *)

Inductive DefaultV : type -> value -> Prop :=
  
| DefaultVBool : DefaultV Tbool (Vbool false)
| DefaultVNat : forall l u, WFType (Tnat l u) -> DefaultV (Tnat l u) (Vnat l)
| DefaultVArray :
  forall t l u v,
    let size := (N.to_nat (u - l)) in
    WFType (Tarray t l u) ->
    DefaultV t v ->
    DefaultV (Tarray t l u) (Varr (create_arr (S size) v (Nat.lt_0_succ size))).

#[export] Hint Constructors DefaultV : hvhdl.

(** Defines the function yielding the implicit default value
    associated to a type. *)

Import ErrMonadNotations.
Require Import String.

Fixpoint defaultv (t : type) {struct t} : optionE value :=
  match t with
  | Tbool => Ret (Vbool false)
  | Tnat l u => if WFType_dec t then Ret (Vnat l) else Err "defaultv: found ill-formed nat type"
  | Tarray ta l u =>
      let size := N.to_nat (u - l) in
      if WFType_dec t then
        do v <- defaultv ta; Ret (Varr (create_arr (S size) v (Nat.lt_0_succ size)))
      else Err "defaultv: found ill-formed array type"
  end.

Functional Scheme defaultv_ind := Induction for defaultv Sort Prop.

(** Soundness of [defaultv] *)

Lemma defaultv_sound :
  forall t v, defaultv t = Success v -> DefaultV t v.
Proof.
  intros t; functional induction (defaultv t) using defaultv_ind.
  all: try (solve [inversion 1]); inversion 1; constructor; auto.
Qed.

(** Completeness of [defaultv] *)

Lemma defaultv_compl :
  forall t v, DefaultV t v -> defaultv t = Success v.
Proof.
  intros t; induction 1.
  cbn; reflexivity.
  cbv iota beta delta [defaultv].
  edestruct (WFType_dec (Tnat l u)); (contradiction || eauto).
  cbn iota delta [defaultv]; edestruct (WFType_dec (Tarray t l u)); (contradiction || eauto).
  rewrite IHDefaultV.
  reflexivity.
Qed.
