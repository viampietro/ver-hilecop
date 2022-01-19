(** * Global facts used in the overall project. *)

Require Import SetoidList.

(** Completes the Coq standard library. *)

Set Implicit Arguments.

(** ** Extra facts about the [option] type *)

Definition some_to_nnone {A} (f : option A) (a : A) (pf : f = Some a) : f <> None.
  intros pf'; rewrite pf in pf'; inversion pf'.
Defined.

(** ** Equivalence relation for sig. *)

Section SigEq.

  Variable A : Type.
  Variable P : A -> Prop.
  Variable eqA_dec : forall x y : A, {x = y} + {x <> y}.
  
  (** Two sigs are P1SigEq-equivalent if there first element is Leibniz's equal. *)
  
  Definition P1SigEq (u v : {a : A | P a}) : Prop :=
    proj1_sig u = proj1_sig v.

  (* Relation [P1SigEq] is reflexive. *)
  
  Lemma P1SigEq_refl : forall x : {a : A | P a}, P1SigEq x x. reflexivity. Defined.
  
  (* Relation [P1SigEq] is symmetric. *)
  
  Lemma P1SigEq_sym :  forall x y : {a : A | P a}, P1SigEq x y -> P1SigEq y x. symmetry; assumption. Defined.

  (* Relation [P1SigEq] is transitive. *)
  
  Lemma P1SigEq_trans :  forall x y z : {a : A | P a}, P1SigEq x y -> P1SigEq y z -> P1SigEq x z.
    intros; transitivity (proj1_sig y); [assumption|assumption].
  Defined.
  
  (** Given that the equality is decidable for Set A, P1SigEq A is decidable. *)
  
  Definition P1SigEqdec (u v : {a : A | P a}) : {P1SigEq u v} + {~P1SigEq u v} :=
    eqA_dec (proj1_sig u) (proj1_sig v).

  (** Equivalence relation between two transitions that are elements of
    a subset of T. *)

  Definition InA_P1SigEq_dec :
    forall a lofA,
      {SetoidList.InA P1SigEq a lofA} + {~SetoidList.InA P1SigEq a lofA}.
  Proof.
    intros; induction lofA.
    
    - right; inversion 1.
    - inversion IHlofA.
      + left; apply SetoidList.InA_cons; right; assumption.
      + specialize (eqA_dec (proj1_sig a) (proj1_sig a0)) as Heqdec; inversion Heqdec;
          [ left; apply SetoidList.InA_cons; left; assumption |
            right; intro; inversion_clear H1; contradiction].
  Defined.
  
End SigEq.

(** Declares P1SigEq as an instance of the Equivalence class. *)
  
#[export] Instance Equivalence_P1SigEq {A : Type} (P : A -> Prop) : Equivalence (@P1SigEq A P) :=
  { Equivalence_Reflexive := (@P1SigEq_refl A P);
      Equivalence_Symmetric := (@P1SigEq_sym A P);
      Equivalence_Transitive := (@P1SigEq_trans A P) }.

Add Parametric Relation {A : Type} {P : A -> Prop}
    {eqA : A -> A -> Prop}
    {eqA_dec : forall x y : A, {eqA x y} + {~eqA x y}} : ({ a : A | P a}) (@P1SigEq A P)
    reflexivity proved by (@P1SigEq_refl A P)
    symmetry proved by (@P1SigEq_sym A P)
    transitivity proved by (@P1SigEq_trans A P)
      as P1SigEq_rel.

Arguments P1SigEq {A P}.
Arguments P1SigEqdec {A P}.

#[export] Hint Unfold P1SigEq : core.



