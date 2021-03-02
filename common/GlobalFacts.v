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
  
  (** Two sigs are seq-equivalent if there first element is Leibniz's equal. *)
  
  Definition seq (u v : {a : A | P a}) : Prop :=
    proj1_sig u = proj1_sig v.

  (* Relation [seq] is reflexive. *)
  
  Lemma seq_refl : forall x : {a : A | P a}, seq x x. reflexivity. Defined.
  
  (* Relation [seq] is symmetric. *)
  
  Lemma seq_sym :  forall x y : {a : A | P a}, seq x y -> seq y x. symmetry; assumption. Defined.

  (* Relation [seq] is transitive. *)
  
  Lemma seq_trans :  forall x y z : {a : A | P a}, seq x y -> seq y z -> seq x z.
    intros; transitivity (proj1_sig y); [assumption|assumption].
  Defined.
  
  (** Given that the equality is decidable for Set A, seq A is decidable. *)
  
  Definition seqdec (u v : {a : A | P a}) : {seq u v} + {~seq u v} :=
    eqA_dec (proj1_sig u) (proj1_sig v).

  (** Equivalence relation between two transitions that are elements of
    a subset of T. *)

  Definition InA_seq_dec :
    forall a lofA,
      {SetoidList.InA seq a lofA} + {~SetoidList.InA seq a lofA}.
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

(** Declares seq as an instance of the Equivalence class. *)
  
  Instance Equivalence_seq {A : Type} (P : A -> Prop) : Equivalence (@seq A P) :=
    { Equivalence_Reflexive := (@seq_refl A P);
      Equivalence_Symmetric := (@seq_sym A P);
      Equivalence_Transitive := (@seq_trans A P) }.

Add Parametric Relation {A : Type} {P : A -> Prop}
    {eqA : A -> A -> Prop}
    {eqA_dec : forall x y : A, {eqA x y} + {~eqA x y}} : ({ a : A | P a}) (@seq A P)
    reflexivity proved by (@seq_refl A P)
    symmetry proved by (@seq_sym A P)
    transitivity proved by (@seq_trans A P)
      as seq_rel.

Arguments seq {A P}.
Arguments seqdec {A P}.

Hint Unfold seq : core.



