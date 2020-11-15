(** * Global facts used in the overall project. *)

Require Import SetoidList.

(** Completes the Coq standard library. *)

Set Implicit Arguments.

(** ** Equivalence relation for sig. *)

Section SigEq.

  Variable A : Type.
  Variable P : A -> Prop.
  Variable Aeqdec : forall x y : A, {x = y} + {x <> y}.
  
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
    Aeqdec (proj1_sig u) (proj1_sig v).

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
      + specialize (Aeqdec (proj1_sig a) (proj1_sig a0)) as Heqdec; inversion Heqdec;
          [ left; apply SetoidList.InA_cons; left; assumption |
            right; intro; inversion_clear H1; contradiction].
  Defined.
  
End SigEq.

Arguments seq {A P}.
Arguments seqdec {A P}.

