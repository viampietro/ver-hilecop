Require Export Arith Omega List Bool Bool.Sumbool Bool.Bool Coq.Lists.ListDec FunInd.
Export ListNotations.

(*=================================*  
 *                                 *
 *         HELPER LEMMAS           *
 *                                 *
 *=================================*)

(* Lemma : Proves a property over the combination of fst and split 
   *         functions.
   *)
  Lemma fst_split_app {A B : Type} :
    forall (a : (A * B)) (l : list (A * B)),
      fst (split (a :: l)) = (fst (split [a])) ++ (fst (split l)).
  Proof.
    intros.
    elim a; simpl.
    elim split; simpl.
    auto.
  Qed.


(*  
 * Lemma : If in_eq is True implies P then P.
 *)
  Lemma in_eq_impl {A : Type} :
    forall (a : A) (l : list A) (P : Prop),
      (In a (a :: l) -> P) -> P.
  Proof.
    intros.
    apply H; apply in_eq.
  Qed.

  (*  
   * Lemma : If a is in list l and l is in list of lists ll
   *         then a is in (concat ll).
   *         The result of (concat ll) is one list corresponding
   *         to the concatenation of all lists in ll.  
   *)
  Lemma in_concat {A : Type} :
    forall (a : A) (l : list A) (ll : list (list A)),
      In a l -> In l ll -> In a (concat ll).
  Proof.
    intros.
    induction ll.
    (* Base case, ll = []. *)
    - elim H0.
    (* Inductive case. *)
    - apply in_inv in H0; elim H0; intros.
      + rewrite <- H1 in H.
        apply or_introl with (B := In a (concat ll)) in H.
        apply in_or_app in H.
        rewrite concat_cons.
        auto.
      + apply IHll in H1.
        apply or_intror with (A := In a a0) in H1.
        apply in_or_app in H1.
        rewrite concat_cons.
        auto.
  Qed.
  
(*==========================================================*  
 *                                                          *
 *         TACTIC FUNCTIONS FOR THE HILECOP PROGRAM         *
 *                                                          *
 *==========================================================*)
  
(*
 * Decides that an accessor function returns no error.  
 *)
Ltac decide_accessor_no_err :=
  match goal with
  | [ H : In ?e (fst (split nil)) |- _ ] => elim H; decide_accessor_no_err
  | [|- exists _ : _, Some ?n = Some _ ] => exists n; reflexivity; decide_accessor_no_err
  | [ IHo : _ -> ?G, H : _ |- ?G ] => apply IHo;
                                      rewrite fst_split_app in H;
                                      simpl in H;
                                      elim H;
                                      intros; [decide_accessor_no_err | auto]
  | [ e1 : ( _ =? _ ) = false, H0 : _ = _ |- _] => apply beq_nat_false in e1;
                                                   (contradiction || symmetry in H0; contradiction)
  end.
