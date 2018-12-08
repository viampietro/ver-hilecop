Require Export Arith Omega List Bool Bool.Sumbool Bool.Bool Coq.Lists.ListDec FunInd.
Export ListNotations.

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