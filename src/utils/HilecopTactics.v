Require Import Hilecop.Utils.HilecopLemmas.

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
                                      rewrite fst_split_cons_app in H;
                                      simpl in H;
                                      elim H;
                                      intros; [decide_accessor_no_err | auto]
  | [ e1 : ( _ =? _ ) = false, H0 : _ = _ |- _] => apply beq_nat_false in e1;
                                                   (contradiction || symmetry in H0; contradiction)
  end.

Ltac decide_not_in :=
  match goal with
  | |- ~In ?a [] => apply in_nil
  | |- ~In ?a ?l => apply not_in_cons; split; [((injection;
                                                 intros Hinv;
                                                 inversion Hinv)
                                                || auto)
                                              | decide_not_in]
  end.

Ltac decide_nodup :=
  match goal with
  | |- NoDup [] => apply NoDup_nil
  | |- NoDup ?l => apply NoDup_cons; [ decide_not_in | decide_nodup ]
  end.

Ltac decide_incl :=
  match goal with
  | |- incl ?l ?l' => unfold incl;
                      intros a H;
                      simpl;
                      simpl in H;
                      decompose [or] H;
                      repeat (auto || right)
  end.
