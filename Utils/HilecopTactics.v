Require Import Hilecop.Utils.HilecopLemmas.
Require Import Arith List Bool.

Import ListNotations.

(*! ====================================================== !*)  
(*!                                                        !*)
(*!         TACTIC FUNCTIONS FOR THE HILECOP PROGRAM       !*)
(*!                                                        !*)
(*! ====================================================== !*)

Ltac decide_not_in :=
  match goal with
  | |- ~In ?a [] => apply in_nil
  | |- ~In ?a ?l =>
    apply not_in_cons;
    split; [((injection;
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
  | |- incl ?l ?l' =>
    unfold incl;
    intros a H;
    simpl;
    simpl in H;
    decompose [or] H;
    repeat (auto || right)
  end.

(** Search for a hypothesis H of the form (incl l l') 
    and a hypothesis H' of the form (In a l).
    If H and H' in the context then apply H a H'
    and name the resulting hypothesis as Hin. *)

Ltac apply_incl Hin :=
  lazymatch goal with
  | [ H: incl ?l ?l' |- _ ] =>
    lazymatch goal with
    | [H': In ?a l |- _ ] => specialize (H a H') as Hin
    | _ => fail "No hypotheses of the form (In ?a ?l) in the context"
    end
  | _ => fail "No hypotheses of the form (incl ?l ?l') in the context"
  end.

(** If Hincl_fs is a the form (incl (fst (split (?a, ?b) :: _)) _)
    then rewrites Hincl_fs in (incl (fst (split _))), i.e removes
    the head. *)

Ltac incl_rm_hd_fs Hincl_fs :=
  match Hincl_fs with
  | ?H: incl (fst (split ((_, _) :: _))) _ =>
    rewrite fst_split_cons_app in Hincl_fs;
    simpl in Hincl_fs;
    apply incl_cons_inv in Hincl_fs
  | _ => fail "Argument is not of the form (incl (fst (split (?a, ?b) :: _)) _)"
  end.

(**  *)

Check (let x := (1, 1) in x).

Ltac contradiction_with_nodup_same_pair l p p' Hin_p_l Hin_p'_l :=

  (* Checks that arguments are well-typed. *)
  lazymatch Hin_p_l with
  | ?H: In p l =>
    lazymatch Hin_p'_l with
    | ?H': In p' l =>
      lazymatch goal with
      | [ Hnodup: NoDup (fst (split l)) |- _ ] =>
            
            (* Specializes nodup_same_pair then shows a contradiction. *)
            assert (Heq_fs_pair : fst p = fst p') by (simpl; auto);
            specialize (nodup_same_pair l Hnodup p p' Hin_p_l Hin_p'_l Heq_fs_pair);
            intros Heq_pp';
            (injection Heq_pp' as Heq_snd_pp'; inversion Heq_snd_pp') || auto
                       
      | _ => fail "No hypothesis of the form NoDup (fst (split l))"
      end

    | _ => fail "Argument is not of the form In (?a, ?b) ?l" 
    end
  | _ => fail "Argument is not of the form In (?a, ?b) ?l"
  end.

  (*   lazymatch type of p with *)
  (*   | (A * B)%type => *)
  (*     lazymatch type of p' with *)
  (*     | (A * B)%type => *)

  (*       (* Checks that context contains the proper hypotheses:  *)
  (*          NoDup (fs l) ∧ p ∈ l ∧ p' ∈ l. *) *)
  (*       lazymatch goal with *)
  (*       | [ Hnodup: NoDup (fst (split l)) |- _ ] => *)
  (*         lazymatch goal with *)
  (*         | [ Hin_p_l: In p l |- _ ] => *)
  (*           lazymatch goal with *)
  (*           | [ Hin_p'_l: In p' l |- _ ] => *)
              
  (*             (* Specializes nodup_same_pair then shows a contradiction. *) *)
  (*             assert (Heq_fs_pair : fst p = fst p') by (simpl; auto); *)
  (*             specialize (nodup_same_pair l Hnodup p p' Hin_p_l Hin_p'_l Heq_fs_pair) *)
                        
  (*           | _ => fail "No hypothesis of the form In p' l" *)
  (*           end *)
  (*         | _ => idtac p *)
  (*         end *)
  (*       | _ => fail "No hypothesis of the form NoDup (fst (split l))" *)
  (*       end *)
  (*     | _ => fail "Argument p' is not of type (?A * ?B)" *)
  (*     end *)
  (*   | _ => fail "Argument p is not of type (?A * ?B)" *)
  (*   end *)
  (* | _ => fail "Argument l is not of type list (?A * ?B)" *)
  (* end. *)
