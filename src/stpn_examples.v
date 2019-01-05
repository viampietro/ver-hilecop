Require Export STPN spn_examples.

(**********************************)
(********   example (1)   *********)
(**********************************)

Print two_positive.
Lemma four_positive : 4 > 0. Proof. omega. Qed.

Lemma preuve2le4 : 2 <= 4. Proof. omega. Qed.
Lemma preuve1le2 : 1 <= 2. Proof. omega. Qed. 

Definition int_1_2 := mk_chrono 1 2 preuve1le2 0.
Definition int_2_4 := mk_chrono 2 4 preuve2le4 0.

Definition ex_chronos : trans_type -> option chrono_type :=
  fun trans => 
    match trans with
    | (tr 9)  =>  Some int_1_2
    | (tr 4)  =>  Some int_2_4
    | _ => None
    end.

Definition ex_stpn := mk_STPN ex_spn1 ex_chronos.

Definition test_ex_stpn := (stpn_animate ex_stpn 3).

(* 9 steps takes 19.843 secs! *)
(* Time Eval compute in (stpn_animate ex_stpn 9). *)

(********************************************************)
(**************** example 2 *****************************)
(********************************************************)

(****  intervals need lemmas and structures .... ****) 
Lemma three_positive : 3 > 0. Proof. omega. Qed.
Lemma five_positive : 5 > 0. Proof. omega. Qed.
Lemma twototheeight_positive : 256 > 0. Proof. omega. Qed.

(*
Definition three_star := mk_nat_star
                           3
                           three_positive.
Definition five_star := mk_nat_star
                           5
                           five_positive.
Definition two_star := mk_nat_star
                           2
                           two_positive.
Definition twototheeight_star := mk_nat_star
                           256
                           twototheeight_positive.
 
Lemma preuve3le5 : three_star <=i five_star. 
Proof. unfold lebi. Admitted.
Lemma preuve2le256 : two_star <=i twototheeight_star.
Proof. unfold lebi. Admitted.
 *)

Lemma preuve3le5 : 3 <= 5. 
Proof. omega. Qed.
Lemma preuve2le256 : 2 <= 256.
Proof. omega. Qed.

Definition int_3_5 := mk_chrono 3 5 preuve3le5 0.
Definition int_2_256 := mk_chrono 2 256 preuve2le256 0.

Definition ex2_chronos :
  trans_type -> option chrono_type :=
  fun trans => 
    match trans with
    | (tr 3)  =>  Some int_3_5
    | (tr 5)  =>  Some int_2_256
    | _ => None
    end.
    
Definition ex2_stpn := mk_STPN ex2_spn ex2_chronos.

