Require Export STPN  spn_examples.


(**********************************)
(********   example (1)   *********)
(**********************************)

Print two_positive.
Lemma four_positive : 4 > 0. Proof. omega. Qed.

Lemma preuve2le4 : 2 <= 4. 
Proof. omega. Qed.
Lemma preuve1le2 : 1 <= 2.
Proof. omega. Qed.


Compute (transs ex_spn1). (* no 7 no 10 no 15 *)

Definition int_1_2 := mk_chrono
                        1        2
                        preuve1le2         0.
Definition int_2_4 := mk_chrono
                          2        4
                          preuve2le4     0.

Definition ex_chronos :
  trans_type -> option chrono_type :=
  fun trans => 
    match trans with
    | mk_trans 9  =>  Some int_1_2
    | mk_trans 4  =>  Some int_2_4
    | _ => None
    end.

Definition ex_stpn := mk_STPN
                        ex_spn1
                        ex_chronos.

Definition test_ex_stpn := (stpn_animate ex_stpn 3).

Recursive Extraction test_ex_stpn.

Compute (list_enabled_spn ex_spn1).
Compute (marking ex_spn1).

Compute (stpn_animate
           ex_stpn
           3). (* 3 steps takes ~15 secs ! *)

 
Lemma ex_stpn_animate : (stpn_animate
                           ex_stpn
                           3) =
     [([[]; []; []; [mk_trans 0]; [mk_trans 1]],
        [(mk_place 0, 1); (mk_place 1, 0); 
        (mk_place 2, 1); (mk_place 3, 0); (mk_place 4, 1);
        (mk_place 5, 1); (mk_place 7, 0); (mk_place 8, 0);
        (mk_place 9, 0); (mk_place 10, 0); 
        (mk_place 11, 0); (mk_place 12, 1)],
        [(mk_trans 0, None); (mk_trans 1, None);
        (mk_trans 2, None); (mk_trans 3, None);
        (mk_trans 4, Some (2, 0, 4)); (mk_trans 5, None);
        (mk_trans 6, None); (mk_trans 8, None);
        (mk_trans 9, Some (1, 0, 2)); (mk_trans 12, None);
        (mk_trans 13, None); (mk_trans 14, None);
        (mk_trans 16, None)]);
       ([[]; []; []; [mk_trans 5]; []],
       [(mk_place 0, 1); (mk_place 1, 0); (mk_place 2, 1);
       (mk_place 3, 0); (mk_place 4, 1); (mk_place 5, 0);
       (mk_place 7, 0); (mk_place 8, 0); (mk_place 9, 1);
       (mk_place 10, 0); (mk_place 11, 0); 
       (mk_place 12, 1)],
       [(mk_trans 0, None); (mk_trans 1, None);
       (mk_trans 2, None); (mk_trans 3, None);
       (mk_trans 4, Some (2, 1, 4)); (mk_trans 5, None);
       (mk_trans 6, None); (mk_trans 8, None);
       (mk_trans 9, Some (1, 0, 2)); (mk_trans 12, None);
       (mk_trans 13, None); (mk_trans 14, None);
       (mk_trans 16, None)]);
       ([[]; [mk_trans 4]; []; [mk_trans 2]; []],
       [(mk_place 0, 1); (mk_place 1, 0); (mk_place 2, 0);
       (mk_place 3, 1); (mk_place 4, 0); (mk_place 5, 0);
       (mk_place 7, 0); (mk_place 8, 1); (mk_place 9, 1);
       (mk_place 10, 0); (mk_place 11, 0); 
       (mk_place 12, 1)],
       [(mk_trans 0, None); (mk_trans 1, None);
       (mk_trans 2, None); (mk_trans 3, None);
       (mk_trans 4, Some (2, 0, 4)); (mk_trans 5, None);
       (mk_trans 6, None); (mk_trans 8, None);
       (mk_trans 9, Some (1, 0, 2)); (mk_trans 12, None);
       (mk_trans 13, None); (mk_trans 14, None);
       (mk_trans 16, None)]); ([], [], [])].
Proof. vm_compute. reflexivity. Qed.

(********************************************************)
(**************** example 2 *****************************)
(********************************************************)

Print STPN. Print chrono_type. Print nat_star.
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

Definition int_3_5 := mk_chrono
                        3
                        5
                        preuve3le5
                        0.
Definition int_2_256 := mk_chrono
                          2
                          256
                          preuve2le256
                          0.

Definition ex2_chronos :
  trans_type -> option chrono_type :=
  fun trans => 
    match trans with
    | mk_trans 3  =>  Some int_3_5
    | mk_trans 5  =>  Some int_2_256
    | _ => None
    end.


    
Print pre. Print weight_type. Print STPN.
Definition ex2_stpn := mk_STPN
                        ex2_spn
                        ex2_chronos.

Check ex2_stpn. 
Search STPN.
Check stpn_cycle.
Check stpn_debug2.
Check stpn_animate.

Compute
  (
    stpn_debug2
    (*  (        snd (stpn_cycle  

        (snd (stpn_cycle 
                (snd (stpn_cycle   *)
                        (snd (stpn_cycle      
                                ex2_stpn)
                        )).

(*
Lemma stpn_ok : stpn_debug2
                  (snd (stpn_cycle  
                          (snd (stpn_cycle 
                                  (snd (stpn_cycle   
                                          (snd (stpn_cycle      
                                                  ex2_stpn)
                  ))))))) =
.*)





Compute (stpn_animate
           ex2_stpn
           9).  (* 9 markings but the last one is dub. It works. *)

Lemma ex2_stpn_animate : (stpn_animate
                           ex2_stpn
                           9) =
     [([[]; []; []; [mk_trans 1]],
       [(mk_place 1, 0); (mk_place 2, 1); 
        (mk_place 3, 2); (mk_place 4, 1); (mk_place 5, 0);
        (mk_place 6, 0); (mk_place 7, 0)],
        [(mk_trans 1, None); (mk_trans 2, None);
        (mk_trans 3, Some (3, 0, 5)); (mk_trans 4, None);
        (mk_trans 5, Some (2, 0, 256)); (mk_trans 6, None)]);
       ([[]; []; []; []],
       [(mk_place 1, 0); (mk_place 2, 1); (mk_place 3, 2);
       (mk_place 4, 1); (mk_place 5, 0); (mk_place 6, 0);
       (mk_place 7, 0)],
       [(mk_trans 1, None); (mk_trans 2, None);
       (mk_trans 3, Some (3, 1, 5)); (mk_trans 4, None);
       (mk_trans 5, Some (2, 0, 256)); (mk_trans 6, None)]);
       ([[]; []; []; []],
       [(mk_place 1, 0); (mk_place 2, 1); (mk_place 3, 2);
       (mk_place 4, 1); (mk_place 5, 0); (mk_place 6, 0);
       (mk_place 7, 0)],
       [(mk_trans 1, None); (mk_trans 2, None);
       (mk_trans 3, Some (3, 2, 5)); (mk_trans 4, None);
       (mk_trans 5, Some (2, 0, 256)); (mk_trans 6, None)]);
       ([[]; []; [mk_trans 3]; []],
       [(mk_place 1, 0); (mk_place 2, 1); (mk_place 3, 0);
       (mk_place 4, 0); (mk_place 5, 0); (mk_place 6, 0);
       (mk_place 7, 1)],
       [(mk_trans 1, None); (mk_trans 2, None);
       (mk_trans 3, Some (3, 0, 5)); (mk_trans 4, None);
       (mk_trans 5, Some (2, 0, 256)); (mk_trans 6, None)]);
       ([[mk_trans 6]; []; []; []],
       [(mk_place 1, 1); (mk_place 2, 1); (mk_place 3, 0);
       (mk_place 4, 0); (mk_place 5, 0); (mk_place 6, 0);
       (mk_place 7, 0)],
       [(mk_trans 1, None); (mk_trans 2, None);
       (mk_trans 3, Some (3, 0, 5)); (mk_trans 4, None);
       (mk_trans 5, Some (2, 0, 256)); (mk_trans 6, None)]);
       ([[]; []; []; [mk_trans 2]],
       [(mk_place 1, 0); (mk_place 2, 1); (mk_place 3, 0);
       (mk_place 4, 0); (mk_place 5, 1); (mk_place 6, 0);
       (mk_place 7, 0)],
       [(mk_trans 1, None); (mk_trans 2, None);
       (mk_trans 3, Some (3, 0, 5)); (mk_trans 4, None);
       (mk_trans 5, Some (2, 0, 256)); (mk_trans 6, None)]);
       ([[]; [mk_trans 4]; []; []],
       [(mk_place 1, 0); (mk_place 2, 1); (mk_place 3, 0);
       (mk_place 4, 0); (mk_place 5, 0); (mk_place 6, 1);
       (mk_place 7, 0)],
       [(mk_trans 1, None); (mk_trans 2, None);
       (mk_trans 3, Some (3, 0, 5)); (mk_trans 4, None);
       (mk_trans 5, Some (2, 0, 256)); (mk_trans 6, None)]);
       ([[]; []; []; []],
       [(mk_place 1, 0); (mk_place 2, 1); (mk_place 3, 0);
       (mk_place 4, 0); (mk_place 5, 0); (mk_place 6, 1);
       (mk_place 7, 0)],
       [(mk_trans 1, None); (mk_trans 2, None);
       (mk_trans 3, Some (3, 0, 5)); (mk_trans 4, None);
       (mk_trans 5, Some (2, 1, 256)); (mk_trans 6, None)]);
       ([[]; []; []; [mk_trans 5]],
       [(mk_place 1, 0); (mk_place 2, 0); (mk_place 3, 0);
       (mk_place 4, 0); (mk_place 5, 0); (mk_place 6, 0);
       (mk_place 7, 1)],
       [(mk_trans 1, None); (mk_trans 2, None);
       (mk_trans 3, Some (3, 0, 5)); (mk_trans 4, None);
       (mk_trans 5, Some (2, 0, 256)); (mk_trans 6, None)]);
       ([], [], [])].
Proof. vm_compute. reflexivity. Qed.

       
Compute (all_chronos
           (snd (stpn_cycle
                   (snd (stpn_cycle
                           (snd (stpn_cycle
                                   (snd (stpn_cycle  
                                           ex2_stpn))))))))). 

Compute
  (
    list_enabled_stpn
(*      (snd (stpn_cycle *) 
              ex2_stpn
  ).

Compute (marking
           (spn
              ex2_stpn)). (* initial marking *)
Check marking2list.
Compute (marking2list
           (marking (spn
                       (snd (stpn_cycle  
                               ex2_stpn))))
           (places (spn
                      (snd (stpn_cycle  
                              ex2_stpn))))).
