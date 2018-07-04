Require Export STPN.

(******************************************************************)
(***** David Andreu's first example (redrawn in my Oxford) ********)

(* 7 places *)
Definition ex_places : (list place_type) :=
  [ mk_place 1 ;
    mk_place 2 ;
    mk_place 3 ;
    mk_place 4 ;
    mk_place 5 ;
    mk_place 6 ;
    mk_place 7 ].
Definition ex_nodup_places : NoDup ex_places :=
  NoDup_nodup
    places_eq_dec
    ex_places. 

(* 6 transitions *)
Definition ex_transs : (list trans_type) :=
  [ mk_trans 1 ;
    mk_trans 2 ;
    mk_trans 3 ;
    mk_trans 4 ;
    mk_trans 5 ;
    mk_trans 6 ].
Definition ex_nodup_transs : NoDup ex_transs :=
  NoDup_nodup
    transs_eq_dec
    ex_transs.

(* one lemma for each arc weight ...  already done*)

(* Require Export spn_examples. (* surtout pas ! *) *)

Lemma one_positive : 1 > 0. Proof. omega. Qed.
Lemma two_positive : 2 > 0. Proof. omega. Qed.
(* one lemma for each arc weight ... *)

(* 7 arcs PT (place transition)  "incoming" *) 
Definition ex_pre (t : trans_type) (p : place_type)
  : option nat_star :=
  match (t,p) with
  | (mk_trans 1, mk_place 1) => Some (mk_nat_star
                                        1
                                        one_positive)
  | (mk_trans 2, mk_place 1) => Some (mk_nat_star
                                        1
                                        one_positive)
  | (mk_trans 3, mk_place 3) => Some (mk_nat_star
                                        2
                                        two_positive)
  | (mk_trans 3, mk_place 4) => Some (mk_nat_star
                                        1
                                        one_positive)
  | (mk_trans 4, mk_place 5) => Some (mk_nat_star
                                        1
                                        one_positive)
  | (mk_trans 5, mk_place 2) => Some (mk_nat_star
                                        1
                                        one_positive)  
  | (mk_trans 5, mk_place 6) => Some (mk_nat_star
                                        1
                                        one_positive)
  | (mk_trans 6, mk_place 7) => Some (mk_nat_star
                                        1
                                        one_positive)
  | _ => None
  end.

Definition ex_test (t : trans_type) (p : place_type) :=
  (* 1 arc of type "test" *)
  match (t, p) with
  | (mk_trans 2, mk_place 2) => Some (mk_nat_star
                                        1
                                        one_positive)               
  | _ => None
  end.

Definition ex_inhib (t : trans_type) (p : place_type) :=
  (* 1 arc of type "inhibitor"  *)
  match (t, p) with
  | (mk_trans 1, mk_place 2) => Some (mk_nat_star
                                        1
                                        one_positive)               
  | _ => None
  end.

(* 7 arcs TP      "outcoming"  *)
Definition ex_post (t : trans_type) (p : place_type)
  : option nat_star :=
  match (t, p) with
  (* trans 1 *)
  | (mk_trans 1, mk_place 2) => Some (mk_nat_star
                                        1
                                        one_positive)               
  | (mk_trans 1, mk_place 3) => Some (mk_nat_star
                                        2
                                        two_positive)               
  | (mk_trans 1, mk_place 4) => Some (mk_nat_star
                                        1
                                        one_positive)
  (* trans 2 *)
  | (mk_trans 2, mk_place 5) => Some (mk_nat_star
                                        1
                                        one_positive)
  (* trans 3 *)
  | (mk_trans 3, mk_place 7) => Some (mk_nat_star
                                        1
                                        one_positive)
  (* trans 4 *)
  | (mk_trans 4, mk_place 6) => Some (mk_nat_star
                                        1
                                        one_positive)
  (* trans 5 *)
  | (mk_trans 5, mk_place 7) => Some (mk_nat_star
                                        1
                                        one_positive)
  (* trans 6 *)
  | (mk_trans 6, mk_place 1) => Some (mk_nat_star
                                        1
                                        one_positive)
  | _ => None
  end.

(* tokens *)
Definition ex_marking (p : place_type) :=
  match p with
  | mk_place 1 => 1
  | mk_place 2 => 0
  | mk_place 3 => 0
  | mk_place 4 => 0
  | mk_place 5 => 0
  | mk_place 6 => 0
  | mk_place 7 => 0
  | _ => 0
  end.

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

Definition ex_chronos :
  trans_type -> option chrono_type :=
  fun trans => 
    match trans with
    | mk_trans 3  =>  Some int_3_5
    | mk_trans 5  =>  Some int_2_256
    | _ => None
    end.

Print prior_type.
Definition ex_prior : prior_type :=
  (* se restreindre aux conflits structurels ! *)
  mk_prior
    [
      [mk_trans 1 ; mk_trans 2 ; mk_trans 5] ;
      [mk_trans 3] ;
      [mk_trans 4] ;
      [mk_trans 6]
    ].
 
    
Print pre. Print weight_type. Print STPN.
Definition ex_stpn := mk_STPN
                        (mk_SPN
                           ex_places
                           ex_transs
                         (*  ex_nodup_places'
                           ex_nodup_transs' *)
                           
                           ex_pre
                           ex_post
                           ex_test
                           ex_inhib                 
                      
                           ex_marking
                           ex_prior
                        )
                        ex_chronos.

Check ex_stpn. 
Search STPN.
Check stpn_cycle.
Check stpn_debug2.
Check stpn_animate.

Compute
  (
    stpn_debug2
      (        snd (stpn_cycle  

        (snd (stpn_cycle 
                (snd (stpn_cycle   
                        (snd (stpn_cycle      
                                ex_stpn)
                                    
  )))))))).

(*
Lemma stpn_ok : stpn_debug2
                  (snd (stpn_cycle  
                          (snd (stpn_cycle 
                                  (snd (stpn_cycle   
                                          (snd (stpn_cycle      
                                                  ex_stpn)
                  ))))))) =
.*)





Compute (stpn_animate
           ex_stpn
           11).  (* 12 markings but the last one is dub. It works. *)

Lemma ex_stpn_animate : (stpn_animate
                           ex_stpn
                           11) =
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
       ([[mk_trans 6]; []; []; []],
       [(mk_place 1, 1); (mk_place 2, 0); (mk_place 3, 0);
       (mk_place 4, 0); (mk_place 5, 0); (mk_place 6, 0);
       (mk_place 7, 0)],
       [(mk_trans 1, None); (mk_trans 2, None);
       (mk_trans 3, Some (3, 0, 5)); (mk_trans 4, None);
       (mk_trans 5, Some (2, 0, 256)); (mk_trans 6, None)]);
       ([[]; []; []; [mk_trans 1]],
       [(mk_place 1, 0); (mk_place 2, 1); (mk_place 3, 2);
       (mk_place 4, 1); (mk_place 5, 0); (mk_place 6, 0);
       (mk_place 7, 0)],
       [(mk_trans 1, None); (mk_trans 2, None);
       (mk_trans 3, Some (3, 0, 5)); (mk_trans 4, None);
       (mk_trans 5, Some (2, 0, 256)); (mk_trans 6, None)]);
       ([], [], [])].
Proof. compute. reflexivity. Qed.

       
Compute (chronos
           (snd (stpn_cycle
                   (snd (stpn_cycle
                           (snd (stpn_cycle
                                   (snd (stpn_cycle  
                                           ex_stpn))))))))). 

Compute
  (
    list_enabled_stpn
(*      (snd (stpn_cycle *) 
              ex_stpn
  ).

Compute (marking
           (spn
              ex_stpn)). (* initial marking *)
Check marking2list.
Compute (marking2list
           (marking (spn
                       (snd (stpn_cycle  
                               ex_stpn))))
           (places (spn
                      (snd (stpn_cycle  
                              ex_stpn))))).
