Require Export SPN.


(** * example 1 *)


Print NoDup. Print nodup. Print NoDup_nodup. (* opaque proof ? *)
(* 3 places *)
Definition ex_places : (list place_type) :=
  nodup
    places_eq_dec
    [ mk_place 0 ;
      mk_place 1 ;
      mk_place 2 ;
      mk_place 3 ;
      mk_place 4 ;
      mk_place 5 ; (* 6 is missing *)
      mk_place 7 ; 
      mk_place 8 ;
      mk_place 9 ;
      mk_place 10 ;
      mk_place 11 ;
      mk_place 12 ].
Definition ex_nodup_places : NoDup ex_places :=
  NoDup_nodup
    places_eq_dec
    ex_places. 

(* 3 transitions *)
Definition ex_transs : (list trans_type) :=
  [ mk_trans 0 ;
    mk_trans 1 ;
    mk_trans 2 ;
    mk_trans 3 ;
    mk_trans 4 ;
    mk_trans 5 ;
    mk_trans 6 ;  (* 7 is missing *)
    mk_trans 8 ;
    mk_trans 9 ;  (* 10, 11 are missing *)
    mk_trans 12 ;
    mk_trans 13 ;
    mk_trans 14 ; (* 15 is missing *)
    mk_trans 16 ].
Definition ex_nodup_transs : NoDup ex_transs :=
  NoDup_nodup
    transs_eq_dec
    ex_transs. 

(**********************************************)
Print nat_star. Print weight_type.
Lemma one_positive : 1 > 0. Proof. omega. Qed.
Lemma two_positive : 2 > 0. Proof. omega. Qed.
(* one lemma for each arc weight ... *)

(* many arcs PT (place transition)  "incoming" *) 
Definition ex_pre (t : trans_type) (p : place_type)
  : option nat_star :=
  (* transitions 7, 10, 11, 15  missing *)
  (* place 6 missing *)
  match (t,p) with
  (* trans 0 *)
  | (mk_trans 0, mk_place 0) => Some (mk_nat_star
                                        1
                                        one_positive)               
  | (mk_trans 0, mk_place 7) => Some (mk_nat_star
                                        1
                                        one_positive)               
  | (mk_trans 0, mk_place 12) => Some (mk_nat_star
                                        1
                                        one_positive)
  (* trans 1 *)
  | (mk_trans 1, mk_place 1) => Some (mk_nat_star
                                        1
                                        one_positive)
  (* trans 2 *)
  | (mk_trans 2, mk_place 2) => Some (mk_nat_star
                                        1
                                        one_positive)
  (* trans 3 *)
  | (mk_trans 3, mk_place 3) => Some (mk_nat_star
                                        1
                                        one_positive)
  (* trans 4 *)
  | (mk_trans 4, mk_place 4) => Some (mk_nat_star
                                        1
                                        one_positive)
  (* trans 5 *)
  | (mk_trans 5, mk_place 5) => Some (mk_nat_star
                                        1
                                        one_positive)
  (* trans 6 *)
  | (mk_trans 6, mk_place 8) => Some (mk_nat_star
                                        1
                                        one_positive)
  | (mk_trans 6, mk_place 9) => Some (mk_nat_star
                                        1
                                        one_positive)
  (* trans 8 *)
  | (mk_trans 8, mk_place 10) => Some (mk_nat_star
                                        2
                                        two_positive)
  (* trans 9 *)
  | (mk_trans 9, mk_place 11) => Some (mk_nat_star
                                        1
                                        one_positive)
  (* trans 12 *)
  | (mk_trans 12, mk_place 1) => Some (mk_nat_star
                                        1
                                        one_positive)
  (* trans 13 *)
  | (mk_trans 13, mk_place 11) => Some (mk_nat_star
                                        1
                                        one_positive)
  (* trans 14 *)
  | (mk_trans 14, mk_place 11) => Some (mk_nat_star
                                        1
                                        one_positive)
  (* trans 16 *)
  | (mk_trans 16, mk_place 3) => Some (mk_nat_star
                                        1
                                        one_positive)
  | (mk_trans 16, mk_place 10) => Some (mk_nat_star
                                        1
                                        one_positive)
  | _ => None
  end.

(* many  arcs TP       "outcoming" *)
Definition ex_post (t : trans_type) (p : place_type)
  : option nat_star :=
  (* transitions 7, 10, 11, 15  missing *)
  (* place 6 missing *)
  match (t, p) with
  (* trans 0 *)
  | (mk_trans 0, mk_place 4) => Some (mk_nat_star
                                        1
                                        one_positive)               
  | (mk_trans 0, mk_place 5) => Some (mk_nat_star
                                        1
                                        one_positive)               
  | (mk_trans 0, mk_place 12) => Some (mk_nat_star
                                        1
                                        one_positive)
  (* trans 1 *)
  | (mk_trans 1, mk_place 2) => Some (mk_nat_star
                                        1
                                        one_positive)
  (* trans 2 *)
  | (mk_trans 2, mk_place 3) => Some (mk_nat_star
                                        1
                                        one_positive)
  (* trans 3 *)
  | (mk_trans 3, mk_place 1) => Some (mk_nat_star
                                        1
                                        one_positive)
  (* trans 4 *)
  | (mk_trans 4, mk_place 8) => Some (mk_nat_star
                                        1
                                        one_positive)
  (* trans 5 *)
  | (mk_trans 5, mk_place 9) => Some (mk_nat_star
                                        1
                                        one_positive)
  (* trans 6 *)
  | (mk_trans 6, mk_place 7) => Some (mk_nat_star
                                        1
                                        one_positive)
  | (mk_trans 6, mk_place 10) => Some (mk_nat_star
                                        1
                                        one_positive)
  (* trans 8 *)
  | (mk_trans 8, mk_place 11) => Some (mk_nat_star
                                        1
                                        one_positive)
  (* trans 9 *)
  | (mk_trans 9, mk_place 0) => Some (mk_nat_star
                                        2
                                        two_positive)
  (* trans 12 *)
  | (mk_trans 12, mk_place 2) => Some (mk_nat_star
                                        1
                                        one_positive)
  (* trans 13 *)
  | (mk_trans 13, mk_place 0) => Some (mk_nat_star
                                         2
                                         two_positive)
  (* trans 14 *)
  | (mk_trans 14, mk_place 0) => Some (mk_nat_star
                                         2
                                         two_positive)
  (* trans 16 *)
  | (mk_trans 16, mk_place 3) => Some (mk_nat_star
                                        1
                                        one_positive)
  | (mk_trans 16, mk_place 10) => Some (mk_nat_star
                                        1
                                        one_positive)
  | _ => None
  end.

(*************************************)
(*** tokens of the initial marking ***)
Definition ex_marking (p : place_type) :=
  match p with
  | mk_place 0 => 2
  | mk_place 1 => 1
  | mk_place 7 => 1
  | mk_place 12 => 1
  | _ => 0
  end. Print ex_marking. Check marking_type.
(* ? reductions, simplifications ? *)

Print SPN.
Definition ex_test (t : trans_type) (p : place_type) :=
  (* transitions 7, 10, 11, 15  missing *)
  (* place 6 missing *)
  match (t, p) with
  (* trans 5 *)
  | (mk_trans 5, mk_place 2) => Some (mk_nat_star
                                        1
                                        one_positive)               
  | (mk_trans 5, mk_place 12) => Some (mk_nat_star
                                        1
                                        one_positive)
  | _ => None
  end.

(* many  arc of type "inhibitor"  *)
Definition ex_inhib (t : trans_type) (p : place_type) :=
  (* transitions 7, 10, 11, 15  missing *)
  (* place 6 missing *)
  match (t, p) with
  (* trans 2 *)
  | (mk_trans 2, mk_place 5) => Some (mk_nat_star
                                        1
                                        one_positive)               
  (* trans 4 *)
  | (mk_trans 4, mk_place 11) => Some (mk_nat_star
                                         1
                                         one_positive)               
  | _ => None
  end.

(*
Definition ex_prior1 (t1 t2 : trans_type) : bool :=
  (* transitions squared  ---> lot's of match branches ... *)
  match (t1 , t2) with
  | (mk_trans 0, mk_trans 0) => false
  | (mk_trans 0, mk_trans 1) => true
  | (mk_trans 0, mk_trans 2) => true
  | (mk_trans 1, mk_trans 0) => false
  | (mk_trans 1, mk_trans 1) => false
  | (mk_trans 1, mk_trans 2) => true
  | (mk_trans 2, mk_trans 0) => false
  | (mk_trans 2, mk_trans 1) => false
  | (mk_trans 2, mk_trans 2) => false
  | (_,_) => false  (* False or True     who care ? -> option bool?*) 
  end.    *)

Print prior_type.
Definition ex_prior_aux :=
  [
    [mk_trans 1 ; mk_trans 12] ;
    [mk_trans 0 ; mk_trans 2 ; mk_trans 5] ;
    [mk_trans 3 ; mk_trans 8 ; mk_trans 16] ;
    [mk_trans 4 ; mk_trans 9 ; mk_trans 13 ; mk_trans 14] ;
    [mk_trans 6]
  ].
Print ex_prior_aux.
Definition ex_prior :=
  mk_prior
    ex_prior_aux.    
    
Print pre. Print weight_type.
Definition ex_spn1 := mk_SPN
                      ex_places
                      ex_transs
                     (* ex_nodup_places
                      ex_nodup_transs *)
                      
                      ex_pre
                      ex_post
                      ex_test
                      ex_inhib                 
                      
                      ex_marking
                      ex_prior.

Compute (marking ex_spn1). (* initial marking *)
(* functions / lists *)


Compute (spn_debug2
                      (*  snd (spn_fired
               (snd (spn_fired  *) 
                      ex_spn1).

Lemma ex_spn1_debugpre : spn_debug2
                      (*  snd (spn_fired
               (snd (spn_fired  *) 
                      ex_spn1 =
     ([[]; []; []; [mk_trans 0]; [mk_trans 1]],
      [(mk_place 0, 1); (mk_place 1, 0); (mk_place 2, 0);
       (mk_place 3, 0); (mk_place 4, 0); (mk_place 5, 0);
       (mk_place 7, 0); (mk_place 8, 0); (mk_place 9, 0);
       (mk_place 10, 0); (mk_place 11, 0); 
       (mk_place 12, 0)]).
Proof. compute. reflexivity. Qed.


Search SPN. (* spn_fired    spn_debug_pre  spn_animate  *)
Compute (spn_animate
           ex_spn1
           10).  (* 11 markings *)

Lemma ex_spn1_animate : (spn_animate
                           ex_spn1
                           10) =
     [([[]; []; []; [mk_trans 0]; [mk_trans 1]],
       [(mk_place 0, 1); (mk_place 1, 0); 
        (mk_place 2, 1); (mk_place 3, 0); (mk_place 4, 1);
        (mk_place 5, 1); (mk_place 7, 0); (mk_place 8, 0);
        (mk_place 9, 0); (mk_place 10, 0); 
        (mk_place 11, 0); (mk_place 12, 1)]);
       ([[]; [mk_trans 4]; []; [mk_trans 5]; []],
       [(mk_place 0, 1); (mk_place 1, 0); (mk_place 2, 1);
       (mk_place 3, 0); (mk_place 4, 0); (mk_place 5, 0);
       (mk_place 7, 0); (mk_place 8, 1); (mk_place 9, 1);
       (mk_place 10, 0); (mk_place 11, 0); 
       (mk_place 12, 1)]);
       ([[mk_trans 6]; []; []; [mk_trans 2]; []],
       [(mk_place 0, 1); (mk_place 1, 0); (mk_place 2, 0);
       (mk_place 3, 1); (mk_place 4, 0); (mk_place 5, 0);
       (mk_place 7, 1); (mk_place 8, 0); (mk_place 9, 0);
       (mk_place 10, 1); (mk_place 11, 0); 
       (mk_place 12, 1)]);
       ([[]; []; [mk_trans 3]; [mk_trans 0]; []],
       [(mk_place 0, 0); (mk_place 1, 1); (mk_place 2, 0);
       (mk_place 3, 0); (mk_place 4, 1); (mk_place 5, 1);
       (mk_place 7, 0); (mk_place 8, 0); (mk_place 9, 0);
       (mk_place 10, 1); (mk_place 11, 0); 
       (mk_place 12, 1)]);
       ([[]; [mk_trans 4]; []; []; [mk_trans 1]],
       [(mk_place 0, 0); (mk_place 1, 0); (mk_place 2, 1);
       (mk_place 3, 0); (mk_place 4, 0); (mk_place 5, 1);
       (mk_place 7, 0); (mk_place 8, 1); (mk_place 9, 0);
       (mk_place 10, 1); (mk_place 11, 0); 
       (mk_place 12, 1)]);
       ([[]; []; []; [mk_trans 5]; []],
       [(mk_place 0, 0); (mk_place 1, 0); (mk_place 2, 1);
       (mk_place 3, 0); (mk_place 4, 0); (mk_place 5, 0);
       (mk_place 7, 0); (mk_place 8, 1); (mk_place 9, 1);
       (mk_place 10, 1); (mk_place 11, 0); 
       (mk_place 12, 1)]);
       ([[mk_trans 6]; []; []; [mk_trans 2]; []],
       [(mk_place 0, 0); (mk_place 1, 0); (mk_place 2, 0);
       (mk_place 3, 1); (mk_place 4, 0); (mk_place 5, 0);
       (mk_place 7, 1); (mk_place 8, 0); (mk_place 9, 0);
       (mk_place 10, 2); (mk_place 11, 0); 
       (mk_place 12, 1)]);
       ([[]; []; [mk_trans 3; mk_trans 8]; []; []],
       [(mk_place 0, 0); (mk_place 1, 1); (mk_place 2, 0);
       (mk_place 3, 0); (mk_place 4, 0); (mk_place 5, 0);
       (mk_place 7, 1); (mk_place 8, 0); (mk_place 9, 0);
       (mk_place 10, 0); (mk_place 11, 1); 
       (mk_place 12, 1)]);
       ([[]; [mk_trans 9]; []; []; [mk_trans 1]],
       [(mk_place 0, 2); (mk_place 1, 0); (mk_place 2, 1);
       (mk_place 3, 0); (mk_place 4, 0); (mk_place 5, 0);
       (mk_place 7, 1); (mk_place 8, 0); (mk_place 9, 0);
       (mk_place 10, 0); (mk_place 11, 0); 
       (mk_place 12, 1)]);
       ([[]; []; []; [mk_trans 0; mk_trans 2]; []],
       [(mk_place 0, 1); (mk_place 1, 0); (mk_place 2, 0);
       (mk_place 3, 1); (mk_place 4, 1); (mk_place 5, 1);
       (mk_place 7, 0); (mk_place 8, 0); (mk_place 9, 0);
       (mk_place 10, 0); (mk_place 11, 0); 
       (mk_place 12, 1)]); ([], [])].
Proof. compute. reflexivity. Qed.



(** **  Second  example (permutation des sous-listes)  *)

Definition ex_prior_aux2 :=
  [
    [mk_trans 1 ; mk_trans 12] ;
    [mk_trans 2 ; mk_trans 0 ; mk_trans 5] ;
    [mk_trans 16 ; mk_trans 8 ; mk_trans 3] ;
    [mk_trans 9 ; mk_trans 4 ; mk_trans 14 ; mk_trans 13] ;
    [mk_trans 6]
  ].
Definition ex_prior2 :=
  mk_prior
    ex_prior_aux2.    
Definition ex_spn2 := mk_SPN
                        ex_places
                        ex_transs
                      (*  ex_nodup_places
                        ex_nodup_transs *)
                        
                        ex_pre
                        ex_post
                        ex_test
                        ex_inhib                 
                        
                        ex_marking
                        ex_prior2.
Compute
  (
    spn_debug2
  (*    (
        snd (spn_fired
               (snd (spn_fired  *)
                             ex_spn2)
      .

Compute (spn_animate
           ex_spn2
           10).  (* 11 markings *)


(**  **  SPN numero 3  (apres permuation des sous-listes)  *)
Definition ex_prior_aux3 :=
  [
    [mk_trans 12 ; mk_trans 1] ;
    [mk_trans 0 ; mk_trans 2 ; mk_trans 5] ;
    [mk_trans 16 ; mk_trans 3 ; mk_trans 8] ;
    [mk_trans 9 ; mk_trans 14 ; mk_trans 4 ; mk_trans 13] ;
    [mk_trans 6]
  ].
Definition ex_prior3 :=
  mk_prior
    ex_prior_aux3.    
Definition ex_spn3 := mk_SPN
                        ex_places
                        ex_transs
                      (*  ex_nodup_places
                        ex_nodup_transs  *)
                        
                        ex_pre
                        ex_post
                        ex_test
                        ex_inhib                 
                        
                        ex_marking
                        ex_prior3.

Compute
  (
    spn_debug2
      (*     (
        snd (spn_fired 
          (snd (spn_fired *)
      ex_spn3)
.

Compute (spn_animate
           ex_spn3
           10).  (* 11 markings *)


Search SPN. Print SPN.


(** *  example 2 *)

(* 7 places *)
Definition ex2_places : (list place_type) :=
  [ mk_place 1 ;
    mk_place 2 ;
    mk_place 3 ;
    mk_place 4 ;
    mk_place 5 ;
    mk_place 6 ;
    mk_place 7 ].
Definition ex2_nodup_places : NoDup ex2_places :=
  NoDup_nodup
    places_eq_dec
    ex2_places. 

(* 6 transitions *)
Definition ex2_transs : (list trans_type) :=
  [ mk_trans 1 ;
    mk_trans 2 ;
    mk_trans 3 ;
    mk_trans 4 ;
    mk_trans 5 ;
    mk_trans 6 ].
Definition ex2_nodup_transs : NoDup ex2_transs :=
  NoDup_nodup
    transs_eq_dec
    ex2_transs.

(* one lemma for each arc weight ...  already done*)

(* Require Export spn_examples. (* surtout pas ! *) *)

(* one lemma for each new weight ... *)

(* 7 arcs PT (place transition)  "incoming" *) 
Definition ex2_pre (t : trans_type) (p : place_type)
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

Definition ex2_test (t : trans_type) (p : place_type) :=
  (* 1 arc of type "test" *)
  match (t, p) with
  | (mk_trans 2, mk_place 2) => Some (mk_nat_star
                                        1
                                        one_positive)               
  | _ => None
  end.

Definition ex2_inhib (t : trans_type) (p : place_type) :=
  (* 1 arc of type "inhibitor"  *)
  match (t, p) with
  | (mk_trans 1, mk_place 2) => Some (mk_nat_star
                                        1
                                        one_positive)               
  | _ => None
  end.

(* 7 arcs TP      "outcoming"  *)
Definition ex2_post (t : trans_type) (p : place_type)
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
Definition ex2_marking (p : place_type) :=
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

Definition ex2_prior : prior_type :=
  (* se restreindre aux conflits structurels ! *)
  mk_prior
    [
      [mk_trans 1 ; mk_trans 2 ; mk_trans 5] ;
      [mk_trans 3] ;
      [mk_trans 4] ;
      [mk_trans 6]
    ].
 
    
Print pre. Print weight_type. 
Definition ex2_spn := mk_SPN
                        ex2_places
                        ex2_transs
                        (*  ex2_nodup_places'
                           ex2_nodup_transs' *)
                        
                        ex2_pre
                        ex2_post
                        ex2_test
                        ex2_inhib                 
                        
                        ex2_marking
                        ex2_prior.



Compute (spn_animate
           ex2_spn
           10).  (* 11 markings *)

      
Lemma ex2_spn_animate : (spn_animate
                           ex2_spn
                           10) =
      [([[]; []; []; [mk_trans 1]],
        [(mk_place 1, 0); (mk_place 2, 1); 
        (mk_place 3, 2); (mk_place 4, 1); (mk_place 5, 0);
        (mk_place 6, 0); (mk_place 7, 0)]);
       ([[]; []; [mk_trans 3]; []],
       [(mk_place 1, 0); (mk_place 2, 1); (mk_place 3, 0);
       (mk_place 4, 0); (mk_place 5, 0); (mk_place 6, 0);
       (mk_place 7, 1)]);
       ([[mk_trans 6]; []; []; []],
       [(mk_place 1, 1); (mk_place 2, 1); (mk_place 3, 0);
       (mk_place 4, 0); (mk_place 5, 0); (mk_place 6, 0);
       (mk_place 7, 0)]);
       ([[]; []; []; [mk_trans 2]],
       [(mk_place 1, 0); (mk_place 2, 1); (mk_place 3, 0);
       (mk_place 4, 0); (mk_place 5, 1); (mk_place 6, 0);
       (mk_place 7, 0)]);
       ([[]; [mk_trans 4]; []; []],
       [(mk_place 1, 0); (mk_place 2, 1); (mk_place 3, 0);
       (mk_place 4, 0); (mk_place 5, 0); (mk_place 6, 1);
       (mk_place 7, 0)]);
       ([[]; []; []; [mk_trans 5]],
       [(mk_place 1, 0); (mk_place 2, 0); (mk_place 3, 0);
       (mk_place 4, 0); (mk_place 5, 0); (mk_place 6, 0);
       (mk_place 7, 1)]);
       ([[mk_trans 6]; []; []; []],
       [(mk_place 1, 1); (mk_place 2, 0); (mk_place 3, 0);
       (mk_place 4, 0); (mk_place 5, 0); (mk_place 6, 0);
       (mk_place 7, 0)]);
       ([[]; []; []; [mk_trans 1]],
       [(mk_place 1, 0); (mk_place 2, 1); (mk_place 3, 2);
       (mk_place 4, 1); (mk_place 5, 0); (mk_place 6, 0);
       (mk_place 7, 0)]);
       ([[]; []; [mk_trans 3]; []],
       [(mk_place 1, 0); (mk_place 2, 1); (mk_place 3, 0);
       (mk_place 4, 0); (mk_place 5, 0); (mk_place 6, 0);
       (mk_place 7, 1)]);
       ([[mk_trans 6]; []; []; []],
       [(mk_place 1, 1); (mk_place 2, 1); (mk_place 3, 0);
       (mk_place 4, 0); (mk_place 5, 0); (mk_place 6, 0);
       (mk_place 7, 0)]); ([], [])].
Proof. compute. reflexivity. Qed.