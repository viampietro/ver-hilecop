Require Export SPN.
                               
(** * example 1 *)
Definition ex_places : (list place_type) := (* 6 is missing *)
  nodup places_eq_dec [ pl 0; pl 1; pl 2; pl 3; pl 4; pl 5; 
                        pl 7; pl 8; pl 9; pl 10; pl 11; pl 12 ].

Definition ex_nodup_places : NoDup ex_places :=
  NoDup_nodup places_eq_dec ex_places. 

(*************************************)
(*** tokens of the initial marking ***)
Definition ex_marking :=
  [ (0, 2); (1, 1); (2, 0); (3, 0); (4, 0); (5, 0);
    (7, 1); (8, 0); (9, 0); (10, 0); (11, 0); (12, 1) ].

(* 16 transitions *)
(* 7, 10, 11, 15 is missing *)
Definition ex_transs : (list trans_type) :=
  [ tr 0; tr 1; tr 2; tr 3; tr 4; tr 5; tr 6; tr 8; tr 9; tr 12; tr 13; tr 14; tr 16 ].

Definition ex_nodup_transs : NoDup ex_transs :=
  NoDup_nodup
    transs_eq_dec
    ex_transs. 

(**********************************************)
Lemma one_positive : 1 > 0. Proof. omega. Qed.
Lemma two_positive : 2 > 0. Proof. omega. Qed.
(* one lemma for each arc weight ... *)

(* List of neighbour places for all transitions of the example. *)
Definition ex_lneighbours : list neighbours_type :=
  [
    (mk_neighbours 0 [pl 0; pl 7; pl 12] [] [] [pl 4; pl 5; pl 12]);
    (mk_neighbours 1 [pl 1] [] [] [pl 2]);
    (mk_neighbours 2 [pl 2] [] [pl 5] [pl 3]);
    (mk_neighbours 3 [pl 3] [] [] [pl 1]);
    (mk_neighbours 4 [pl 4] [] [pl 11] [pl 8]);
    (mk_neighbours 5 [pl 5] [pl 2; pl 12] [] [pl 9]);
    (mk_neighbours 6 [pl 8; pl 9] [] [] [pl 7; pl 10]);
    (mk_neighbours 8 [pl 10] [] [] [pl 11]);
    (mk_neighbours 9 [pl 11] [] [] [pl 0]);
    (mk_neighbours 12 [pl 1] [] [] [pl 2]);
    (mk_neighbours 13 [pl 11] [] [] [pl 0]);
    (mk_neighbours 14 [pl 11] [] [] [pl 0]);
    (mk_neighbours 16 [pl 3; pl 10] [] [] [pl 3; pl 10])
  ].

(* many arcs PT (place transition)  "incoming" *) 
Definition ex_pre (t : trans_type) (p : place_type) : option nat_star :=
  (* transitions 7, 10, 11, 15  missing *)
  (* place 6 missing *)
  match (t, p) with
  (* trans 0 *)
  | (tr 0, pl 0) => Some (mk_nat_star 1 one_positive)               
  | (tr 0, pl 7) => Some (mk_nat_star 1 one_positive)               
  | (tr 0, pl 12) => Some (mk_nat_star 1 one_positive)
  (* trans 1 *)
  | (tr 1, pl 1) => Some (mk_nat_star 1 one_positive)
  (* trans 2 *)
  | (tr 2, pl 2) => Some (mk_nat_star 1 one_positive)
  (* trans 3 *)
  | (tr 3, pl 3) => Some (mk_nat_star 1 one_positive)
  (* trans 4 *)
  | (tr 4, pl 4) => Some (mk_nat_star 1 one_positive)
  (* trans 5 *)
  | (tr 5, pl 5) => Some (mk_nat_star 1 one_positive)
  (* trans 6 *)
  | (tr 6, pl 8) => Some (mk_nat_star 1 one_positive)
  | (tr 6, pl 9) => Some (mk_nat_star 1 one_positive)
  (* trans 8 *)
  | (tr 8, pl 10) => Some (mk_nat_star 2 two_positive)
  (* trans 9 *)
  | (tr 9, pl 11) => Some (mk_nat_star 1 one_positive)
  (* trans 12 *)
  | (tr 12, pl 1) => Some (mk_nat_star 1 one_positive)
  (* trans 13 *)
  | (tr 13, pl 11) => Some (mk_nat_star 1 one_positive)
  (* trans 14 *)
  | (tr 14, pl 11) => Some (mk_nat_star 1 one_positive)
  (* trans 16 *)
  | (tr 16, pl 3) => Some (mk_nat_star 1 one_positive)
  | (tr 16, pl 10) => Some (mk_nat_star 1 one_positive)
  | _ => None
  end.

(* many  arcs TP       "outcoming" *)
Definition ex_post (t : trans_type) (p : place_type) : option nat_star :=
  (* transitions 7, 10, 11, 15  missing *)
  (* place 6 missing *)
  match (t, p) with
  (* trans 0 *)
  | (tr 0, pl 4) => Some (mk_nat_star 1 one_positive)               
  | (tr 0, pl 5) => Some (mk_nat_star 1 one_positive)               
  | (tr 0, pl 12) => Some (mk_nat_star 1 one_positive)
  (* trans 1 *)
  | (tr 1, pl 2) => Some (mk_nat_star 1 one_positive)
  (* trans 2 *)
  | (tr 2, pl 3) => Some (mk_nat_star 1 one_positive)
  (* trans 3 *)
  | (tr 3, pl 1) => Some (mk_nat_star 1 one_positive)
  (* trans 4 *)
  | (tr 4, pl 8) => Some (mk_nat_star 1 one_positive)
  (* trans 5 *)
  | (tr 5, pl 9) => Some (mk_nat_star 1 one_positive)
  (* trans 6 *)
  | (tr 6, pl 7) => Some (mk_nat_star 1 one_positive)
  | (tr 6, pl 10) => Some (mk_nat_star 1 one_positive)
  (* trans 8 *)
  | (tr 8, pl 11) => Some (mk_nat_star 1 one_positive)
  (* trans 9 *)
  | (tr 9, pl 0) => Some (mk_nat_star 2 two_positive)
  (* trans 12 *)
  | (tr 12, pl 2) => Some (mk_nat_star 1 one_positive)
  (* trans 13 *)
  | (tr 13, pl 0) => Some (mk_nat_star 2 two_positive)
  (* trans 14 *)
  | (tr 14, pl 0) => Some (mk_nat_star 2 two_positive)
  (* trans 16 *)
  | (tr 16, pl 3) => Some (mk_nat_star 1 one_positive)
  | (tr 16, pl 10) => Some (mk_nat_star 1 one_positive)
  | _ => None
  end.

(* ? reductions, simplifications ? *)
Definition ex_test (t : trans_type) (p : place_type) :=
  (* transitions 7, 10, 11, 15  missing *)
  (* place 6 missing *)
  match (t, p) with
  (* trans 5 *)
  | (tr 5, pl 2) => Some (mk_nat_star 1 one_positive)               
  | (tr 5, pl 12) => Some (mk_nat_star 1 one_positive)
  | _ => None
  end.

(* many  arc of type "inhibitor"  *)
Definition ex_inhib (t : trans_type) (p : place_type) :=
  (* transitions 7, 10, 11, 15  missing *)
  (* place 6 missing *)
  match (t, p) with
  (* trans 2 *)
  | (tr 2, pl 5) => Some (mk_nat_star 1 one_positive)               
  (* trans 4 *)
  | (tr 4, pl 11) => Some (mk_nat_star 1 one_positive)               
  | _ => None
  end.

(*
Definition ex_prior1 (t1 t2 : trans_type) : bool :=
  (* transitions squared  ---> lot's of match branches ... *)
  match (t1 , t2) with
  | (tr 0, tr 0) => false
  | (tr 0, tr 1) => true
  | (tr 0, tr 2) => true
  | (tr 1, tr 0) => false
  | (tr 1, tr 1) => false
  | (tr 1, tr 2) => true
  | (tr 2, tr 0) => false
  | (tr 2, tr 1) => false
  | (tr 2, tr 2) => false
  | (_,_) => false  (* False or True     who care ? -> option bool?*) 
  end.    *)

Definition ex_prior := {| Lol := [
                                    [tr 1 ; tr 12];
                                    [tr 0 ; tr 2 ; tr 5];
                                    [tr 3 ; tr 8 ; tr 16];
                                    [tr 4 ; tr 9 ; tr 13 ; tr 14];
                                    [tr 6]
                                ]
                       |}.    

Definition ex_spn1 := mk_SPN
                        ex_places
                        ex_transs
                        ex_pre
                        ex_post
                        ex_test
                        ex_inhib                 
                        ex_marking
                        ex_prior
                        ex_lneighbours.

Lemma ex_spn1_animate : (spn_animate ex_spn1 10) =
                        [
                          ([[]; []; []; [tr 0]; [tr 1]],
                           [(0, 1); (1, 0); (2, 1); (3, 0); (4, 1); (5, 1); (7, 0); (8, 0); (9, 0); (10, 0); (11, 0); (12, 1)]);
                          ([[]; [tr 4]; []; [tr 5]; []],
                           [(0, 1); (1, 0); (2, 1); (3, 0); (4, 0); (5, 0); (7, 0); (8, 1); (9, 1); (10, 0); (11, 0); (12, 1)]);
                          ([[tr 6]; []; []; [tr 2]; []],
                           [(0, 1); (1, 0); (2, 0); (3, 1); (4, 0); (5, 0); (7, 1); (8, 0); (9, 0); (10, 1); (11, 0); (12, 1)]);
                          ([[]; []; [tr 3]; [tr 0]; []],
                           [(0, 0); (1, 1); (2, 0); (3, 0); (4, 1); (5, 1); (7, 0); (8, 0); (9, 0); (10, 1); (11, 0); (12, 1)]);
                          ([[]; [tr 4]; []; []; [tr 1]],
                           [(0, 0); (1, 0); (2, 1); (3, 0); (4, 0); (5, 1); (7, 0); (8, 1); (9, 0); (10, 1); (11, 0); (12, 1)]);
                          ([[]; []; []; [tr 5]; []],
                           [(0, 0); (1, 0); (2, 1); (3, 0); (4, 0); (5, 0); (7, 0); (8, 1); (9, 1); (10, 1); (11, 0); (12, 1)]);
                          ([[tr 6]; []; []; [tr 2]; []],
                           [(0, 0); (1, 0); (2, 0); (3, 1); (4, 0); (5, 0); (7, 1); (8, 0); (9, 0); (10, 2); (11, 0); (12, 1)]);
                          ([[]; []; [tr 3; tr 8]; []; []],
                           [(0, 0); (1, 1); (2, 0); (3, 0); (4, 0); (5, 0); (7, 1); (8, 0); (9, 0); (10, 0); (11, 1); (12, 1)]);
                          ([[]; [tr 9]; []; []; [tr 1]],
                           [(0, 2); (1, 0); (2, 1); (3, 0); (4, 0); (5, 0); (7, 1); (8, 0); (9, 0); (10, 0); (11, 0); (12, 1)]);
                          ([[]; []; []; [tr 0; tr 2]; []],
                           [(0, 1); (1, 0); (2, 0); (3, 1); (4, 1); (5, 1); (7, 0); (8, 0); (9, 0); (10, 0); (11, 0); (12, 1)]);
                          ([], [])
                        ].
Proof. compute. reflexivity. Qed.

(** **  Second  example (permutation des sous-listes)  *)

Definition ex_prior_aux2 :=
  [
    [tr 1 ; tr 12] ;
    [tr 2 ; tr 0 ; tr 5] ;
    [tr 16 ; tr 8 ; tr 3] ;
    [tr 9 ; tr 4 ; tr 14 ; tr 13] ;
    [tr 6]
  ].

Definition ex_prior2 :=
  mk_prior
    ex_prior_aux2.    

Definition ex_spn2 := mk_SPN
                        ex_places
                        ex_transs
                        ex_pre
                        ex_post
                        ex_test
                        ex_inhib                                         
                        ex_marking
                        ex_prior2
                        ex_lneighbours.

(**  **  SPN numero 3  (apres permuation des sous-listes)  *)
Definition ex_prior_aux3 :=
  [
    [tr 12 ; tr 1] ;
    [tr 0 ; tr 2 ; tr 5] ;
    [tr 16 ; tr 3 ; tr 8] ;
    [tr 9 ; tr 14 ; tr 4 ; tr 13] ;
    [tr 6]
  ].

Definition ex_prior3 :=
  mk_prior
    ex_prior_aux3.    

Definition ex_spn3 := mk_SPN
                        ex_places
                        ex_transs
                        ex_pre
                        ex_post
                        ex_test
                        ex_inhib                 
                        ex_marking
                        ex_prior3.

(*******************************************************)
(********************** EXAMPLE 2 **********************)
(*******************************************************)

(* 7 places *)
Definition ex2_places : (list place_type) :=
  [ pl 1; pl 2; pl 3; pl 4; pl 5; pl 6; pl 7 ].

Definition ex2_nodup_places : NoDup ex2_places :=
  NoDup_nodup places_eq_dec ex2_places. 

(* tokens *)
Definition ex2_marking :=
  [ (1, 1); (2, 0); (3, 0); (4, 0); (5, 0); (6, 0); (7, 0) ].

(* 6 transitions *)
Definition ex2_transs : (list trans_type) :=
  [ tr 1; tr 2; tr 3; tr 4; tr 5; tr 6 ].

Definition ex2_nodup_transs : NoDup ex2_transs :=
  NoDup_nodup transs_eq_dec ex2_transs.

Definition ex2_lneighbours :=
  [
    mk_neighbours 1 [pl 1] [] [pl 2] [pl 2; pl 3; pl 4];
    mk_neighbours 2 [pl 1] [pl 2] [] [pl 5];
    mk_neighbours 3 [pl 3; pl 4] [] [] [pl 7];
    mk_neighbours 4 [pl 5] [] [] [pl 6];
    mk_neighbours 5 [pl 2; pl 6] [] [] [pl 7];
    mk_neighbours 6 [pl 7] [] [] [pl 1]
  ].

(* 7 arcs PT (place transition)  "incoming" *) 
Definition ex2_pre (t : trans_type) (p : place_type) : option nat_star :=
  match (t,p) with
  | (tr 1, pl 1) => Some (mk_nat_star 1 one_positive)
  | (tr 2, pl 1) => Some (mk_nat_star 1 one_positive)
  | (tr 3, pl 3) => Some (mk_nat_star 2 two_positive)
  | (tr 3, pl 4) => Some (mk_nat_star 1 one_positive)
  | (tr 4, pl 5) => Some (mk_nat_star 1 one_positive)
  | (tr 5, pl 2) => Some (mk_nat_star 1 one_positive)  
  | (tr 5, pl 6) => Some (mk_nat_star 1 one_positive)
  | (tr 6, pl 7) => Some (mk_nat_star 1 one_positive)
  | _ => None
  end.

Definition ex2_test (t : trans_type) (p : place_type) :=
  (* 1 arc of type "test" *)
  match (t, p) with
  | (tr 2, pl 2) => Some (mk_nat_star 1 one_positive)               
  | _ => None
  end.

Definition ex2_inhib (t : trans_type) (p : place_type) :=
  (* 1 arc of type "inhibitor"  *)
  match (t, p) with
  | (tr 1, pl 2) => Some (mk_nat_star 1 one_positive)               
  | _ => None
  end.

(* 7 arcs TP "outcoming" *)
Definition ex2_post (t : trans_type) (p : place_type) : option nat_star :=
  match (t, p) with
  (* trans 1 *)
  | (tr 1, pl 2) => Some (mk_nat_star 1 one_positive)               
  | (tr 1, pl 3) => Some (mk_nat_star 2 two_positive)               
  | (tr 1, pl 4) => Some (mk_nat_star 1 one_positive)
  (* trans 2 *)
  | (tr 2, pl 5) => Some (mk_nat_star 1 one_positive)
  (* trans 3 *)
  | (tr 3, pl 7) => Some (mk_nat_star 1 one_positive)
  (* trans 4 *)
  | (tr 4, pl 6) => Some (mk_nat_star 1 one_positive)
  (* trans 5 *)
  | (tr 5, pl 7) => Some (mk_nat_star 1 one_positive)
  (* trans 6 *)
  | (tr 6, pl 1) => Some (mk_nat_star 1 one_positive)
  | _ => None
  end.

Definition ex2_prior : prior_type :=
  (* se restreindre aux conflits structurels ! *)
  mk_prior [[tr 1 ; tr 2 ; tr 5]; [tr 3]; [tr 4]; [tr 6]].
 
Definition ex2_spn := mk_SPN
                        ex2_places
                        ex2_transs
                        ex2_pre
                        ex2_post
                        ex2_test
                        ex2_inhib                 
                        ex2_marking
                        ex2_prior
                        ex2_lneighbours.
      
Lemma ex2_spn_animate : (spn_animate ex2_spn 10) =
       [([[]; []; []; [tr 1]],
         [(1, 0); (2, 1); (3, 2); (4, 1); (5, 0); (6, 0); (7, 0)]);
        ([[]; []; [tr 3]; []],
         [(1, 0); (2, 1); (3, 0); (4, 0); (5, 0); (6, 0); (7, 1)]);
        ([[tr 6]; []; []; []],
         [(1, 1); (2, 1); (3, 0); (4, 0); (5, 0); (6, 0); (7, 0)]);
        ([[]; []; []; [tr 2]],
         [(1, 0); (2, 1); (3, 0); (4, 0); (5, 1); (6, 0); (7, 0)]);
        ([[]; [tr 4]; []; []],
         [(1, 0); (2, 1); (3, 0); (4, 0); (5, 0); (6, 1); (7, 0)]);
        ([[]; []; []; [tr 5]],
         [(1, 0); (2, 0); (3, 0); (4, 0); (5, 0); (6, 0); (7, 1)]);
        ([[tr 6]; []; []; []],
         [(1, 1); (2, 0); (3, 0); (4, 0); (5, 0); (6, 0); (7, 0)]);
       ([[]; []; []; [tr 1]],
        [(1, 0); (2, 1); (3, 2); (4, 1); (5, 0); (6, 0); (7, 0)]);
       ([[]; []; [tr 3]; []],
        [(1, 0); (2, 1); (3, 0); (4, 0); (5, 0); (6, 0); (7, 1)]);
       ([[tr 6]; []; []; []],
        [(1, 1); (2, 1); (3, 0); (4, 0); (5, 0); (6, 0); (7, 0)]);
       ([], [])].
Proof. compute. reflexivity. Qed.
