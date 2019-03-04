Require Export Hilecop.SPN Hilecop.SPNAnimator.
                               
(*! ================================================== !*) 
(*!                  FIRST SPN EXAMPLE                 !*)
(*! ================================================== !*)

(* List of places *)

Definition ex_places : (list place_type) := [ 0; 1; 2; 3; 4; 5; 7; 8; 9; 10; 11; 12 ].

(* Initial marking *)

Definition ex_marking :=
  [ (0, 2); (1, 1); (2, 0); (3, 0); (4, 0); (5, 0);
      (7, 1); (8, 0); (9, 0); (10, 0); (11, 0); (12, 1) ].

(* List of transitions *)
Definition ex_transs : (list trans_type) :=
  [ 0; 1; 2; 3; 4; 5; 6; 8; 9; 12; 13; 14; 16 ].

(* List of neighbour places for all transitions of the example. *)

Definition ex_lneighbours : list (trans_type * neighbours_type) :=
  [
    (0, (mk_neighbours [0; 7; 12] [] [] [4; 5; 12]));
    (1, (mk_neighbours [1] [] [] [2]));
    (2, (mk_neighbours [2] [] [5] [3]));
    (3, (mk_neighbours [3] [] [] [1]));
    (4, (mk_neighbours [4] [] [11] [8]));
    (5, (mk_neighbours [5] [2; 12] [] [9]));
    (6, (mk_neighbours [8; 9] [] [] [7; 10]));
    (8, (mk_neighbours [10] [] [] [11]));
    (9, (mk_neighbours [11] [] [] [0]));
    (12, (mk_neighbours [1] [] [] [2]));
    (13, (mk_neighbours [11] [] [] [0]));
    (14, (mk_neighbours [11] [] [] [0]));
    (16, (mk_neighbours [3; 10] [] [] [3; 10]))
  ].

(* Incoming arcs, from place to transition. *)

Definition ex_pre (t : trans_type) (p : place_type) : nat :=
  match (t, p) with
  (* trans 0 *)
  | (0, 0) => 1                
  | (0, 7) => 1               
  | (0, 12) => 1
  (* trans 1 *)
  | (1, 1) => 1
  (* trans 2 *)
  | (2, 2) => 1
  (* trans 3 *)
  | (3, 3) => 1
  (* trans 4 *)
  | (4, 4) => 1
  (* trans 5 *)
  | (5, 5) => 1
  (* trans 6 *)
  | (6, 8) => 1
  | (6, 9) => 1
  (* trans 8 *)
  | (8, 10) => 2
  (* trans 9 *)
  | (9, 11) => 1
  (* trans 12 *)
  | (12, 1) => 1
  (* trans 13 *)
  | (13, 11) => 1
  (* trans 14 *)
  | (14, 11) => 1
  (* trans 16 *)
  | (16, 3) => 1
  | (16, 10) => 1
  | _ => 0
  end.

(* Outcoming arcs, from transition to place. *)

Definition ex_post (t : trans_type) (p : place_type) : nat :=
  match (t, p) with
  (* trans 0 *)
  | (0, 4) => 1               
  | (0, 5) => 1               
  | (0, 12) => 1
  (* trans 1 *)
  | (1, 2) => 1
  (* trans 2 *)
  | (2, 3) => 1
  (* trans 3 *)
  | (3, 1) => 1
  (* trans 4 *)
  | (4, 8) => 1
  (* trans 5 *)
  | (5, 9) => 1
  (* trans 6 *)
  | (6, 7) => 1
  | (6, 10) => 1
  (* trans 8 *)
  | (8, 11) => 1
  (* trans 9 *)
  | (9, 0) => 2
  (* trans 12 *)
  | (12, 2) => 1
  (* trans 13 *)
  | (13, 0) => 2
  (* trans 14 *)
  | (14, 0) => 2
  (* trans 16 *)
  | (16, 3) => 1
  | (16, 10) => 1
  | _ => 0
  end.

(* Test arcs, from place to transition. *)

Definition ex_test (t : trans_type) (p : place_type) :=
  match (t, p) with
  (* trans 5 *)
  | (5, 2) => 1               
  | (5, 12) => 1
  | _ => 0
  end.

(* Inhibitor arcs, from place to transition. *)

Definition ex_inhib (t : trans_type) (p : place_type) :=
  match (t, p) with
  (* trans 2 *)
  | (2, 5) => 1               
  (* trans 4 *)
  | (4, 11) => 1               
  | _ => 0
  end.

Definition ex_priority_groups := [ [1 ; 12];
                                     [0 ; 2 ; 5];
                                     [3 ; 8 ; 16];
                                     [4 ; 9 ; 13 ; 14];
                                     [6] ].
                           
Definition spn1 := mk_Spn
                     ex_places
                     ex_transs
                     ex_pre
                     ex_post
                     ex_test
                     ex_inhib                 
                     ex_marking
                     ex_priority_groups
                     ex_lneighbours.

(*! ================================ !*)
(*! PROVING ISWELLSTRUCTUREDSPN SPN1 !*)
(*! ================================ !*)

(*  
 * Proving that spn1 is well-structured, and thus spn_animate
 * executed with spn1 passed as parameter will never fail.
 *)
Lemma nodup_places_spn1 : NoDupPlaces spn1.
Proof.
  unfold NoDupPlaces.
  decide_nodup.
Qed.

Lemma nodup_transs_spn1 : NoDupTranss spn1.
Proof.
  unfold NoDupTranss.
  decide_nodup.
Qed.

Lemma no_unknown_in_priority_groups_spn1 :
  NoUnknownInPriorityGroups spn1.
Proof.
  unfold NoUnknownInPriorityGroups.
  simpl.
  unfold ex_transs.
  apply NoDup_Permutation_bis.
  decide_nodup.
  decide_nodup.
  simpl; auto.
  compute.
  intros.
  decompose [or] H; repeat (auto || right).
Qed.

Lemma no_intersect_in_priority_groups_spn1 :
  NoIntersectInPriorityGroups spn1.
Proof.
  unfold NoIntersectInPriorityGroups.
  simpl.
  decide_nodup.
Qed.

Lemma nodup_lneighbours_spn1 :
  NoDupLneighbours spn1.
Proof.
  unfold NoDupLneighbours.
  decide_nodup.
Qed.

Lemma no_isolated_place_spn1 :
  NoIsolatedPlace spn1.
Proof.
  unfold NoIsolatedPlace.
  decide_incl.
Qed.

Lemma no_unknown_place_in_neighbours_spn1 :
  NoUnknownPlaceInNeighbours spn1.
Proof.
  unfold NoUnknownPlaceInNeighbours.
  decide_incl.
Qed.

Lemma no_unknown_trans_in_lneighbours_spn1 :
  NoUnknownTransInLNeighbours spn1.
Proof.
  unfold NoUnknownTransInLNeighbours.
  simpl.
  unfold ex_transs.
  auto.
Qed.
  
Lemma no_isolated_trans_spn1 :
  NoIsolatedTrans spn1.
Proof.
  unfold NoIsolatedTrans;
  intros;
  simpl in H;
  decompose [or] H;
  (match goal with
   | [ H : (_, _) = (_, _) |- ?l <> _ ] =>
     injection H;
     intros Heql Heqr;
     rewrite <- Heql;
     simpl;
     apply hd_error_some_nil with (a := hd 0 l);
     rewrite <- Heql;
     simpl;
     auto
   end
   || auto).
Qed.

Lemma no_unmarked_place_spn1 :
  NoUnmarkedPlace spn1.
Proof.
  unfold NoUnmarkedPlace; simpl; unfold ex_places; auto.
Qed.

Lemma is_well_structured_spn1 :
  IsWellDefinedSpn spn1.
Proof.
  unfold IsWellDefinedSpn.
  assert (H := (conj nodup_places_spn1
               (conj nodup_transs_spn1
               (conj no_unknown_in_priority_groups_spn1
               (conj no_intersect_in_priority_groups_spn1
               (conj nodup_lneighbours_spn1
               (conj no_isolated_place_spn1
               (conj no_unknown_place_in_neighbours_spn1
               (conj no_unknown_trans_in_lneighbours_spn1
               (conj no_isolated_trans_spn1 no_unmarked_place_spn1)))))))))).
  auto.
Qed.

(*! ========================== !*)
(*! === PERFORMANCE TESTS. === !*)
(*! ========================== !*)

(* Time Compute (spn_animate spn1 10000). *)
(* Time Compute (spn_animate spn1 1000). *)
(* Time Compute (spn_animate spn1 2000). *)
(* Time Compute (spn_animate spn1 4000). *)


(*! ================================================ !*)  
(*!                SECOND SPN EXAMPLE                !*)
(*! ================================================ !*)

(* List of places. *)

Definition ex2_places : (list place_type) := [ 1; 2; 3; 4; 5; 6; 7 ].

(* Initial marking. *)

Definition ex2_marking := [ (1, 1); (2, 0); (3, 0); (4, 0); (5, 0); (6, 0); (7, 0) ].

(* List of transitions. *)

Definition ex2_transs : (list trans_type) := [ 1; 2; 3; 4; 5; 6 ].

(* List of pairs (transition, neighbours) *)

Definition ex2_lneighbours :=
  [
    (1, mk_neighbours [1] [] [2] [2; 3; 4]);
    (2, mk_neighbours [1] [2] [] [5]);
    (3, mk_neighbours [3; 4] [] [] [7]);
    (4, mk_neighbours [5] [] [] [6]);
    (5, mk_neighbours [2; 6] [] [] [7]);
    (6, mk_neighbours [7] [] [] [1])
  ].

(* 7 arcs PT (place transition)  "incoming" *)

Definition ex2_pre (t : trans_type) (p : place_type) : nat :=
  match (t,p) with
  | (1, 1) => 1
  | (2, 1) => 1
  | (3, 3) => 2
  | (3, 4) => 1
  | (4, 5) => 1
  | (5, 2) => 1  
  | (5, 6) => 1
  | (6, 7) => 1
  | _ => 0
  end.

Definition ex2_test (t : trans_type) (p : place_type) :=
  match (t, p) with
  | (2, 2) => 1               
  | _ => 0
  end.

Definition ex2_inhib (t : trans_type) (p : place_type) :=
  match (t, p) with
  | (1, 2) => 1               
  | _ => 0
  end.

(* 7 arcs TP "outcoming" *)

Definition ex2_post (t : trans_type) (p : place_type) : nat :=
  match (t, p) with
  (* trans 1 *)
  | (1, 2) => 1               
  | (1, 3) => 2               
  | (1, 4) => 1
  (* trans 2 *)
  | (2, 5) => 1
  (* trans 3 *)
  | (3, 7) => 1
  (* trans 4 *)
  | (4, 6) => 1
  (* trans 5 *)
  | (5, 7) => 1
  (* trans 6 *)
  | (6, 1) => 1
  | _ => 0
  end.

Definition ex2_priority_groups := [ [1 ; 2 ; 5]; [3]; [4]; [6] ].
 
Definition spn2 := mk_Spn
                     ex2_places
                     ex2_transs
                     ex2_pre
                     ex2_post
                     ex2_test
                     ex2_inhib                 
                     ex2_marking
                     ex2_priority_groups
                     ex2_lneighbours.

(*! ========================== !*)
(*! === PERFORMANCE TESTS. === !*)
(*! ========================== !*)

(* Time Compute (spn_animate spn2 100 []). *)
(* Time Compute (spn_animate spn2 200 []). *)
(* Time Compute (spn_animate spn2 400 []). *)
(* Time Compute (spn_animate spn2 800 []). *)
(* Time Compute (spn_animate spn2 1000 []). *)
(* Time Compute (spn_animate spn2 2000 []). *)
(* Time Compute (spn_animate spn2 4000 []). *)
