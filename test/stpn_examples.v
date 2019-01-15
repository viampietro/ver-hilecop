Require Export STPN spn_examples.

(*=====================================================*)  
(*                  FIRST STPN EXAMPLE                 *)
(*=====================================================*)

Lemma pos1 : 1 > 0. omega. Qed.
Lemma pos2 : 2 > 0. omega. Qed.
Lemma pos3 : 3 > 0. omega. Qed.
Lemma pos4 : 4 > 0. omega. Qed.
Lemma le24 : 2 <= 4. omega. Qed.
Lemma le12 : 1 <= 2. omega. Qed. 
Lemma le23 : 2 <= 3. omega. Qed.

(* Defines some chronos. *)
Definition chr1 := {| cnt := 0;
                      min_t := {| int := 1; posi := pos1 |};
                      max_t := {| int := 2; posi := pos2 |};
                      max_is_infinite := false;
                      min_t_le_max_t := le12 |}.
Definition chr2 := {| cnt := 0;
                      min_t := {| int := 2; posi := pos2 |};
                      max_t := {| int := 3; posi := pos3 |};
                      max_is_infinite := false;
                      min_t_le_max_t := le23 |}.
Definition chr3 := {| cnt := 0;
                      min_t := {| int := 2; posi := pos2 |};
                      max_t := {| int := 3; posi := pos3 |};
                      max_is_infinite := true;
                      min_t_le_max_t := le23 |}.

(* List of (trans_type, option chrono_type). *)
Definition ex_chronos := [(0, None);
                            (1, Some chr1);
                            (2, Some chr2);
                            (3, Some chr3);
                            (4, None);
                            (5, None);
                            (6, None);
                            (8, None);
                            (9, None);
                            (12, None);
                            (13, None);
                            (14, None);
                            (16, None)
                         ].

(* Defines a STPN instance. *)
Definition stpn1 := mk_STPN ex_chronos spn1.

(*==== PERFORMANCE TESTS. ====*)

(* FORMER stpn_animate : 9 steps takes 19.843 secs! *)

(* ACTUAL stpn_animate : 9 steps takes 0.53 secs! *)
(* Time Eval compute in stpn_animate stpn1 9 []. *)
(* Time Eval compute in stpn_animate stpn1 50 []. *)
(* Time Eval compute in stpn_animate stpn1 100 []. *)
(* Time Eval compute in stpn_animate stpn1 500 []. *)
(* Time Eval compute in stpn_animate stpn1 1000 []. *)

