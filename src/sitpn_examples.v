Require Import SITPN stpn_examples.

(**********************************)
(********   example (1)   *********)
(**********************************)

Definition ex_eval_conds_cycle1 (t : trans_type) : option bool :=
  match t with
  | mk_trans 0  => Some true
  | mk_trans 2  => Some false
  | _ => None
  end.

Definition ex_eval_conds_cycle2 (t : trans_type) : option bool :=
  match t with
  | mk_trans 0  => Some true
  | mk_trans 2  => Some true
  | _ => None
  end.

Definition ex_eval_conds_cycle3 (t : trans_type) : option bool :=
  match t with
  | mk_trans 0  => Some true
  | mk_trans 2  => Some true
  | mk_trans 3  => Some false
  | _ => None
  end.

Definition ex_eval_conds_cycle4 (t : trans_type) : option bool :=
  match t with
  | mk_trans 0  => Some true
  | mk_trans 2  => Some true
  | mk_trans 3  => Some false
  | _ => None
  end.

Definition ex_eval_conds_cycle5 (t : trans_type) : option bool :=
  match t with
  | mk_trans 0  => Some true
  | mk_trans 2  => Some true
  | mk_trans 3  => Some false
  | _ => None
  end.

Definition ex_scenar := [ex_eval_conds_cycle1;
                           ex_eval_conds_cycle2;
                           ex_eval_conds_cycle3;
                           ex_eval_conds_cycle4;
                           ex_eval_conds_cycle5].

Definition ex_sitpn := mk_SITPN ex_stpn ex_scenar.

Time Eval compute in (sitpn_animate ex_sitpn 9).

Lemma ex_sitpn_animate : (sitpn_animate
                             ex_sitpn
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

Definition ex2_conds_cycle1 (t : trans_type) : option bool :=
  match t with
  | mk_trans 1  => Some true
  | mk_trans 2  => Some false
  | _ => None
  end.

Definition ex2_conds_cycle2 (t : trans_type) : option bool :=
  match t with
  | mk_trans 1  => Some true
  | mk_trans 6  => Some true
  | _ => None
  end.

Definition ex2_conds_cycle3 (t : trans_type) : option bool :=
  match t with
  | mk_trans 1  => Some true
  | mk_trans 2  => Some true
  | mk_trans 5  => Some false
  | _ => None
  end.

Definition ex2_conds_cycle4 (t : trans_type) : option bool :=
  match t with
  | mk_trans 1  => Some true
  | mk_trans 2  => Some true
  | mk_trans 3  => Some false
  | _ => None
  end.

Definition ex2_conds_cycle5 (t : trans_type) : option bool :=
  match t with
  | mk_trans 5  => Some true
  | mk_trans 2  => Some true
  | mk_trans 3  => Some false
  | _ => None
  end.

Definition ex2_scenar := [ex2_conds_cycle1; ex2_conds_cycle2; ex2_conds_cycle3;
                           ex2_conds_cycle4; ex2_conds_cycle5].

Definition ex2_sitpn := mk_SITPN ex2_stpn ex2_scenar.

Lemma ex2_sitpn_animate : (sitpn_animate ex2_sitpn 13) =
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
       ([[]; []; []; []],
       [(mk_place 1, 0); (mk_place 2, 1); (mk_place 3, 2);
       (mk_place 4, 1); (mk_place 5, 0); (mk_place 6, 0);
       (mk_place 7, 0)],
       [(mk_trans 1, None); (mk_trans 2, None);
       (mk_trans 3, Some (3, 3, 5)); (mk_trans 4, None);
       (mk_trans 5, Some (2, 0, 256)); (mk_trans 6, None)]);
       ([[]; []; []; []],
       [(mk_place 1, 0); (mk_place 2, 1); (mk_place 3, 2);
       (mk_place 4, 1); (mk_place 5, 0); (mk_place 6, 0);
       (mk_place 7, 0)],
       [(mk_trans 1, None); (mk_trans 2, None);
       (mk_trans 3, Some (3, 4, 5)); (mk_trans 4, None);
       (mk_trans 5, Some (2, 0, 256)); (mk_trans 6, None)]);
       ([],
       [(mk_place 1, 0); (mk_place 2, 1); (mk_place 3, 2);
       (mk_place 4, 1); (mk_place 5, 0); (mk_place 6, 0);
       (mk_place 7, 0)],
       [(mk_trans 1, None); (mk_trans 2, None);
       (mk_trans 3, Some (3, 4, 5)); (mk_trans 4, None);
       (mk_trans 5, Some (2, 0, 256)); (mk_trans 6, None)]);
       ([],
       [(mk_place 1, 0); (mk_place 2, 1); (mk_place 3, 2);
       (mk_place 4, 1); (mk_place 5, 0); (mk_place 6, 0);
       (mk_place 7, 0)],
       [(mk_trans 1, None); (mk_trans 2, None);
       (mk_trans 3, Some (3, 4, 5)); (mk_trans 4, None);
       (mk_trans 5, Some (2, 0, 256)); (mk_trans 6, None)]);
       ([],
       [(mk_place 1, 0); (mk_place 2, 1); (mk_place 3, 2);
       (mk_place 4, 1); (mk_place 5, 0); (mk_place 6, 0);
       (mk_place 7, 0)],
       [(mk_trans 1, None); (mk_trans 2, None);
       (mk_trans 3, Some (3, 4, 5)); (mk_trans 4, None);
       (mk_trans 5, Some (2, 0, 256)); (mk_trans 6, None)]);
       ([],
       [(mk_place 1, 0); (mk_place 2, 1); (mk_place 3, 2);
       (mk_place 4, 1); (mk_place 5, 0); (mk_place 6, 0);
       (mk_place 7, 0)],
       [(mk_trans 1, None); (mk_trans 2, None);
       (mk_trans 3, Some (3, 4, 5)); (mk_trans 4, None);
       (mk_trans 5, Some (2, 0, 256)); (mk_trans 6, None)]);
       ([],
       [(mk_place 1, 0); (mk_place 2, 1); (mk_place 3, 2);
       (mk_place 4, 1); (mk_place 5, 0); (mk_place 6, 0);
       (mk_place 7, 0)],
       [(mk_trans 1, None); (mk_trans 2, None);
       (mk_trans 3, Some (3, 4, 5)); (mk_trans 4, None);
       (mk_trans 5, Some (2, 0, 256)); (mk_trans 6, None)]);
       ([],
       [(mk_place 1, 0); (mk_place 2, 1); (mk_place 3, 2);
       (mk_place 4, 1); (mk_place 5, 0); (mk_place 6, 0);
       (mk_place 7, 0)],
       [(mk_trans 1, None); (mk_trans 2, None);
       (mk_trans 3, Some (3, 4, 5)); (mk_trans 4, None);
       (mk_trans 5, Some (2, 0, 256)); (mk_trans 6, None)]);
       ([],
       [(mk_place 1, 0); (mk_place 2, 1); (mk_place 3, 2);
       (mk_place 4, 1); (mk_place 5, 0); (mk_place 6, 0);
       (mk_place 7, 0)],
       [(mk_trans 1, None); (mk_trans 2, None);
       (mk_trans 3, Some (3, 4, 5)); (mk_trans 4, None);
       (mk_trans 5, Some (2, 0, 256)); (mk_trans 6, None)]);
       ([],
       [(mk_place 1, 0); (mk_place 2, 1); (mk_place 3, 2);
       (mk_place 4, 1); (mk_place 5, 0); (mk_place 6, 0);
       (mk_place 7, 0)],
       [(mk_trans 1, None); (mk_trans 2, None);
       (mk_trans 3, Some (3, 4, 5)); (mk_trans 4, None);
       (mk_trans 5, Some (2, 0, 256)); (mk_trans 6, None)]);
       ([], [], [])].
Proof. vm_compute. reflexivity. Qed.