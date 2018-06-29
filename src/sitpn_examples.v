Require Import SITPN stpn_examples.

(*** interpreted Petri net ***)
Definition ex_eval_conds_cycle1 (t : trans_type)
  : option bool :=
  match t with
  | mk_trans 0  => Some true
  | mk_trans 2  => Some false
  | _ => None
  end.
Definition ex_eval_conds_cycle2 (t : trans_type)
  : option bool :=
  match t with
  | mk_trans 0  => Some true
  | mk_trans 2  => Some true
  | _ => None
  end.
Definition ex_eval_conds_cycle3 (t : trans_type)
  : option bool :=
  match t with
  | mk_trans 0  => Some true
  | mk_trans 2  => Some true
  | mk_trans 3  => Some false
  | _ => None
  end.
Definition ex_eval_conds_cycle4 (t : trans_type)
  : option bool :=
  match t with
  | mk_trans 0  => Some true
  | mk_trans 2  => Some true
  | mk_trans 3  => Some false
  | _ => None
  end.
Definition ex_eval_conds_cycle5 (t : trans_type)
  : option bool :=
  match t with
  | mk_trans 0  => Some true
  | mk_trans 2  => Some true
  | mk_trans 3  => Some false
  | _ => None
  end.



Import ListNotations.
Definition ex_scenar := [ex_eval_conds_cycle1 ;
                           ex_eval_conds_cycle2 ;
                           ex_eval_conds_cycle3 ;
                           ex_eval_conds_cycle4 ;
                           ex_eval_conds_cycle5].


Print ex_stpn.
Definition ex_sitpn := mk_SITPN
                         ex_stpn
                         ex_scenar.

Compute (animate_sitpn
           ex_sitpn
           11).

Print SITPN.
Compute
  (scenario
     (snd (sitpn_cycle  
             (snd (sitpn_cycle 
                     (snd (sitpn_cycle   
                             ex_sitpn)
                                    
                      )))))).
Compute
  (sitpn_debug2
     (snd (sitpn_cycle  
             (snd (sitpn_cycle

                     (snd (sitpn_cycle

                     
                             (snd (sitpn_cycle   
                                     ex_sitpn)
                          
                      )))))))).

