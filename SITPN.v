
(* conditions  on transitions...   for  SIPN  (interpreted) *)
Inductive cond_type : Set :=
| mk_cond : nat -> cond_type.

(*  inutile
Definition caract_funct_gards := trans_type -> cond_type -> bool.

Notation "cond [ trans ]" := (caract_funct_gards
                                trans
                                cond)  
                               (at level 50) : type_scope. *)

Structure SITPN : Set := mk_SITPN
                          {
                            stpn : STPN ;
                            conds : trans_type -> list cond_type
                            (** good to have list of conditions ??
possibly an empty list **) ;}.

(*** scenario  scenari  ....  evolving through time  ???? *)
(***   --->  central  clock ?  ***) 






(*** interpreted Petri net ***)
Definition ex_conditions (t : trans_type) (c : gard_type)
  : bool
  := match (t, c) with
  | (mk_trans 0, mk_gard 0) => true
  | (mk_trans 2, mk_gard 1) => true
  | _ => false
  end.

Definition ipn_ex := mk_IPN
                       ex_pn
                       ex_conditions.







(***************************************************************)
(**************** "firable" is stronger than "enabled" *********)
(********************** conditions & intervals *****************)


Definition eval_cond (c : cond_type) : bool := true.

Fixpoint conds_firable_trans_aux
           (t : trans_type)
           (con : list cond_type)
  : bool :=
  match con with
  | []  => true
  | c :: tail => (eval_cond c)
                   && (conds_firable_trans_aux
                         t
                         tail)
  end.

Definition conds_firable_trans
           (t : trans_type)
           (conds : trans_type -> list cond_type)
  : bool :=
  conds_firable_trans_aux
    t 
    (conds t).





Print SITPN. Print time_interval_type. Print nat_star.
Definition inter_firable_trans
           (t : trans_type)
           (intervals : trans_type -> option time_interval_type)
  : bool :=
  match (intervals t) with
  | None  => true
  | Some inter => match inter with
                  | mk_inter
                      mini
                      maxi
                      min_le_max
                      cpt => (*match (mini, maxi) with
                             | (mk_nat_star
                                  inta
                                  carea,
                                mk_nat_star
                                  intb
                                  careb) =>*) if (mini <=? cpt)
                                                   &&
                                                   (cpt <=? maxi)
                                              then true
                                              else false
                  end
                                
  end.



(* conditions + intervals *)
Definition firable_trans
           (t : trans_type)
           (conds : trans_type -> list cond_type)
           (intervals : trans_type -> option time_interval_type)
            : bool :=
  (conds_firable_trans
     t
     conds)
    &&
    (inter_firable_trans
       t
       intervals).
