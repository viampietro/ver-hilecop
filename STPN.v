(****************************************************)
(********* intervals of time...   for S(I)TPN   *******) 

Print le. About "<=". Print nat_star.
Definition lebo (n m : nat_star) : Prop :=
  match (n, m) with
  | (mk_nat_star
       intn
       posin ,
     mk_nat_star
       intm
       posim) => intn <= intm
  end.
Notation "n o<= m" := (lebo n m)
                        (at level 50) : type_scope.

Structure time_interval_type : Set :=
  mk_inter
    {
      mini : nat_star ; (* no [0, in synchronous time Petri nets *) 
      maxi : nat_star ;
      min_le_max : mini o<= maxi  ;
      cpt  : nat ;   (* nat_star ? *)
      (* in_range  : bool      mini <= cpt <= maxi ; *)
    }.



Structure STPN : Set := mk_STPN
                           {
                             spn : SPN ;
                             intervals : trans_type ->
                                         option time_interval_type ;}.
(* there is an interval iff there is a local clock *)
(*** but if conditions are meant to evolve through time .... *)



(* conditions + intervals  ?? *)
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
