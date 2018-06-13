(*  Require Import ALL.  *)


Inductive step : SPN -> SPN -> Prop := 
| trans_sync: forall (x y : SPN),
    (y = cycle_spn x)  ->  (step x y).  

                             
Definition is_the_algorithm (f : SPN -> SPN) :=
  forall spn, (* Permutation al (f al) /\ sorted (f al) *) . 
