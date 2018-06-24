Require Export STPN.

(********************************************************
*********************************************************
*********************   SITPN   *************************
*********************************************************)

(**************************************************************)
(* conditions  on transitions...   for Interpreted Petri nets *)

(*
Inductive cond_type : Set :=
| mk_cond : nat -> cond_type. *)

(*** conditions are evolving through time 
   scenario/scenari 
some transitions of a Petri net are given conditions
which have a boolean value  ****)

(***  a list of size n allows one to compute up to n cycles  ***) 

Definition conditions_type := trans_type -> option bool.
(* some transitions (+ transitions not inside the Petri net)
don't have any condition at all *)

Definition scenar_type := list conditions_type.

Structure SITPN : Set := mk_SITPN
                           { 
                             stpn : STPN  ;
                             scenario : scenar_type
                           }.

(*****************************************************************
******************************************************************
*********   FIRING ALGORITHM    for SITPN     ********************
******************************************************************)

Print SITPN.
Check update_marking_pre.
(** given 1 ordered class of transitions 
in structural conflict (a list class_of_transs), 
return 1 list of transitions "subclass_half_fired" 
and marking "m_intermediate" accordingly ...   *)
Fixpoint sitpn_sub_fire_pre
         (places : list place_type)
         (pre test inhib : weight_type)  (* 3 *)
         (m_init m_intermediate : marking_type)    (* 2 *)
         (* to reset clocks .. *)
         (enabled_transs : list trans_type)
         (intervals : trans_type -> option chrono_type)
         (* to reset clocks .. *)
         (class_transs subclass_half_fired : list trans_type) (* 2 *)
  (* "subclass_half_fired"  is meant to be empty at first *)
         (conditions : conditions_type)
  : (list trans_type) *
    marking_type *
    (trans_type -> option chrono_type) :=
  match class_transs with
  | t :: tail => if (
                     (pre_or_test_check
                        places
                        (pre t)
                        m_intermediate)
                       && (pre_or_test_check
                             places
                             (test t)
                             m_init)
                       && (inhib_check
                             places
                             (inhib t)
                             m_init)
                   )
                 then
                   if
                     (good_time (intervals t))
        (* si transition a une condition alors regarder la condition
sinon faire ce qui est dans le "then"  

si condition vrai alors faire ce qui est dans le "then"
sinon elle n'est pas tirable

         *)      
                   then
                     let new_m :=
                         (update_marking_pre
                            places t pre m_intermediate)
                     in
                     stpn_sub_fire_pre
                       places pre test inhib
                       m_init new_m 
                       
                       enabled_transs
                       (* updating the intervals in case ... *)
                       (reset_time_list
                          intervals
                          (list_enabled
                             places
                             pre test inhib
                             new_m
                             class_transs)
                       )
                       
                       tail (subclass_half_fired ++ [t])
                       (* concatenate t behind, to keep order *)
                   else
                     stpn_sub_fire_pre
                            places pre test inhib
                            m_init m_intermediate
                            enabled_transs  intervals
                            tail subclass_half_fired 
                        (* t not fired, let's continue with tail *)
                 else


(*
                   (if
                          in_list_enabled
                            enabled_transs
                            t
                        then (* reset the local counter of
                            this (momentarily) disabled trans *)
                          sub_fire_pre
                            places pre test inhib
                            m_init m_intermediate
                            enabled_transs
                            (reset_time
                               intervals
                               t )
                            tail subclass_half_fired
                        else   *)
                   stpn_sub_fire_pre
                     places  pre  test  inhib
                     m_init  m_intermediate
                     enabled_transs  intervals
                     tail subclass_half_fired 
                        
  | []  => (subclass_half_fired, m_intermediate, intervals)
  end.
(* 
there are 3 parallel calculus in this function : 
1) pumping tokens to get "m_intermediate"  (half fired)
2) returning subclass of transitions (half fired)
3) resting local counters of any "enabled transition no more enabled". 
and 2 markings are recorded : 
1) the initial one to check with inhib and test arcs
2) a floating (decreasing) intermediate marking to check classic arcs
*)

(*
 Apply sub_fire_pre over ALL classes of transitions. 
 Begin with initial marking, 
  end with half fired marking.  
 "classes_half_fired" is empty at first 
 (a bit like for sub_fire_pre) 
 *)
Print nth. Print prior_type.
Fixpoint sitpn_fire_pre
         (places : list place_type)
         (pre test inhib : weight_type)
         (marking : marking_type)
         (* ......... to reset clocks .................. *)
         (enabled_transs : list trans_type)
         (chronos : trans_type -> option chrono_type)
         (* ......... to reset clocks .................. *)
         (classes_transs  classes_half_fired : list (list trans_type))
         (conditions : conditions_type)
  : (list (list trans_type)) *
    marking_type *
    (trans_type -> option chrono_type)  :=
  match classes_transs with
  | [] => (classes_half_fired , marking, chronos)
  | l :: Ltail => let '(sub_l, new_m, new_i) := sitpn_sub_fire_pre
                                                  places
                                                  pre test inhib
                                                  marking marking
                                                  enabled_transs
                                                  chronos
                                                  l []
                                                  conditions
                  in
                  sitpn_fire_pre
                    places
                    pre  test  inhib
                    new_m
                    enabled_transs  new_i
                    Ltail
                    (sub_l :: classes_half_fired)
                    conditions
  end.

(*
Print SPN.  (*** for nice prints  only  ! debugging ..  **)
Definition fire_pre_print
           (places : list place_type) (pre test inhib : weight_type)
           (marking : marking_type)
           (classes_transs classes_half_fired : list (list trans_type))
  : (list (list trans_type)) * list (place_type * nat) :=
  let res := (fire_pre
                places 
                pre
                test 
                inhib 
                marking
                classes_transs [] )
  in
  ((fst res), marking2list
                places 
                (snd res) ).

*)

(* Returns  [transitions fired + final marking] *)
Definition sitpn_fire  
           (places : list place_type)
           (pre test inhib post : weight_type)
           (m_init : marking_type)
           (* ......... to reset clocks .................. *)
           (enabled_transs : list trans_type)
           (chronos : trans_type -> option chrono_type)
           (* .......... to reset clocks ................. *)
           (classes_transs : list (list trans_type))
           (conditions : conditions_type)

  : (list (list trans_type)) *
    marking_type *
    (trans_type -> option chrono_type)  :=

  let '(L, m, i) := sitpn_fire_pre
                      places  pre test inhib 
                      m_init
                      enabled_transs  chronos
                      classes_transs []
                      conditions
  in
  ( L ,
    fire_post
      places post
      m
      L ,
    i  ).

(* The marking and the "intervals" (their counter) 
   are evolving !!  
but we want to see also the fired transitions ! *)
(******************************* CYCLE **********************)
Print list_enabled. Print SITPN. Print STPN. Print SPN.
Definition sitpn_cycle (stpn : STPN)
           
  : (list (list trans_type)) * STPN  :=

  match stpn with
  | mk_STPN
      (mk_SPN
         places
         transs
       (*  nodup_places 
           nodup_transitions *)          
         pre
         test
         inhib
         post
         marking
         (mk_prior
            Lol)
      )
      chronos
    => let enabled := (list_enabled
                       places 
                       pre  test  inhib 
                       marking
                       transs
                    )
     in let chronos_incr := increment_time
                              chronos 
                              enabled
        in let '(fired, new_m, new_chronos) := stpn_fire  
                                                 places
                                                 pre 
                                                 test
                                                 inhib  post
                                                 marking
                                                 enabled (* ! *)  
                                                 chronos_incr (* ! *)
                                                 Lol
           in  (fired ,  (* ! *)
                (mk_STPN
                   (mk_SPN
                      places
                      transs 
                   (*   nodup_places 
                        nodup_transitions *) 
                      pre
                      post
                      test
                      inhib
                      new_m       (* ! *)
                      (mk_prior
                         Lol)
                   )
                   new_chronos  (* ! *)
                )     
               )
  end.



                         

(**************************************************)
(************* to animate a SITPN   *****************)

(* n steps calculus  *)
Print STPN. Check intervals2list.
Fixpoint animate_sitpn
         (stpn : STPN)
         (n : nat)
  : list
      (list (list trans_type)  *
       list (place_type * nat) *
       (list (trans_type * option (nat * nat * nat)))) :=
  match n with
  | O => [ ( [] ,
             marking2list
                    (places (spn stpn))
                    (marking (spn stpn)) ,
             (intervals2list
                (transs (spn stpn))
                (chronos stpn))
         ) ]
  | S n' =>  let (fired, next_stpn) := (stpn_cycle stpn)
             in
             ( fired ,
               (marking2list
                  (places (spn
                             next_stpn))
                  (marking (spn
                              next_stpn))) ,
               (intervals2list
                  (transs (spn
                             next_stpn))
                  (chronos
                     next_stpn))
             ) 
               ::
               (animate_stpn
                  next_stpn
                  n')
  end.    (* split / combine ... *)
