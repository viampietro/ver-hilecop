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
(* some transitions don't have any condition *)

Definition scenar_type := list conditions_type.

Structure SITPN : Set := mk_SITPN
                           { 
                             stpn : STPN  ;
                             scenario : scenar_type
                           }.

Definition condition_check
           (conditions : conditions_type)
           (t : trans_type)
  : bool :=
  match (conditions t) with
  | None  =>  true
  | Some b  => b
  end.

(*****************************************************************
******************************************************************
*********   FIRING ALGORITHM    for SITPN     ********************
******************************************************************)

Print SITPN.
Print stpn_class_fire_pre_aux.
(** compared with STPN it just add an "if clause"  : *) 
Fixpoint sitpn_class_fire_pre_aux
         (places : list place_type)
         (pre test inhib : weight_type)
         (m_steady m_decreasing : marking_type)
         (chronos : trans_type -> option chrono_type)
         (class_transs  subclass_half_fired : list trans_type)
         (conditions : conditions_type)
         {struct class_transs} :
  list trans_type * marking_type *
  (trans_type -> option chrono_type) :=
  match class_transs with
  | [] => (subclass_half_fired, m_decreasing, chronos)
  | t :: tail =>
    if
      (synchro_check_arcs places (pre t) (test t) 
                          (inhib t)  m_steady  m_decreasing)
        && (good_time (chronos t))
        && (condition_check conditions t)
    then
      let new_decreasing :=
          update_marking_pre
            places t pre m_decreasing in
      let new_chronos :=
          reset_time_disabled
            chronos
            (not_synchro_check_list
               class_transs places pre test
               inhib m_steady new_decreasing) in
      stpn_class_fire_pre_aux
        places pre test inhib m_steady
        new_decreasing new_chronos tail
        (subclass_half_fired ++ [t])
    else
      stpn_class_fire_pre_aux
        places pre test inhib m_steady
        m_decreasing chronos tail subclass_half_fired
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

Print stpn_class_fire_pre.
Definition sitpn_class_fire_pre
           (places : list place_type)
           (pre test inhib : weight_type)
           (m_steady m_decreasing : marking_type)
           (chronos : trans_type -> option chrono_type)
           (class_transs : list trans_type)
           (conditions : conditions_type)
  : list trans_type * marking_type *
  (trans_type -> option chrono_type) :=
  sitpn_class_fire_pre_aux
    places    pre test inhib m_steady m_decreasing
    chronos class_transs []   conditions.

Print stpn_fire_pre_aux.
Fixpoint sitpn_fire_pre_aux
         (places : list place_type)
         (pre test inhib : weight_type)
         (m_steady m_decreasing : marking_type)
         (chronos : trans_type -> option chrono_type)
         (classes_transs classes_half_fired : list (list trans_type))
         (conditions : conditions_type)
         {struct classes_transs} :
  list (list trans_type) * marking_type *
  (trans_type -> option chrono_type) :=
  match classes_transs with
  | [] => (classes_half_fired, m_decreasing, chronos)
  | class :: Ltail =>
    let
      '(sub_l, new_m, new_chronos) :=
      sitpn_class_fire_pre
        places     pre test inhib    m_steady  m_decreasing
        chronos    class             conditions         in
    sitpn_fire_pre_aux
      places       pre test inhib    m_steady  new_m
      new_chronos  Ltail (sub_l :: classes_half_fired) conditions
  end.

Print stpn_fire_pre.
Definition sitpn_fire_pre
           (places : list place_type)
           (pre test inhib : weight_type)
           (m_steady : marking_type)
           (chronos : trans_type -> option chrono_type)
           (classes_transs : list (list trans_type))
           (conditions : conditions_type )
  : list (list trans_type) * marking_type *
  (trans_type -> option chrono_type) :=
  sitpn_fire_pre_aux
    places pre test inhib m_steady m_steady chronos
    classes_transs [] conditions.

(***************************************************)
(******* for  DEBUGGING  only  ..  *****************)
Search SPN.
Print stpn_debug1. 
Definition sitpn_debug1
           (places : list place_type)
           (transs : list trans_type)
           (pre test inhib : weight_type)
           (marking : marking_type)
           (chronos : trans_type -> option chrono_type)
           (classes_transs : list (list trans_type))
           (conditions : conditions_type )
  : (list (list trans_type)) *
    list (place_type * nat)  *
    list (trans_type * option (nat * nat * nat)) (* chronos *) :=
  let '(sub_Lol, m_inter, new_chronos ) := (sitpn_fire_pre
                                              places 
                                              pre   test  inhib 
                                              marking
                                              chronos
                                              classes_transs
                                              conditions)
  in
  (sub_Lol, marking2list
              m_inter  places ,
  intervals2list
    transs
    new_chronos).

Print stpn_debug2. Print SITPN. Print scenar_type. Print conditions_type.
Definition sitpn_debug2 (sitpn : SITPN)
  : (list (list trans_type)) *
    list (place_type * nat)  *
    list (trans_type * option (nat * nat * nat))  :=
  match sitpn with
  | mk_SITPN
      (mk_STPN
         (mk_SPN
            places  transs (* nodup_places nodup_transitions *)
            pre     test    inhib        post
            marking
            (mk_prior
               Lol) )
         chronos )
      scenario
    =>
    match scenario with
    | C :: tail
      => 
      sitpn_debug1
        places    transs
        pre   test   inhib
        marking
        chronos
        Lol
        C
    | [] => ([], [], [])
    end
  end.

(**************************************************************)
(*******************  fire_post already done in SPN.v *********)
(******* fire *************************************************)

Print conditions_type.
(* Returns  [transitions fired + final marking] *)
Print stpn_fire.
Definition sitpn_fire  
           (places : list place_type)
           (pre test inhib post : weight_type)
           (m_steady : marking_type)
           (chronos : trans_type -> option chrono_type)
           (classes_transs : list (list trans_type))
           (conditions : conditions_type)
  : (list (list trans_type)) *
    marking_type *
    (trans_type -> option chrono_type)  :=
  let '(sub_Lol, m_inter, new_chronos) := sitpn_fire_pre
                                            places  pre test inhib 
                                            m_steady    chronos
                                            classes_transs
                                            conditions
  in
  (sub_Lol ,
   fire_post
     places post
     m_inter
     sub_Lol ,
   new_chronos).

(* The marking and the "intervals" (their counter) 
   are evolving !!  
but we want to see also the fired transitions ! *)
(******************************* CYCLE **********************)
Print list_enabled. Print SITPN. Print STPN. Print SPN.
Print stpn_cycle.
Definition sitpn_cycle (sitpn : SITPN)
  : (list (list trans_type)) * SITPN  :=
  match sitpn with
  | mk_SITPN
      (mk_STPN
         (mk_SPN
            places  transs
            (* nodup_places  nodup_transitions *)          
            pre     post    test          inhib         
            marking
            (mk_prior
               Lol) )
         chronos)
      scenario
    =>
    match scenario with
    | [] => ([], sitpn)   (* dangerous ? *)
    | C :: tail =>
      let chronos_incr := increment_time_enabled
                            chronos
                            (list_enabled_stpn
                               (stpn sitpn))
      in
      let
        '(transs_fired, new_m, new_chro) :=
        sitpn_fire
          places pre test inhib post marking 
          chronos_incr Lol C
      in
      (transs_fired,
       (mk_SITPN
          (mk_STPN
             (mk_SPN
                places  transs  (* nodup_places  nodup_transitions *)
                pre     post     test          inhib
                new_m      
                (mk_prior
                   Lol) )
             new_chro  )
          (tl scenario)))
    end
  end.

(**************************************************)
(************* to animate a SITPN   *****************)

(* n steps calculus  *)
Print SITPN. Check intervals2list.
Fixpoint animate_sitpn
         (sitpn : SITPN)
         (n : nat)   (* n should be less than length scenario ... *)
  : list
      (list (list trans_type)  *
       list (place_type * nat) *
       (list (trans_type * option (nat * nat * nat)))) :=
  match n with
  | O => [ ( [] , [] , [] ) ]
  | S n' =>  let (fired, next_sitpn) := (sitpn_cycle sitpn)
             in
             ( fired ,
               (marking2list
                  (marking (spn (stpn  next_sitpn)))
                  (places (spn (stpn  next_sitpn)))) ,
               (intervals2list
                  (transs (spn (stpn   next_sitpn)))
                  (chronos (stpn        next_sitpn)))
             ) 
               ::
               (animate_sitpn
                  next_sitpn
                  n')
  end.


