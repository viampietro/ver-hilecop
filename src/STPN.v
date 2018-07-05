Require Export SPN.

(*************************************************************
**************************************************************
***********************   STPN  ******************************
**************************************************************)

Structure chrono_type : Set :=
  mk_chrono
    {
      mini : nat  ; (* no [0, . ] in _S_TPN ! *)
      maxi : nat ;
      min_leb_max : mini <= maxi  ;
      cpt  : nat ;   (* possibly 0   /!\  *)
      (* in_range  : bool      mini <= cpt <= maxi 
sumbool ? ; *)
    }.

Definition good_time (i : option chrono_type) : bool :=
  match i with
  | None => true
  | Some (mk_chrono
            mini
            maxi
            _
            cpt ) =>  ((mini <=? cpt)
                         &&
                         (cpt <=? maxi))
  end.


Structure STPN : Set := mk_STPN
                           { 
                             spn : SPN ;
                             chronos : trans_type -> option chrono_type
                           }.



(******* to print *****************************************)
Print chrono_type. Print STPN.
Fixpoint intervals2list
         (transs : list trans_type)
         (eval_chronos : trans_type -> option chrono_type)
  : list (trans_type * option (nat * nat * nat) ) :=
  match transs with
  | nil => nil
  | t :: tail => match (eval_chronos t) with
                 | None  => (t, None) ::
                                      (intervals2list
                                         tail
                                         eval_chronos)
                 | Some (mk_chrono
                           mini
                           maxi
                           _
                           cpt) =>
                   (t, Some (mini, cpt, maxi)) ::
                                               (intervals2list
                                                  tail
                                                  eval_chronos)
                 end
  end.
(***************** to print ******************)


(** "enabled" <=> "arcs_classic" + "arcs_test" + "arcs_inhi" OK **)

Definition is_enabled
           (places : list place_type)
           (pre   test  inhib : weight_type)
           (m_steady : marking_type) (t : trans_type)
  : bool :=
  (pre_or_test_check
     (pre t) m_steady places)
    &&
    (pre_or_test_check
       (test t) m_steady  places)
    &&
    (inhib_check
       (inhib t) m_steady  places).
Functional Scheme is_enabled_ind :=
  Induction for is_enabled Sort Prop.
Print is_enabled_ind. Print nat_ind.
Inductive is_enabled_spec
          (places : list place_type)
          (pre   test  inhib : weight_type)
          (m_steady : marking_type) (t : trans_type)
  : Prop :=
| is_enabled_mk :   
    (pre_or_test_check
       (pre t) m_steady places)
      &&
      (pre_or_test_check
         (test t) m_steady  places)
      &&
      (inhib_check
         (inhib t) m_steady  places) = true   ->
    is_enabled_spec
      places
      pre   test  inhib
      m_steady    t.
Theorem is_enabled_correct :
  forall (places : list place_type)
          (pre   test  inhib : weight_type)
          (m_steady : marking_type) (t : trans_type),
    is_enabled
      places
      pre   test  inhib
      m_steady    t   = true        ->
    is_enabled_spec
      places
      pre   test  inhib
      m_steady    t.
Proof.
  intros places pre test inhib m_steady t.
  functional induction (is_enabled
                          places pre test inhib m_steady t)
             using is_enabled_ind.
  intro H. apply is_enabled_mk. apply H.  
Qed.
Theorem is_enabled_complete :
  forall (places : list place_type)
          (pre   test  inhib : weight_type)
          (m_steady : marking_type) (t : trans_type),
    is_enabled_spec
      places
      pre   test  inhib
      m_steady    t      ->
    is_enabled
      places
      pre   test  inhib
      m_steady    t   = true .
Proof.
  intros places pre   test  inhib m_steady  t H. elim H.
  intros H0. unfold is_enabled. rewrite H0. reflexivity.
Qed.

(**   useless fonction for SPN but useful for 

-  _asynchronous_ Petri nets
-   STPN  (and SITPN by extension) 

  needed to list the enabled transitions :

1) to increment time for the right transitions, 
at the beginning of the cycle

2) to reset disabled transitions ? 
NO !  because   m_steady   &  ! m_decreasing !    **)


Fixpoint list_enabled_aux 
         (sometranss : list trans_type)
         (places : list place_type)
         (pre    test    inhib : weight_type) 
         (m_steady   : marking_type)
         (enabled_transs : list trans_type)
  : list trans_type :=
  match sometranss with
  | [] => enabled_transs 
  | t :: tail
    =>
    if is_enabled
         places    pre    test   inhib    m_steady   t
    then list_enabled_aux 
           tail   places   pre   test   inhib  
           m_steady    (t::enabled_transs)
    else list_enabled_aux 
           tail   places   pre   test   inhib  
           m_steady    enabled_transs
  end.
Inductive list_enabled_aux_spec
          (places : list place_type)
          (pre    test    inhib : weight_type) 
          (m_steady   : marking_type)
          (enabled_transs : list trans_type)
  : list trans_type  ->   (* sometranss *)
    list trans_type  ->   (* enabled_transs *)
    Prop :=
| list_enabled_nil :
    list_enabled_aux_spec 
      places   pre   test   inhib  
      m_steady  enabled_transs [] enabled_transs
| list_enabled_cons_if :  forall
    (tail : list trans_type)
    (t : trans_type),
    list_enabled_aux_spec 
      places   pre   test   inhib  
      m_steady  enabled_transs tail (t::enabled_transs)
    ->
    is_enabled
      places
      pre   test  inhib
      m_steady    t  = true
    ->
    list_enabled_aux_spec 
      places   pre   test   inhib  
      m_steady  enabled_transs (t::tail) enabled_transs
| list_enabled_cons_else :  forall
    (tail : list trans_type)
    (t : trans_type),
    list_enabled_aux_spec 
      places   pre   test   inhib  
      m_steady  enabled_transs tail enabled_transs
    ->
    is_enabled
      places
      pre   test  inhib
      m_steady    t  = true
    ->
    list_enabled_aux_spec 
      places   pre   test   inhib  
      m_steady  enabled_transs (t::tail) enabled_transs.




Definition list_enabled 
           (sometranss : list trans_type)
           (places : list place_type)
           (pre    test    inhib : weight_type) 
           (m_steady   : marking_type)
  : list trans_type :=
  list_enabled_aux
    sometranss    places    pre    test   inhib    m_steady  [].
Inductive list_enabled_spec
           (sometranss : list trans_type)
           (places : list place_type)
           (pre    test    inhib : weight_type) 
           (m_steady   : marking_type)
  : list trans_type  ->  Prop  :=
| list_enabled_mk : forall (enabled_transs : list trans_type),
    list_enabled_aux
      sometranss    places    pre    test   inhib    m_steady  []
    = enabled_transs
    -> list_enabled_spec
         sometranss    places    pre    test   inhib    m_steady
         enabled_transs.
         
Print STPN. Print SPN.
Definition list_enabled_spn
           (spn : SPN)
  : list trans_type :=
  match spn with
  | mk_SPN
      places  transs (* nodup_places nodup_transitions *)
      pre     post    test    inhib
      marking
      (mk_prior
         Lol)
    =>
    list_enabled 
      transs      places
      pre  test  inhib      marking   
  end.
Inductive list_enabled_spn_spec
           (spn : SPN)
  : list trans_type  ->  Prop  :=
| list_enabled_spn_mk : forall
    (Lol: list (list trans_type))
    (m : marking_type)
    (places : list place_type)
    (transs : list trans_type)
    (pre  post test inhib : weight_type)
    (enabled_transs : list trans_type),
    spn = (mk_SPN
             places  transs  
             pre  post test inhib
             m
             (mk_prior
               Lol))
    ->
    list_enabled
      transs    places    pre    test   inhib    m
    = enabled_transs
    ->
    list_enabled_spn_spec
         spn 
         enabled_transs.


Print list_enabled_spn. Print chronos. 
Definition list_enabled_stpn
           (stpn : STPN)
  : list trans_type :=
  match stpn with
  | mk_STPN
      spn
      chronos
    =>
    list_enabled_spn
      spn
  end.
Inductive list_enabled_stpn_spec
           (stpn : STPN)
  : list trans_type  ->  Prop  :=
| list_enabled_stpn_mk : forall
    (spn : SPN)
    (enabled_transs : list trans_type)
    (chronos : trans_type -> option chrono_type),
    stpn = mk_STPN
             spn
             chronos
    ->
    list_enabled_spn 
      spn
    = enabled_transs
    ->
    list_enabled_stpn_spec
      stpn 
      enabled_transs.

(***********  the same but SYNCHRO  (so 2 markings) ***********)
Print synchro_check_arcs.
Fixpoint not_synchro_check_list_aux 
         (sometranss : list trans_type)
         (places : list place_type)
         (pre    test    inhib : weight_type) 
         (m_steady    m_decreasing : marking_type)
         (disabled_transs : list trans_type)
  : list trans_type :=
  match sometranss with
  | [] => disabled_transs 
  | t :: tail
    =>
    if synchro_check_arcs
         places  (pre t) (test t) (inhib t) m_steady  m_decreasing
    then not_synchro_check_list_aux 
           tail  places  pre   test  inhib  
           m_steady    m_decreasing   disabled_transs
    else not_synchro_check_list_aux 
           tail  places  pre   test  inhib  
           m_steady    m_decreasing   (t::disabled_transs)
  end.
Inductive not_synchro_check_list_aux_spec
          (places : list place_type)
          (pre    test    inhib : weight_type) 
          (m_steady   m_decreasing  : marking_type)
          (disabled_transs : list trans_type)
  : list trans_type  ->   (* sometranss *)
    list trans_type  ->   (* DISabled_transs *)
    Prop :=
| not_synchro_check_list_aux_nil :
    not_synchro_check_list_aux_spec
      places 
      pre    test    inhib 
      m_steady   m_decreasing  disabled_transs  [] disabled_transs
| not_synchro_check_list_aux_cons_if :  forall
    (tail : list trans_type)
    (t : trans_type),
    not_synchro_check_list_aux_spec 
      places   pre   test   inhib  
      m_steady m_decreasing disabled_transs tail
      disabled_transs
    ->
     synchro_check_arcs
       places  (pre t) (test t) (inhib t) m_steady  m_decreasing
     = true 
    ->
    not_synchro_check_list_aux_spec  
      places   pre   test   inhib  
      m_steady  m_decreasing disabled_transs (t::tail)
      disabled_transs
| not_synchro_check_list_aux_cons_else :  forall
    (tail : list trans_type)
    (t : trans_type),
    not_synchro_check_list_aux_spec 
      places   pre   test   inhib  
      m_steady m_decreasing disabled_transs tail
      disabled_transs
    ->
     synchro_check_arcs
       places  (pre t) (test t) (inhib t) m_steady  m_decreasing
     = false
    ->
    not_synchro_check_list_aux_spec  
      places   pre   test   inhib  
      m_steady  m_decreasing disabled_transs (t::tail)
      disabled_transs.

Definition not_synchro_check_list 
         (sometranss : list trans_type)
         (places : list place_type)
         (pre    test    inhib : weight_type) 
         (m_steady    m_decreasing : marking_type)
  : list trans_type :=
  not_synchro_check_list_aux 
    sometranss 
    places
    pre    test    inhib
    m_steady    m_decreasing  [].
Inductive not_synchro_check_list_spec
           (sometranss : list trans_type)
           (places : list place_type)
           (pre    test    inhib : weight_type) 
           (m_steady   m_decreasing : marking_type)
  : list trans_type  ->  Prop  :=
| not_synchro_check_list_mk : forall
    (enabled_transs : list trans_type),
    not_synchro_check_list_aux 
      sometranss 
      places
      pre    test    inhib
      m_steady    m_decreasing  []
    = enabled_transs
    -> not_synchro_check_list_spec
         sometranss    places    pre    test   inhib
         m_steady  m_decreasing
         enabled_transs.


(********************* TIME intervals  ---> chronos  ***********)

Print STPN. Print chronos.
(* increment time, for a given list of enabled transitions *)
Definition increment_time_trans
           (chronos : trans_type -> option chrono_type)
           (t :  trans_type)
  : trans_type -> option chrono_type :=
  match (chronos t) with
  | None => chronos  (* increment nothing ... *)
  | Some (mk_chrono        (* immutable ... *)
            mini
            maxi
            min_le_max
            cpt )
    => (fun trans =>
          if beq_transs
               trans t
          then Some (mk_chrono
                       mini
                       maxi
                       min_le_max
                       (cpt + 1))
          else (chronos trans))                      
  end.

Fixpoint increment_time_enabled
         (chronos : trans_type -> option chrono_type)
         (enabled_transs : list trans_type)
  : trans_type -> option chrono_type :=
  match enabled_transs with
  | [] => chronos
  | t :: tail
    =>
    increment_time_enabled
      (increment_time_trans
         chronos   t)
      tail
  end.

(* on incremente en debut de cycle. Avec un marquage stable 
donc on se sert d'une liste de transitions enabled, 
facilement calculable *)

Definition reset_time_trans
           (chronos : trans_type -> option chrono_type)
           (t : trans_type)
  : trans_type -> option chrono_type :=
  match (chronos t) with
  | None  => chronos   (* reset nothing ... *)
  | Some (mk_chrono
            mini
            maxi
            min_le_max
            cpt )
    => (fun trans =>
          if beq_transs
               trans t
          then Some (mk_chrono
                       mini
                       maxi
                       min_le_max
                       0 )
          else (chronos trans))             
  end.
(* 
le reset de compteur est plus subtil : 
 1) quand faut-il le faire ?  
   ----> a la fin du cycle ou plutot dans stpn_sub_fire_pre !
 2) pour quelles transitions faut-il le faire ?
   ----> celles desensibilisees durant le cycle. meme transitoirement
*)
    
(* reset time counters of (a class of ?) some transitions ... *)
Fixpoint reset_time_disabled
           (chronos : trans_type -> option chrono_type)
           (disabled_transs : list trans_type)
  : trans_type -> option chrono_type :=
  match disabled_transs with
  | [] => chronos
  | t :: tail => reset_time_disabled
                   (reset_time_trans
                      chronos
                      t)
                   tail
  end.


(*****************************************************************
**********   FIRING ALGORITHM    for STPN      *******************
******************************************************************)

Print STPN. Print spn_class_fire_pre. Print reset_time_trans.
Check update_marking_pre.
(** given 1 ordered class of transitions 
in structural conflict (a list class_of_transs), 
return 1 list of transitions "subclass_half_fired" 
and marking "m_intermediate" accordingly ...   *)
Fixpoint stpn_class_fire_pre_aux
         (places : list place_type)
         (pre    test    inhib : weight_type) 
         (m_steady    m_decreasing : marking_type) 
         (chronos : trans_type -> option chrono_type)
         (class_transs   subclass_half_fired : list trans_type)  
  : (list trans_type) * marking_type * (trans_type -> option chrono_type) :=
  match class_transs with
  | t :: tail =>
    if synchro_check_arcs
         places (pre t) (test t) (inhib t) m_decreasing m_steady
         (* t is enabled, even w.r.t. to the others *)
         && (good_time (chronos  t))
    then   (* firing  t *)
      let new_decreasing   :=
          (update_marking_pre
             places  t  pre  m_decreasing)
      in   (* reseting the disabled intervals ! *)
      let new_chronos :=
          (reset_time_disabled
             chronos
             (not_synchro_check_list
                class_transs   places     pre    test    inhib
                m_steady       new_decreasing))
      in
      stpn_class_fire_pre_aux
        places    pre    test   inhib   m_steady      new_decreasing 
        new_chronos   tail      (subclass_half_fired ++ [t])
    else  (* not enabled  w.r.t. the other transs OR not goog time*)
      stpn_class_fire_pre_aux
        places    pre    test   inhib   m_steady    m_decreasing
        chronos     tail        subclass_half_fired
  | []  => (subclass_half_fired, m_decreasing, chronos)
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

(* filling subclass_half_fired  ...  *)
Definition stpn_class_fire_pre
           (places : list place_type)
           (pre    test    inhib : weight_type) 
           (m_steady    m_decreasing : marking_type) 
           (chronos : trans_type -> option chrono_type)
           (class_transs : list trans_type)
  : (list trans_type) *
    marking_type      *
    (trans_type -> option chrono_type) :=
  stpn_class_fire_pre_aux
    places
    pre    test    inhib
    m_steady    m_decreasing
    chronos     class_transs    [].

(* stpn_fire_pre 
 apply sub_fire_pre over ALL classes of transitions. 
 Begin with initial marking, 
  end with half fired marking.  
 "classes_half_fired" is empty at first 
 (a bit like for sub_fire_pre) 
 *)
Print nth. Print prior_type.
Fixpoint stpn_fire_pre_aux
         (places : list place_type)
         (pre test inhib : weight_type)
         (m_steady    m_decreasing : marking_type)
         (chronos : trans_type -> option chrono_type)
         (classes_transs  classes_half_fired : list (list trans_type))
  : (list (list trans_type)) *
    marking_type *
    (trans_type -> option chrono_type)  :=
  match classes_transs with
  | [] => (classes_half_fired , m_decreasing, chronos)
  | class :: Ltail => let '(sub_l, new_m, new_chronos) :=
                          stpn_class_fire_pre
                            places
                            pre     test    inhib
                            m_steady    m_decreasing
                            chronos     class
                      in  stpn_fire_pre_aux
                            places
                            pre  test  inhib
                            m_steady   new_m
                            new_chronos      Ltail
                            (sub_l :: classes_half_fired)         
  end.

Definition stpn_fire_pre
         (places : list place_type)
         (pre test inhib : weight_type)
         (m_steady : marking_type)
         (chronos : trans_type -> option chrono_type)
         (classes_transs  : list (list trans_type))
  : (list (list trans_type)) *
    marking_type *
    (trans_type -> option chrono_type)  :=
  stpn_fire_pre_aux
    places
    pre test inhib 
    m_steady    m_steady
    chronos     classes_transs  [].
  
(***************************************************)
(******* for  DEBUGGING  only  ..  *****************)
Search SPN.
Print spn_debug1. 
Print stpn_fire_pre.
Definition stpn_debug1
           (places : list place_type)
           (transs : list trans_type)
           (pre test inhib : weight_type)
           (marking : marking_type)
           (chronos : trans_type -> option chrono_type)
           (classes_transs : list (list trans_type))
  : (list (list trans_type)) *
    list (place_type * nat)  *
    list (trans_type * option (nat * nat * nat)) (* chronos *) :=
  let '(sub_Lol, m_inter, new_chronos ) := (stpn_fire_pre
                                              places 
                                              pre   test  inhib 
                                              marking
                                              chronos
                                              classes_transs)
  in
  (sub_Lol, marking2list
              m_inter   places ,
  intervals2list
    transs
    new_chronos).

Print spn_debug2. Print SPN.
Definition stpn_debug2 (stpn : STPN)
  : (list (list trans_type)) *
    list (place_type * nat)  *
    list (trans_type * option (nat * nat * nat))  :=
  match stpn with
  | mk_STPN
      (mk_SPN
         places  transs (* nodup_places nodup_transitions *)
         pre     test    inhib        post
         marking
         (mk_prior
            Lol) )
      chronos
    =>
    stpn_debug1
      places    transs
      pre   test   inhib
      marking
      chronos
      Lol
  end.

(**************************************************************)
(*******************  fire_post already done in SPN.v *********)
(******* fire *************************************************)

(* Returns  [transitions fired + final marking] *)
Definition stpn_fire  
           (places : list place_type)
           (pre test inhib post : weight_type)
           (m_init : marking_type)
           (chronos : trans_type -> option chrono_type)
           (classes_transs : list (list trans_type))
  : (list (list trans_type)) *
    marking_type             *
    (trans_type -> option chrono_type)  :=
  let '(sub_Lol, m_inter, new_chronos) :=
      stpn_fire_pre
        places    pre  test  inhib 
        m_init       chronos    classes_transs
  in  (sub_Lol ,
       fire_post
         places     post
         m_inter     sub_Lol ,
       new_chronos ).

(* The marking and the chronos are evolving,  
but we want to see also the      fired transitions    *)
(******************************* CYCLE **********************)
Print list_enabled_stpn. Print STPN. Print SPN.
Definition stpn_cycle (stpn : STPN)           
  : (list (list trans_type)) * STPN  :=
  match stpn with
  | mk_STPN
      (mk_SPN
         places  transs (* nodup_places  nodup_transitions *)
         pre     post    test          inhib         
         marking         (mk_prior
                            Lol) )
      chronos
    =>
    let enabled := list_enabled_stpn
                     stpn                         in
    let chronos_incr := increment_time_enabled
                          chronos 
                          enabled                 in
    let '(transs_fired, new_m, new_chronos) :=
        stpn_fire  
          places     pre  test  inhib  post
          marking     chronos_incr     Lol
    in (transs_fired, 
        (mk_STPN
           (mk_SPN
              places  transs  (* nodup_places  nodup_transitions *)
              pre     post     test          inhib
              new_m           (mk_prior
                                 Lol) )
           new_chronos))
  end.


(**************************************************)
(************* to animate a STPN   *****************)

(* n steps calculus  *)
Print STPN. Check intervals2list. Print spn_animate.
Fixpoint stpn_animate
         (stpn : STPN)
         (n : nat)
  : list
      (list (list trans_type)  *
       list (place_type * nat) *
       (list (trans_type * option (nat * nat * nat)))) :=
  match n with
  | O => [ ( [] , [] , [] 
         (*    marking2list
                    (places   (spn stpn))
                    (marking  (spn stpn)) ,
             (intervals2list
                (transs (spn stpn))
                (chronos     stpn))  *)
         ) ]
  | S n' =>  let (Lol_fired, next_stpn) := (stpn_cycle stpn)
             in
             ( Lol_fired ,
               (marking2list
                  (marking (spn  next_stpn))
                  (places (spn   next_stpn))) ,
               (intervals2list
                  (transs (spn   next_stpn))
                  (chronos       next_stpn)) ) 
               ::
               (stpn_animate
                  next_stpn
                  n')
  end.    

