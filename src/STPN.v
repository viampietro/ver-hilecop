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
Definition trans_is_enabled
           (places : list place_type)
           (pre : weight_type)
           (pre_test : weight_type)
           (pre_inhi : weight_type)
           (m : marking_type)
  : trans_type -> bool :=  
  fun t => (pre_or_test_check places (pre t) m)
             &&
             (pre_or_test_check places (pre_test t) m)
             &&
             (inhib_check places (pre_inhi t) m). 
(**   useless fonction ?  (unless for STPN and SITPN ...)
 because 
 firing a bunch of transitions synchronously implies
   checking arcs with a constant marking AND a decreasing one ! 
 --->    useful only for _asynchronous_ Petri nets, or S(I)TPN **)

(**   needed to list the enabled transitions :

1) to increment time for the right transitions, 
at the beginning of the cycle

2) to reset disabled transitions ? during "fire_pre" ? or after ?
*)


Fixpoint list_enabled_aux
         (places : list place_type)
         (pre test inhib : weight_type)
         (m : marking_type)
         (transs enabled_transs : list trans_type) (*input/output*)
  : list trans_type :=
  match transs with
  | [] => enabled_transs
  | t :: tail => if trans_is_enabled
                      places
                      pre test inhib
                      m t
                 then list_enabled_aux
                        places
                        pre test inhib
                        m
                        tail (t::enabled_transs)
                 else list_enabled_aux
                        places
                        pre test inhib
                        m
                        tail enabled_transs
  end.
Definition list_enabled
           (places : list place_type)
           (pre test inhib : weight_type)
           (m : marking_type)
           (transs : list trans_type) (*input/output*)
  : list trans_type :=
  list_enabled_aux
    places
    pre test inhib
    m
    transs [].

Fixpoint list_disabled_aux
         (places : list place_type)
         (pre test inhib : weight_type)
         (m : marking_type)
         (enabled_transs  disabled_transs : list trans_type)
  : list trans_type :=
  match enabled_transs with
  | [] => disabled_transs
  | t :: tail => if trans_is_enabled
                      places
                      pre test inhib
                      m t
                 then list_disabled_aux
                        places
                        pre test inhib
                        m
                        tail   disabled_transs
                 else list_disabled_aux
                        places
                        pre test inhib
                        m
                        tail   (t::disabled_transs)
  end.
Definition list_disabled
           (places : list place_type)
           (pre test inhib : weight_type)
           (m : marking_type)
           (enabled_transs : list trans_type) (*input/output*)
  : list trans_type :=
  list_disabled_aux
    places
    pre test inhib
    m
    enabled_transs [].

Search trans_type. 
Fixpoint in_list    (* must exist in library List *)
         (some_transs : list trans_type)
         (trans : trans_type)
  : bool :=
  match some_transs with
  | [] => false
  | t :: tail => if (beq_transs trans t)  (* t =? trans *)
                 then true
                 else false
  end.  

(********************* TIME intervals  ---> chronos  ***********)

Print STPN. Print chronos.
(* increment time, for a given list of enabled transitions *)
Fixpoint increment_time
         (chronos : trans_type -> option chrono_type)
         (enabled_transs : list trans_type)
  : trans_type -> option chrono_type :=
  match enabled_transs with
  | [] => chronos
  | t :: tail => match (chronos t) with
                 | None => chronos  (* increment nothing ... *)
                 | Some (mk_chrono        (* immutable ... *)
                           mini
                           maxi
                           min_le_max
                           cpt ) =>  increment_time
                                       (fun trans =>
                                          if beq_transs
                                               trans t
                                          then Some (mk_chrono
                                                       mini
                                                       maxi
                                                       min_le_max
                                                       (cpt + 1)
                                                    (* !!! *) )
                                          else (chronos trans)
                                       )
                                       tail
                 end 
  end.
(* on incremente en debut de cycle. Avec un marquage stable 
donc on se sert d'une liste de transitions enabled, 
facilement calculable *)

Definition reset_time
           (chronos : trans_type -> option chrono_type)
           (t : trans_type)
  : trans_type -> option chrono_type :=
  match (chronos t) with
  | None  => chronos   (* reset nothing ... *)
  | Some (mk_chrono
            mini
            maxi
            min_le_max
            cpt ) => (fun trans =>
                                if beq_transs
                                     trans t
                                then Some (mk_chrono
                                             mini
                                             maxi
                                             min_le_max
                                             0   (* !!! *) )
                                else (chronos trans)
                     )             
  end.
(* le rest de compteur est plus subtile : 
 1) quand faut-il le faire ?  
   ----> a la fin du cycle ou plutot dans stpn_sub_fire_pre !
 2) pour quelles transitions faut-il le faire ?
   ----> celles desensibilisees durant le cycle. meme transitoirement
*)

(* reset time counters of several transitions ... *)
Fixpoint reset_time_list
           (chronos : trans_type -> option chrono_type)
           (list_to_reset : list trans_type)
  : trans_type -> option chrono_type :=
  match list_to_reset with
  | [] => chronos
  | t :: tail => reset_time_list
                   (reset_time
                      chronos
                      t)
                   tail
  end.


(*****************************************************************
**********   FIRING ALGORITHM    for STPN      *******************
******************************************************************)

Print STPN.
Check update_marking_pre.
(** given 1 ordered class of transitions 
in structural conflict (a list class_of_transs), 
return 1 list of transitions "subclass_half_fired" 
and marking "m_intermediate" accordingly ...   *)
Fixpoint stpn_sub_fire_pre
         (places : list place_type)
         (pre test inhib : weight_type)  (* 3 *)
         (m_init m_decreasing : marking_type)    (* 2 *)
         (* to reset clocks .. *)
         (enabled_transs : list trans_type)
         (chronos : trans_type -> option chrono_type)
         (* to reset clocks .. *)
         (class_transs subclass_half_fired : list trans_type) (* 2 *)
         (* "subclass_half_fired"  is meant to be empty at first *) 
  : (list trans_type) *
    marking_type *
    (trans_type -> option chrono_type) :=
  match class_transs with
  | t :: tail => if(
                     (pre_or_test_check
                        places
                        (pre t)
                        m_decreasing)
                       && (pre_or_test_check
                             places
                             (test t)
                             m_init)
                       && (inhib_check
                             places
                             (inhib t)
                             m_init)
                   ) (* t is enabled, even w.r.t. to the others *)
                 then
                   if    (good_time (chronos  t))
                   then
                     let new_decreasing :=
                         (update_marking_pre
                            places t pre
                            m_decreasing)
                     in
                     let new_chronos :=
                         (reset_time_list
                            chronos
                  (* disabled = enabled_before - enabled_now *) 
                            (list_disabled
                               places
                               pre test inhib
                               new_decreasing
                               enabled_transs))
                     in
                     stpn_sub_fire_pre
                       places pre test inhib
                       m_init new_decreasing 
                       enabled_transs
                       (* updating the intervals in case ... *)
                       new_chronos
                       tail (subclass_half_fired ++ [t])
                       (* concatenate t behind, keep order *)
                   else (* not goog time *)
                     stpn_sub_fire_pre
                       places pre test inhib
                       m_init m_decreasing
                       enabled_transs   chronos
                       tail subclass_half_fired 
                        (* t not fired, let's continue with tail *)
                 else  (* not enabled   w.r.t. ... *)
                   stpn_sub_fire_pre
                     places  pre  test  inhib
                     m_init  m_decreasing
                     enabled_transs    chronos
                     tail subclass_half_fired 
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

(* stpn_fire_pre 
 apply sub_fire_pre over ALL classes of transitions. 
 Begin with initial marking, 
  end with half fired marking.  
 "classes_half_fired" is empty at first 
 (a bit like for sub_fire_pre) 
 *)
Print nth. Print prior_type.
Fixpoint stpn_fire_pre
         (places : list place_type)
         (pre test inhib : weight_type)
         (marking : marking_type)
         (* ......... to reset clocks .................. *)
         (enabled_transs : list trans_type)
         (chronos : trans_type -> option chrono_type)
         (* ......... to reset clocks .................. *)
         (classes_transs  classes_half_fired : list (list trans_type))
  : (list (list trans_type)) *
    marking_type *
    (trans_type -> option chrono_type)  :=
  match classes_transs with
  | [] => (classes_half_fired , marking, chronos)
  | l :: Ltail => let '(sub_l, new_m, new_chrs) := stpn_sub_fire_pre
                                                     places
                                                     pre test inhib
                                                     marking marking
                                                     enabled_transs
                                                     chronos
                                                     l []
                  in  stpn_fire_pre
                        places
                        pre  test  inhib
                        new_m
                        enabled_transs  new_chrs
                        Ltail
                        (sub_l :: classes_half_fired)         
  end.


(*** for nice prints  only  ! debugging ..  **)
Search SPN.
Print spn_fire_pre_print. 
Print stpn_fire_pre.
Definition stpn_fire_pre_print
           (places : list place_type) (pre test inhib : weight_type)
           (marking : marking_type)
           (* ......... to reset clocks .................. *)
           (enabled_transs : list trans_type)
           (chronos : trans_type -> option chrono_type)
           (* ......... to reset clocks .................. *)
           (classes_transs : list (list trans_type))
  : (list (list trans_type)) *
    list (place_type * nat)  *
    (* chronos added, compared with SPN *)
    list (trans_type * option (nat * nat * nat)) :=
  let '(sub_Lol, m_pre, new_chronos ) := (stpn_fire_pre
                                            places 
                                            pre   test  inhib 
                                            marking
                                            enabled_transs
                                            chronos
                                            classes_transs [] )
  in
  (sub_Lol, marking2list
              places 
              m_pre ,
  intervals2list
    enabled_transs
    new_chronos).

Print spn_debug_pre.
Definition stpn_debug_pre (stpn : STPN)
  : (list (list trans_type)) *
    list (place_type * nat)  *
    list (trans_type * option (nat * nat * nat))  :=
  match stpn with
  | mk_STPN
      (mk_SPN
         places  transs  nodup_places nodup_transitions           
         pre     test    inhib        post
         marking
         (mk_prior
            Lol) )
      chronos
    =>
    stpn_fire_pre_print
      places
      pre test inhib
      marking
      (list_enabled
         places 
         pre  test  inhib 
         marking
         transs )
      chronos
      Lol
  end.

(* Returns  [transitions fired + final marking] *)
Definition stpn_fire  
           (places : list place_type)
           (pre test inhib post : weight_type)
           (m_init : marking_type)
           (* ......... to reset clocks .................. *)
           (enabled_transs : list trans_type)
           (chronos : trans_type -> option chrono_type)
           (* .......... to reset clocks ................. *)
           (classes_transs : list (list trans_type))
  : (list (list trans_type)) *
    marking_type             *
    (trans_type -> option chrono_type)  :=
  let '(sub_Lol, m_inter, new_chronos) := stpn_fire_pre
                                            places  pre test inhib 
                                            m_init
                                            enabled_transs  chronos
                                            classes_transs []
  in  (sub_Lol ,
       fire_post
         places post
         m_inter
         sub_Lol ,
       chronos ).

(* The marking and the chronos are evolving,  
but we want to see also the      fired transitions    *)
(******************************* CYCLE **********************)
Print list_enabled. Print STPN. Print SPN.
Definition stpn_cycle (stpn : STPN)           
  : (list (list trans_type)) * STPN  :=
  match stpn with
  | mk_STPN
      (mk_SPN
         places  transs  nodup_places  nodup_transitions           
         pre     post    test          inhib         
         marking
         (mk_prior
            Lol) )
      chronos
    =>
    let enabled := (list_enabled
                      places 
                      pre  test  inhib 
                      marking
                      transs )
    in
    let chronos_incr := increment_time
                          chronos 
                          enabled
    in
    let '(fired, new_m, new_chronos) := stpn_fire  
                                          places
                                          pre  test  inhib  post
                                          marking
                                          enabled (* ! *)  
                                          chronos_incr (* ! *)
                                          Lol
    in (fired ,  (* ! *)
        (mk_STPN
           (mk_SPN
              places  transs   nodup_places  nodup_transitions 
              pre     post     test          inhib
              new_m       (* ! *)
              (mk_prior
                 Lol) )
           new_chronos  (* ! *) )  )
  end.


(**************************************************)
(************* to animate a STPN   *****************)

(* n steps calculus  *)
Print STPN. Check intervals2list. Print animate_spn.
Fixpoint animate_stpn
         (stpn : STPN)
         (n : nat)
  : list
      (list (list trans_type)  *
       list (place_type * nat) *
       (list (trans_type * option (nat * nat * nat)))) :=
  match n with
  | O => [ ( [] ,
             marking2list
                    (places   (spn stpn))
                    (marking  (spn stpn)) ,
             (intervals2list
                (transs (spn stpn))
                (chronos     stpn))
         ) ]
  | S n' =>  let (Lol_fired, next_stpn) := (stpn_cycle stpn)
             in
             ( Lol_fired ,
               (marking2list
                  (places (spn   next_stpn))
                  (marking (spn  next_stpn))) ,
               (intervals2list
                  (transs (spn   next_stpn))
                  (chronos       next_stpn)) ) 
               ::
               (animate_stpn
                  next_stpn
                  n')
  end.    (* split / combine ... *)


(******************************************************************)
(***** David Andreu's first example (redrawn in my Oxford) ********)

Reset all. Print ex_places.
(* 7 places *)
Definition ex_places' : (list place_type) :=
  [ mk_place 1 ;
    mk_place 2 ;
    mk_place 3 ;
    mk_place 4 ;
    mk_place 5 ;
    mk_place 6 ;
    mk_place 7 ].
Definition ex_nodup_places' : NoDup ex_places' :=
  NoDup_nodup
    places_eq_dec
    ex_places'. 

(* 6 transitions *)
Definition ex_transs' : (list trans_type) :=
  [ mk_trans 1 ;
    mk_trans 2 ;
    mk_trans 3 ;
    mk_trans 4 ;
    mk_trans 5 ;
    mk_trans 6 ].
Definition ex_nodup_transs' : NoDup ex_transs' :=
  NoDup_nodup
    transs_eq_dec
    ex_transs'.

(* one lemma for each arc weight ...  already done*)

(* 7 arcs PT (place transition)  "incoming" *) 
Definition ex_pre' (t : trans_type) (p : place_type)
  : option nat_star :=
  match (t,p) with
  | (mk_trans 1, mk_place 1) => Some (mk_nat_star
                                        1
                                        one_positive)
  | (mk_trans 2, mk_place 1) => Some (mk_nat_star
                                        1
                                        one_positive)
  | (mk_trans 3, mk_place 3) => Some (mk_nat_star
                                        2
                                        two_positive)
  | (mk_trans 3, mk_place 4) => Some (mk_nat_star
                                        1
                                        one_positive)
  | (mk_trans 4, mk_place 5) => Some (mk_nat_star
                                        1
                                        one_positive)
  | (mk_trans 5, mk_place 2) => Some (mk_nat_star
                                        1
                                        one_positive)  
  | (mk_trans 5, mk_place 6) => Some (mk_nat_star
                                        1
                                        one_positive)
  | (mk_trans 6, mk_place 7) => Some (mk_nat_star
                                        1
                                        one_positive)
  | _ => None
  end.

Definition ex_test' (t : trans_type) (p : place_type) :=
  (* 1 arc of type "test" *)
  match (t, p) with
  | (mk_trans 2, mk_place 2) => Some (mk_nat_star
                                        1
                                        one_positive)               
  | _ => None
  end.

Definition ex_inhib' (t : trans_type) (p : place_type) :=
  (* 1 arc of type "inhibitor"  *)
  match (t, p) with
  | (mk_trans 1, mk_place 2) => Some (mk_nat_star
                                        1
                                        one_positive)               
  | _ => None
  end.

(* 7 arcs TP      "outcoming"  *)
Definition ex_post' (t : trans_type) (p : place_type)
  : option nat_star :=
  match (t, p) with
  (* trans 1 *)
  | (mk_trans 1, mk_place 2) => Some (mk_nat_star
                                        1
                                        one_positive)               
  | (mk_trans 1, mk_place 3) => Some (mk_nat_star
                                        2
                                        two_positive)               
  | (mk_trans 1, mk_place 4) => Some (mk_nat_star
                                        1
                                        one_positive)
  (* trans 2 *)
  | (mk_trans 2, mk_place 5) => Some (mk_nat_star
                                        1
                                        one_positive)
  (* trans 3 *)
  | (mk_trans 3, mk_place 7) => Some (mk_nat_star
                                        1
                                        one_positive)
  (* trans 4 *)
  | (mk_trans 4, mk_place 6) => Some (mk_nat_star
                                        1
                                        one_positive)
  (* trans 5 *)
  | (mk_trans 5, mk_place 7) => Some (mk_nat_star
                                        1
                                        one_positive)
  (* trans 6 *)
  | (mk_trans 6, mk_place 1) => Some (mk_nat_star
                                        1
                                        one_positive)
  | _ => None
  end.

(* tokens *)
Definition ex_marking' (p : place_type) :=
  match p with
  | mk_place 1 => 1
  | mk_place 2 => 0
  | mk_place 3 => 0
  | mk_place 4 => 0
  | mk_place 5 => 0
  | mk_place 6 => 0
  | mk_place 7 => 0
  | _ => 0
  end.

Print STPN. Print chrono_type. Print nat_star.
(****  intervals need lemmas and structures .... ****) 
Lemma three_positive : 3 > 0. Proof. omega. Qed.
Lemma five_positive : 5 > 0. Proof. omega. Qed.
Lemma twototheeight_positive : 256 > 0. Proof. omega. Qed.

(*
Definition three_star := mk_nat_star
                           3
                           three_positive.
Definition five_star := mk_nat_star
                           5
                           five_positive.
Definition two_star := mk_nat_star
                           2
                           two_positive.
Definition twototheeight_star := mk_nat_star
                           256
                           twototheeight_positive.
 
Lemma preuve3le5 : three_star <=i five_star. 
Proof. unfold lebi. Admitted.
Lemma preuve2le256 : two_star <=i twototheeight_star.
Proof. unfold lebi. Admitted.
 *)

Lemma preuve3le5 : 3 <= 5. 
Proof. omega. Qed.
Lemma preuve2le256 : 2 <= 256.
Proof. omega. Qed.

Definition int_3_5 := mk_chrono
                        3
                        5
                        preuve3le5
                        0.
Definition int_2_256 := mk_chrono
                          2
                          256
                          preuve2le256
                          0.

Definition ex_chronos' :
  trans_type -> option chrono_type :=
  fun trans => 
    match trans with
    | mk_trans 3  =>  Some int_3_5
    | mk_trans 5  =>  Some int_2_256
    | _ => None
    end.

Print prior_type.
Definition ex_prior' : prior_type :=
  (* se restreindre aux conflits structurels ! *)
  mk_prior
    [
      [mk_trans 1 ; mk_trans 2 ; mk_trans 5] ;
      [mk_trans 3] ;
      [mk_trans 4] ;
      [mk_trans 6]
    ].
 
    
Print pre. Print weight_type. Print STPN.
Definition ex_stpn := mk_STPN
                        (mk_SPN
                           ex_places'
                           ex_transs'
                           ex_nodup_places'
                           ex_nodup_transs'
                           
                           ex_pre'
                           ex_post'
                           ex_test'
                           ex_inhib'                 
                      
                           ex_marking'
                           ex_prior'
                        )
                        ex_chronos'.

Check ex_stpn. Compute (marking
                          (spn
                             ex_stpn)). (* initial marking *)

Search STPN.  (* stpn_cycle     stpn_debug_pre    animate_stpn *)
Compute (animate_stpn
           ex_stpn
           10).  (* 11 markings *)

Compute
  (
    stpn_debug_pre
      (
     (*   snd (stpn_cycle
               (snd (stpn_cycle
                       (snd (stpn_cycle
                               (snd (stpn_cycle  *)
                                      ex_stpn)
      
  ).

