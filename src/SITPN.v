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
Inductive condition_check_spec
          (maybe_chrono : option chrono_type)
  : Prop :=
| good_time_none : 
    maybe_chrono = None                             -> 
    condition_check_spec
      maybe_chrono
| good_time_some : forall
    (mini maxi cpt: nat)
    (min_leb_max : mini <= maxi),
    maybe_chrono = Some (mk_chrono
                           mini
                           maxi
                           min_leb_max
                           cpt )                    ->
    (mini <=? cpt)
      &&
      (cpt <=? maxi) = true              ->
    condition_check_spec
      maybe_chrono.
Functional Scheme condition_check_ind :=
  Induction for condition_check Sort Prop.
Theorem condition_check_correct : forall
    (maybe_chrono : option chrono_type),
    good_time       maybe_chrono = true     ->
    good_time_spec  maybe_chrono.
Proof.
  intros maybe_chrono.
  functional induction (good_time  maybe_chrono) using good_time_ind.
  - intro H. (* apply good_time_some with (mini:=mini0) (maxi:=maxi0) (cpt:=cpt0) (min_leb_max:=_x).
    + reflexivity.
    + exact H.
  - intro H. apply good_time_none. reflexivity.
Qed. *) Admitted.
Theorem condition_check_complete : forall
    (maybe_chrono : option chrono_type),
    good_time_spec  maybe_chrono            ->
    good_time       maybe_chrono = true.     
Proof.
  intros maybe_chrono H. elim H.
  - intro H'. unfold good_time. rewrite H'. reflexivity.
  - intros mini maxi cpt min_leb_max H1 H2.
    unfold good_time. rewrite H1. exact H2.
Qed.



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
      sitpn_class_fire_pre_aux
        places pre test inhib     m_steady
        new_decreasing     new_chronos     tail
        (subclass_half_fired ++ [t])    conditions
    else
      sitpn_class_fire_pre_aux
        places pre test inhib     m_steady
        m_decreasing  chronos  tail  subclass_half_fired  conditions
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

Inductive sitpn_class_fire_pre_aux_spec
          (places : list place_type)
          (pre   test   inhib : weight_type)  
          (m_steady     : marking_type)
  : marking_type      ->   (* m_decreasing *)
    (list trans_type) ->   (* class *)
    (list trans_type) ->   (* subclass_fired_pre *)

    (list trans_type) ->   (* subclass_fired_pre *)
     marking_type     ->   (* m_decreasing *)
    Prop :=
| class_nil : forall
    (m_decreased : marking_type)
    (subclass_fired_pre : list trans_type),
    sitpn_class_fire_pre_aux_spec
      places               pre  test  inhib
      m_steady             m_decreased 
      []                   subclass_fired_pre
      subclass_fired_pre   m_decreased
| class_cons_if :  forall
    (t : trans_type)
    (tail    subclass_fired_pre  sub : list trans_type)
    (m_decreasing_low  m_decreasing_high  m : marking_type),
    synchro_check_arcs
      places    (pre t) (test t) (inhib t)
      m_steady  m_decreasing_high
    = true
    ->
    m_decreasing_low = (update_marking_pre
                          places   t   pre   m_decreasing_high)
    ->
    stpn_class_fire_pre_aux_spec
      places                       pre  test  inhib
      m_steady                     m_decreasing_low
      tail                         (subclass_fired_pre ++ [t])
      sub                          m 
    ->
    sitpn_class_fire_pre_aux_spec
      places               pre  test  inhib
      m_steady             m_decreasing_high     
      (t::tail)            subclass_fired_pre
      sub                  m
| class_cons_else :  forall
    (t : trans_type)
    (tail   subclass_half_fired   sub : list trans_type)
    (m_decreasing   m : marking_type),
    synchro_check_arcs
      places    (pre t) (test t) (inhib t)
      m_steady  m_decreasing
    = false
    ->
    stpn_class_fire_pre_aux_spec
      places                pre  test  inhib
      m_steady              m_decreasing  
      tail                  subclass_half_fired
      sub                  m 
    ->
    sitpn_class_fire_pre_aux_spec
      places                pre  test  inhib
      m_steady              m_decreasing     
      (t::tail)             subclass_half_fired
      sub                  m.

Functional Scheme sitpn_class_fire_pre_aux_ind :=
  Induction for sitpn_class_fire_pre_aux   Sort Prop.
Theorem sitpn_class_fire_pre_aux_correct :
  forall (places : list place_type)
         (pre  test  inhib : weight_type)
         (m_steady      m_decreasing      m_final : marking_type)
         (class_transs  subclass_fired_pre  sub_final : list trans_type),
    spn_class_fire_pre_aux
      places    pre   test   inhib   
      m_steady     m_decreasing       
      class_transs subclass_fired_pre 
    = (sub_final, m_final)
    ->
    spn_class_fire_pre_aux_spec
      places          pre   test  inhib   
      m_steady        m_decreasing         
      class_transs    subclass_fired_pre
      sub_final       m_final.
Proof. 
  intros places pre test inhib  m_steady  m_decreasing m_final
  class_transs subclass_fired_pre  sub_final.
  functional induction (spn_class_fire_pre_aux
                          places  pre test inhib
                          m_steady  m_decreasing
                          class_transs  subclass_fired_pre)
             using spn_class_fire_pre_aux_ind.
  - intro H.
    assert (Hleft :  subclass_half_fired = sub_final).
    { inversion  H. reflexivity. } (* useful ? *)
    assert (Hright :   m_decreasing = m_final).
    { inversion  H. reflexivity. }
    rewrite Hright. rewrite Hleft. (* apply class_nil.
  - intro H.
    apply class_cons_if
      with (m_decreasing_low := (update_marking_pre
                                   places t pre m_decreasing)).
    + apply e0.
    + reflexivity.
    + apply (IHp H).      
  - intro H. apply class_cons_else.
    + apply e0.
    + apply (IHp H).
Qed. *) Admitted.
Theorem sitpn_class_fire_pre_aux_complete :
  forall (places : list place_type)
         (pre  test  inhib : weight_type)
         (m_steady   m_decreasing     m_final : marking_type)
         (class_transs  subclass_fired_pre  sub_final : list trans_type),
    spn_class_fire_pre_aux_spec
      places               pre test inhib   
      m_steady             m_decreasing         
      class_transs         subclass_fired_pre
      sub_final   m_final
    ->
    spn_class_fire_pre_aux
      places          pre test inhib   
      m_steady        m_decreasing       
      class_transs    subclass_fired_pre 
    = (sub_final , m_final).
Proof.
  intros. elim H.
  - simpl. reflexivity.
  - intros. simpl.
    rewrite H0. rewrite <- H1. rewrite H3. (* reflexivity.
  - intros. simpl. rewrite H0. rewrite H2.  reflexivity. 
Qed. *) Admitted.



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

Inductive sitpn_class_fire_pre_spec
          (places : list place_type)
          (pre   test   inhib : weight_type)  
          (m_steady    m_decreasing    : marking_type)
          (class_transs : list trans_type)
  : (list trans_type) ->
    marking_type ->
    Prop :=
| sitpn_sub_fire_pre_mk :
    forall (subclass_fired_pre : list trans_type)
           (m_fired_pre_class : marking_type),
      spn_class_fire_pre_aux
        places          pre    test    inhib
        m_steady        m_decreasing
        class_transs    []
      = (subclass_fired_pre, m_fired_pre_class)
      ->
      sitpn_class_fire_pre_spec
        places          pre  test  inhib
        m_steady        m_decreasing     
        class_transs
        subclass_fired_pre  m_fired_pre_class
.

Functional Scheme sitpn_class_fire_pre_ind :=
  Induction for sitpn_class_fire_pre   Sort Prop.
Theorem sitpn_class_fire_pre_correct :
  forall (places : list place_type)
         (pre  test  inhib : weight_type)
         (m_steady   m_decreasing     m_decreased : marking_type)
         (class_transs     subclass_fired_pre  : list trans_type),
    spn_class_fire_pre
      places        pre test inhib   
      m_steady      m_decreasing       
      class_transs       
    = (subclass_fired_pre, m_decreased)
    ->
    spn_class_fire_pre_spec
      places        pre test inhib   
      m_steady      m_decreasing         
      class_transs
      subclass_fired_pre    m_decreased.
Proof.
  intros places pre test inhib m_steady m_decreasing m_decreased
         class_transs  subclass_fired_pre H.
  functional induction (spn_class_fire_pre
                          places  pre test inhib
                          m_steady  m_decreasing
                          class_transs)
             using spn_class_fire_pre_ind.
  apply spn_sub_fire_pre_mk. assumption.
Qed. 
Theorem sitpn_class_fire_pre_complete :
  forall (places : list place_type)
         (pre  test  inhib : weight_type)
         (m_steady   m_decreasing     m_decreased : marking_type)
         (class_transs    subclass_fired_pre  : list trans_type),
    spn_class_fire_pre_spec
      places         pre test inhib   
      m_steady       m_decreasing         
      class_transs
      subclass_fired_pre    m_decreased
    ->
    spn_class_fire_pre
      places         pre test inhib   
      m_steady       m_decreasing       
      class_transs
    = (subclass_fired_pre, m_decreased).
Proof.
  intros. elim H.
  intros. unfold spn_class_fire_pre. assumption.
Qed.


(*****************************************************************
 ***********  from class to  classes *****************************)

(*********************** sitpn_fire_pre_aux *********
 Apply sub_fire_pre over ALL classes of transitions. 
 Begin with initial marking, 
  end with half fired marking.  
 "classes_half_fired" is meant to be empty at first .. 
 *)
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

Inductive sitpn_fire_pre_aux_spec
          (places : list place_type)
          (pre test inhib : weight_type)
          (m_steady  : marking_type)
  : marking_type             ->  (* build_m_decreasing *)
    list (list trans_type)   ->  (* classes   *)
    list (list trans_type)   ->  (* buil_classes_fired_pre *)

    list (list trans_type)   ->  (* classes_fired_pre *)
    marking_type             ->  (* m_decreasing *)
    Prop :=
| classes_nil : forall
    (classes_fired_pre : list (list trans_type))
    (m_decreased : marking_type),
    sitpn_fire_pre_aux_spec
      places               pre   test  inhib
      m_steady             m_decreased
      []                   classes_fired_pre    
      classes_fired_pre    m_decreased
| classes_cons : forall
    (classes_tail classes_fired_pre_tail C : list (list trans_type))
    (class     class_fired_pre : list trans_type)
    (m_decreased_class   m_decreasing  m_any  : marking_type),
    (class_fired_pre, m_decreased_class) =
    (spn_class_fire_pre
       places     pre  test  inhib
       m_steady   m_decreasing
       class)
    ->
    spn_fire_pre_aux_spec
      places              pre   test   inhib
      m_steady            m_decreased_class
      classes_tail        (class_fired_pre ::
                                           classes_fired_pre_tail)
      C                   m_any
    ->
    sitpn_fire_pre_aux_spec
      places                  pre   test   inhib
      m_steady                m_decreasing
      (class :: classes_tail) classes_fired_pre_tail
      C                       m_any
.

Functional Scheme sitpn_fire_pre_aux_ind :=
  Induction for sitpn_fire_pre_aux   Sort Prop.
Theorem sitpn_fire_pre_aux_correct :
  forall (places : list place_type)
         (pre   test  inhib : weight_type)
         (m_steady  m_decreasing  m_decreased : marking_type)
         (classes_transs   classes_fired_pre_growing
                           classes_fired_pre : list (list trans_type)),
    spn_fire_pre_aux
      places             pre   test  inhib
      m_steady           m_decreasing 
      classes_transs     classes_fired_pre_growing
    = (classes_fired_pre, m_decreased)
    ->
    spn_fire_pre_aux_spec
      places             pre   test  inhib
      m_steady           m_decreasing
      classes_transs     classes_fired_pre_growing
      classes_fired_pre  m_decreased.
Proof.
  do 10 intro. (*
  functional induction (spn_fire_pre_aux
                          places0         pre0 test0 inhib0
                          m_steady        m_decreasing
                          classes_transs  classes_fired_pre_growing)
             using spn_fire_pre_aux_ind.
  - intro H.
    assert (Hleft :  classes_fired_pre0 = classes_fired_pre).
    { inversion  H. reflexivity. } 
    assert (Hright :   m_decreasing = m_decreased).
    { inversion  H. reflexivity. }
    rewrite Hright. rewrite Hleft. apply classes_nil.
  - intro H.
    apply classes_cons
      with (class_fired_pre := fst(spn_class_fire_pre
                                     places0 pre0 test0 inhib0
                                     m_steady
                                     m_decreasing class))
           (m_decreased_class := snd(spn_class_fire_pre
                                       places0 pre0 test0 inhib0
                                       m_steady
                                       m_decreasing class)).
    + rewrite e0. reflexivity.
    + rewrite e0. simpl. apply (IHp H).
Qed. *) Admitted.
Theorem sitpn_fire_pre_aux_complete :
  forall (places : list place_type)
         (pre   test  inhib : weight_type)
         (m_steady  m_decreasing  m_decreased : marking_type)
         (classes_transs   classes_fired_pre_growing
                           classes_fired_pre : list (list trans_type)),
    spn_fire_pre_aux_spec
      places             pre   test  inhib
      m_steady           m_decreasing
      classes_transs     classes_fired_pre_growing
      classes_fired_pre  m_decreased
    -> 
    spn_fire_pre_aux
      places             pre   test  inhib
      m_steady           m_decreasing 
      classes_transs     classes_fired_pre_growing
    = (classes_fired_pre, m_decreased).
Proof.
  intros. elim H.
  -  intros. simpl. reflexivity.
  -  intros. simpl. (* rewrite <- H0. apply H2.
Qed. *) Admitted.





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

Inductive sitpn_fire_pre_spec
         (places : list place_type)
         (pre test inhib : weight_type)
         (m_steady : marking_type)
         (classes_transs  : list (list trans_type))
  : (list (list trans_type)) ->
    marking_type ->
    Prop :=
| spn_fire_pre_mk :
    forall (classes_fired_pre : list (list trans_type))
           (m_inter : marking_type),
      spn_fire_pre_aux
        places           pre    test    inhib
        m_steady         m_steady
        classes_transs   []
      = (classes_fired_pre, m_inter)
      ->
      sitpn_fire_pre_spec
        places              pre  test  inhib
        m_steady            classes_transs
        classes_fired_pre   m_inter
.
Functional Scheme sitpn_fire_pre_ind :=
  Induction for sitpn_fire_pre   Sort Prop.
Theorem sitpn_fire_pre_correct :
  forall (places : list place_type)
         (pre  test  inhib : weight_type)
         (m_steady   m_inter : marking_type)
         (classes_transs  subclasses_fired_pre : list (list trans_type)),
    spn_fire_pre
      places           pre   test   inhib   
      m_steady         classes_transs  
    = (subclasses_fired_pre, m_inter)
    ->
    spn_fire_pre_spec
      places           pre test inhib   
      m_steady         classes_transs
      subclasses_fired_pre    m_inter.
Proof.
  do 8 intro. (*
  functional induction (spn_fire_pre
                          places0      pre0 test0 inhib0
                          m_steady     classes_transs)
             using spn_fire_pre_ind.
  apply spn_fire_pre_mk. 
Qed. *) Admitted.
Theorem sitpn_fire_pre_complete :
  forall (places : list place_type)
         (pre  test  inhib : weight_type)
         (m_steady   m_inter : marking_type)
         (classes_transs  subclasses_fired_pre : list (list trans_type)),
    spn_fire_pre_spec
      places           pre test inhib   
      m_steady         classes_transs
      subclasses_fired_pre    m_inter
    ->
    spn_fire_pre
      places           pre   test   inhib   
      m_steady         classes_transs  
    = (subclasses_fired_pre, m_inter).
Proof.
  intros. elim H.
  intros. unfold spn_fire_pre. assumption.
Qed.




(*********************************************************)
(******* for  DEBUGGING  only  ..  ***********************)
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

Inductive sitpn_fire_spec   
          (places : list place_type)
          (pre test inhib post : weight_type)
          (m_steady : marking_type)
          (classes_transs : list (list trans_type))
  : (list (list trans_type))   ->
    marking_type               ->
    Prop :=
| spn_fire_mk :  forall
    (sub_Lol : list (list trans_type))
    (m_inter   m  : marking_type),
    (sub_Lol, m_inter) = spn_fire_pre
                           places  pre test inhib 
                           m_steady   classes_transs
    ->
    m = fire_post
          places post   m_inter  sub_Lol
    ->
    sitpn_fire_spec   
      places         pre test inhib post
      m_steady       classes_transs
      sub_Lol    m.

Functional Scheme sitpn_fire_ind :=
  Induction for  sitpn_fire   Sort Prop.
Theorem sitpn_fire_correct :
  forall (places : list place_type)
         (pre  test  inhib   post : weight_type)
         (m_steady   m_next : marking_type)
         (classes_transs   sub_Lol : list (list trans_type)),
    spn_fire
      places   pre  test  inhib  post
      m_steady  classes_transs   =  (sub_Lol, m_next)
    ->
    spn_fire_spec
      places   pre  test  inhib  post
      m_steady   classes_transs   sub_Lol  m_next.
Proof.
  do 9 intro. (*
  functional induction (spn_fire
                          places0       pre0 test0 inhib0 post0
                          m_steady  classes_transs)
             using spn_fire_ind.
  intro H.
  assert (Hleft : sub_Lol0 = sub_Lol).
  { inversion  H. reflexivity. } 
  assert (Hright :  fire_post
                      places0 post0 m_inter sub_Lol0 = m_next).
  { inversion  H. reflexivity. }
  apply spn_fire_mk with (m_inter := m_inter).
  - rewrite Hleft in e. rewrite e. reflexivity.
  - rewrite <- Hright. rewrite Hleft. reflexivity.
Qed. *) Admitted.
Theorem sitpn_fire_complete :
  forall (places : list place_type)
         (pre  test  inhib   post : weight_type)
         (m_steady   m_next : marking_type)
         (classes_transs   sub_Lol : list (list trans_type)),
    spn_fire_spec
      places   pre  test  inhib  post
      m_steady   classes_transs   sub_Lol  m_next
    ->
    spn_fire
      places   pre  test  inhib  post
      m_steady  classes_transs   =  (sub_Lol, m_next).
Proof.
  intros. elim H.
  intros. unfold spn_fire. rewrite <- H0. rewrite H1. reflexivity.
Qed.

(***************************************************************)
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

Inductive sitpn_cycle_spec
          (spn : SPN) :
  list (list trans_type)    ->
  SPN                       ->
  Prop :=
| spn_fired_mk : forall
    (sub_Lol  Lol: list (list trans_type))
    (final_m   m : marking_type)
    (next_spn : SPN)
    (places : list place_type)
    (transs : list trans_type)
    (pre  post test inhib : weight_type),
    spn = (mk_SPN
             places  transs  
             pre  post test inhib
             m
             (mk_prior
               Lol))
    ->
    (sub_Lol, final_m) = (spn_fire
                            places 
                            pre  test  inhib  post
                            m
                            Lol)
    ->
    next_spn = mk_SPN
                 places   transs  
                 pre      post    test   inhib
                 final_m
                 (mk_prior
                    Lol)
    -> 
    sitpn_cycle_spec
      spn   sub_Lol  next_spn.

Functional Scheme sitpn_cycle_ind :=
  Induction for sitpn_cycle   Sort Prop.
Theorem sitpn_fired_correct :
  forall (spn  next_spn : SPN)
         (sub_Lol : list (list trans_type)),
    spn_fired
      spn    =  (sub_Lol, next_spn)
    ->
    spn_fired_spec
      spn   sub_Lol  next_spn.
Proof.
  intros  spn  next_spn  sub_Lol.
  functional induction (spn_fired spn)
             using spn_fired_ind. (*
  intro H. apply spn_fired_mk
             with (Lol:=Lol0) (final_m:=final_m) (m:=m)
                  (places:=places0) (transs:=transs0)
                  (pre:=pre0) (post:=post0) (test:=test0) (inhib:=inhib0).
  - reflexivity.
  - assert (Hleft : sub_Lol0 = sub_Lol).
  { inversion  H. reflexivity. } 
  rewrite <- Hleft. rewrite e1. reflexivity.
  - inversion H. reflexivity.
Qed. *) Admitted.
Theorem sitpn_fired_complete :
 forall (spn  next_spn : SPN)
        (sub_Lol : list (list trans_type)),
   spn_fired_spec
     spn   sub_Lol  next_spn
   ->
   spn_fired
      spn    =  (sub_Lol, next_spn).
Proof.
  intros. elim H.
  intros. unfold spn_fired. rewrite  H0. rewrite <- H1.
  rewrite H2. reflexivity.
Qed.


(**************************************************)
(************* to animate a SITPN   *****************)

(* n steps calculus  *)
Print SITPN. Check intervals2list.
Fixpoint sitpn_animate
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
               (sitpn_animate
                  next_sitpn
                  n')
  end.

Inductive sitpn_animate_spec
          (spn : SPN)
  : nat ->
    list
      (list (list trans_type)  *
       list (place_type * nat) ) -> Prop :=
| animate_spn_O : sitpn_animate_spec
                    spn   O  [ ( [] , [] ) ]
| animate_spn_S :
    forall (next_spn : SPN)
           (Lol_fired : list (list trans_type))
           (m_visuel : list (place_type * nat))
           (n : nat)
           (TAIL : list (list (list trans_type) * list (place_type * nat))),
     
      (Lol_fired, next_spn) = spn_fired spn
      ->
      m_visuel = marking2list
                   (marking next_spn)   (places next_spn)
      ->
      spn_animate_spec
        next_spn    n    TAIL
      -> 
      sitpn_animate_spec
        spn   (S n)   ((Lol_fired, m_visuel) :: TAIL).

Functional Scheme sitpn_animate_ind :=
  Induction for sitpn_animate   Sort Prop.
Theorem sitpn_animate_correct :
  forall (spn   : SPN)
         (n : nat)
         (truc : list (list (list trans_type)  *
                       list (place_type * nat) )),
    spn_animate
      spn    n   =  truc
    ->
    spn_animate_spec
      spn    n     truc.
Proof.
  intros spn n.
  functional induction (spn_animate spn n)
             using spn_animate_ind.
  - intros truc H. rewrite <- H. (* apply animate_spn_O.
  - intros truc H. rewrite <- H.
    apply animate_spn_S with (next_spn := snd (spn_fired spn)).
    + rewrite e0. simpl. reflexivity.
    + rewrite e0. simpl. reflexivity.
    + rewrite e0. simpl.
      apply (IHl (spn_animate next_spn n')). reflexivity.
Qed. *) Admitted.
Theorem sitpn_animate_complete :
  forall (spn   : SPN)
         (n : nat)
         (truc : list (list (list trans_type)  *
                       list (place_type * nat) )),
    spn_animate_spec
      spn    n     truc
    ->
    spn_animate
      spn    n   =  truc.
Proof.
  intros. elim H.
  - simpl. (* reflexivity. 
  - intros. simpl. rewrite <- H0. rewrite <- H1. rewrite <- H3.
    reflexivity.
Qed. *)  Admitted.

