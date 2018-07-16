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
          (conditions : conditions_type)
          (t : trans_type)
  : Prop :=
| condition_check_none : 
    (conditions t) = None                             -> 
    condition_check_spec
      conditions  t
| condition_check_some_if : 
    (conditions t) = Some true 
    ->
    condition_check_spec
      conditions  t.
Functional Scheme condition_check_ind :=
  Induction for condition_check Sort Prop.
Theorem condition_check_correct : forall
    (conditions : conditions_type)
    (t : trans_type),
    (condition_check
      conditions t)  = true
    ->
    (condition_check_spec
       conditions t).
Proof.
  intros conditions t.
  functional induction (condition_check  conditions t) using condition_check_ind.
  - intro H. apply condition_check_some_if. rewrite e. rewrite H.
    reflexivity.
  - intro H. apply condition_check_none. assumption.
Qed.
Theorem condition_check_complete : forall
    (conditions : conditions_type)
    (t : trans_type),
    (condition_check_spec
       conditions t)                    ->
    (condition_check
      conditions t)  = true.    
Proof.
  intros conditions t H. elim H.
  - intro H'. unfold condition_check. rewrite H'. reflexivity.
  - intro H'. unfold condition_check. rewrite H'. reflexivity.
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

(*
Print synchro_check_arcs. 
Inductive stpn_class_fire_pre_aux_spec
          (whole_class : list trans_type)
          (places : list place_type)
          (pre   test   inhib : weight_type)  
          (m_steady     : marking_type)
  : marking_type                          ->   (* m_decreasing *)
    (trans_type -> option chrono_type)    ->  (* chronos *)
    (list trans_type)                     ->   (* class *)
    (list trans_type)               ->   (* subclass_fired_pre *)
    
      
    (list trans_type)           ->   (* subclass_fired_pre *)
    marking_type                       ->   (* m_decreasing *)
    (trans_type -> option chrono_type)    ->  (* chronos *)
    Prop :=
| class_nil : forall
    (m_decreased : marking_type)
    (subclass_fired_pre : list trans_type)
    (chronos : trans_type -> option chrono_type),
    stpn_class_fire_pre_aux_spec
      whole_class    places       pre  test  inhib
      m_steady             
      m_decreased          chronos
      []                   subclass_fired_pre
      subclass_fired_pre   m_decreased     chronos
| class_cons_if :  forall
    (t : trans_type)
    (tail    subclass_fired_pre  sub : list trans_type)
    (m_decreasing_low  m_decreasing_high  m : marking_type)
    (chronos  new_chronos   chronos_final : trans_type -> option chrono_type),
    synchro_check_arcs
      places    (pre t) (test t) (inhib t)
      m_steady  m_decreasing_high
    = true   /\     good_time (chronos  t) = true
    -> 
    m_decreasing_low = (update_marking_pre
                          places   t   pre   m_decreasing_high)
    ->
     new_chronos =
     (reset_time_disabled
        chronos
        (not_synchro_check_list
           whole_class   places     pre    test    inhib
           m_steady       m_decreasing_low))
    ->    
    stpn_class_fire_pre_aux_spec
      whole_class     places      pre  test  inhib
      m_steady
      m_decreasing_low             new_chronos
      tail                         (subclass_fired_pre ++ [t])
      sub                          m     chronos_final
    ->
    stpn_class_fire_pre_aux_spec
      whole_class     places     pre  test  inhib
      m_steady
      m_decreasing_high    chronos
      (t::tail)            subclass_fired_pre
      sub                  m           chronos_final
| class_cons_else :  forall
    (t : trans_type)
    (tail   subclass_half_fired   sub : list trans_type)
    (m_decreasing   m : marking_type)
    (chronos     chronos_final : trans_type -> option chrono_type),
    synchro_check_arcs
      places    (pre t) (test t) (inhib t)
      m_steady  m_decreasing
    = false   \/     good_time (chronos  t) = false
    ->
    stpn_class_fire_pre_aux_spec
      whole_class     places      pre  test  inhib
      m_steady
      m_decreasing          chronos 
      tail                  subclass_half_fired
      sub                   m       chronos_final
    ->
    stpn_class_fire_pre_aux_spec
      whole_class     places      pre  test  inhib
      m_steady
      m_decreasing          chronos     
      (t::tail)             subclass_half_fired
      sub                  m   chronos_final.

Functional Scheme sitpn_class_fire_pre_aux_ind :=
  Induction for sitpn_class_fire_pre_aux   Sort Prop.

Theorem stpn_class_fire_pre_aux_correct : forall
    (whole_class : list trans_type)
    (places : list place_type)
    (pre  test  inhib : weight_type)
    (m_steady      m_decreasing      m_final : marking_type)
    (class_transs  subclass_fired_pre  sub_final : list trans_type)
    (chronos chronos_final : trans_type -> option chrono_type),
    stpn_class_fire_pre_aux
      whole_class     places         pre   test   inhib   
      m_steady
      m_decreasing    chronos      
      class_transs   subclass_fired_pre 
    = (sub_final, m_final, chronos_final)
    ->
    stpn_class_fire_pre_aux_spec
      whole_class     places          pre   test  inhib   
      m_steady
      m_decreasing    chronos     
      class_transs    subclass_fired_pre
      sub_final       m_final   chronos_final.
Proof.
  intros whole_class  places  pre test inhib  m_steady
         m_decreasing  m_final
         class_transs   subclass_fired_pre    sub_final
         chronos  chronos_final.
  functional induction 
             (stpn_class_fire_pre_aux
                whole_class places  pre test inhib
                m_steady  m_decreasing    chronos 
                class_transs  subclass_fired_pre)
             using stpn_class_fire_pre_aux_ind.
  - intro H.     
    assert (Hleft :  subclass_half_fired = sub_final).
    { inversion  H. reflexivity. } (* useful ? *)
    assert (Hmiddle :   m_decreasing = m_final).
    { inversion  H. reflexivity. }
    assert (Hright :  chronos =  chronos_final).
    { inversion  H. reflexivity. } (* useful ? *)
    rewrite Hleft. rewrite Hmiddle. rewrite Hright.
    apply class_nil.
  - intro H.
    apply class_cons_if
      with (m_decreasing_low := (update_marking_pre
                                   places t pre m_decreasing))
           (new_chronos :=
              (reset_time_disabled
                 chronos
                 (not_synchro_check_list
                    whole_class   places     pre    test    inhib
                    m_steady    (update_marking_pre
                                   places t pre m_decreasing)))).
    + apply andb_prop. assumption. 
(*      assert (H' : synchro_check_arcs
                     places (pre t) (test t) 
                     (inhib t)  m_steady  m_decreasing = true /\
                   good_time (chronos0 t) = true).
      { apply andb_prop. apply e0. }  *) 
    + reflexivity.
    + reflexivity.
    + apply (IHp H).      
  - intro H. apply class_cons_else.
    + apply andb_false_iff. assumption. 
    + apply (IHp H).
Qed. 
Theorem stpn_class_fire_pre_aux_complete :  forall
    (whole_class : list trans_type)
    (places : list place_type)
    (pre  test  inhib : weight_type)
    (m_steady   m_decreasing     m_final : marking_type)
    (class_transs  subclass_fired_pre  sub_final : list trans_type)
    (chronos chronos_final : trans_type -> option chrono_type),
    stpn_class_fire_pre_aux_spec
      whole_class      places               pre test inhib   
      m_steady
      m_decreasing        chronos 
      class_transs         subclass_fired_pre
      sub_final   m_final    chronos_final
    ->
    stpn_class_fire_pre_aux
      whole_class      places          pre test inhib   
      m_steady
      m_decreasing    chronos       
      class_transs    subclass_fired_pre 
    = (sub_final , m_final, chronos_final).
Proof.
  intros. elim H.
  - simpl. reflexivity.
  - intros. simpl.
    assert (H0' : synchro_check_arcs
                    places (pre t) (test t) 
                    (inhib t) m_steady m_decreasing_high &&
                    good_time (chronos1 t) = true).
      { apply andb_true_iff. assumption. }  
      rewrite H0'. rewrite <- H1. rewrite <- H2. rewrite H4.
      reflexivity.
  - intros. simpl.
    assert (H0' : synchro_check_arcs
                    places (pre t) (test t) 
                    (inhib t) m_steady m_decreasing0 &&
                    good_time (chronos1 t) = false).
      { apply andb_false_iff. assumption. } 
    rewrite H0'. rewrite H2.  reflexivity. 
Qed.
 *)

(****** sitpn_class_fire_pre_aux ---> sitpn_class_fire_pre  *****)

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


Inductive stpn_class_fire_pre_spec
          (places : list place_type)
          (pre   test   inhib : weight_type)  
          (m_steady    m_decreasing    : marking_type)
          (chronos  :  trans_type -> option chrono_type)
          (class_transs : list trans_type)
  : (list trans_type)                     ->
    marking_type                          ->
    (trans_type -> option chrono_type)    ->
    Prop :=
| stpn_sub_fire_pre_mk :
    forall (subclass_fired_pre : list trans_type)
           (m_fired_pre_class : marking_type)
           (chronos_final: trans_type -> option chrono_type),
      stpn_class_fire_pre_aux
        class_transs     places          pre    test    inhib
        m_steady
        m_decreasing     chronos
        class_transs    []
      = (subclass_fired_pre, m_fired_pre_class, chronos_final)
      ->
      stpn_class_fire_pre_spec
        places          pre  test  inhib
        m_steady
        m_decreasing        chronos            class_transs
        subclass_fired_pre  m_fired_pre_class  chronos_final
.
(*
Functional Scheme stpn_class_fire_pre_ind :=
  Induction for stpn_class_fire_pre   Sort Prop.
Theorem stpn_class_fire_pre_correct : forall
    (places : list place_type)
    (pre  test  inhib : weight_type)
    (m_steady   m_decreasing     m_decreased : marking_type)
    (class_transs     subclass_fired_pre  : list trans_type)
    (chronos chronos_final: trans_type -> option chrono_type),
    stpn_class_fire_pre
      places    pre    test    inhib
      m_steady
      m_decreasing   chronos     class_transs
    = (subclass_fired_pre, m_decreased, chronos_final)
    ->
    stpn_class_fire_pre_spec
      places          pre  test  inhib
      m_steady
      m_decreasing        chronos            class_transs
      subclass_fired_pre  m_decreased  chronos_final.
Proof.
  intros places pre test inhib m_steady m_decreasing m_decreased
         class_transs  subclass_fired_pre chronos chronos_final H.
  functional induction (stpn_class_fire_pre
                          places    pre test inhib
                          m_steady  m_decreasing
                          chronos   class_transs)
             using stpn_class_fire_pre_ind.
  apply stpn_sub_fire_pre_mk. assumption.
Qed. 
Theorem stpn_class_fire_pre_complete : forall
    (places : list place_type)
    (pre  test  inhib : weight_type)
    (m_steady   m_decreasing     m_decreased : marking_type)
    (class_transs     subclass_fired_pre  : list trans_type)
    (chronos chronos_final: trans_type -> option chrono_type),
    stpn_class_fire_pre_spec
      places          pre  test  inhib
      m_steady
      m_decreasing        chronos            class_transs
      subclass_fired_pre  m_decreased  chronos_final
    -> 
    stpn_class_fire_pre
      places    pre    test    inhib
      m_steady
      m_decreasing   chronos     class_transs
    = (subclass_fired_pre, m_decreased, chronos_final).
Proof.
  intros. elim H.
  intros. unfold stpn_class_fire_pre. assumption.
Qed.
*)

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

Inductive stpn_fire_pre_aux_spec
          (places : list place_type)
          (pre test inhib : weight_type)
          (m_steady  : marking_type)
  : marking_type             ->  (* m_decreasing *)
    list (list trans_type)   ->  (* classes   *)
    list (list trans_type)   ->  (* classes_fired_pre *)
    (trans_type -> option chrono_type)     ->     (* chronos *)
    list (list trans_type)   ->  (* classes_fired_pre *)
    marking_type             ->  (* m_decreasing *)
    (trans_type -> option chrono_type)     ->     (* chronos *)
    Prop :=
| classes_nil : forall
    (classes_fired_pre : list (list trans_type))
    (m_decreased : marking_type)
    (chronos : trans_type -> option chrono_type)
  ,
    stpn_fire_pre_aux_spec
      places               pre   test  inhib
      m_steady
      m_decreased      []       classes_fired_pre    chronos 
      classes_fired_pre    m_decreased          chronos
| classes_cons : forall
    (classes_tail classes_fired_pre_tail C : list (list trans_type))
    (class     class_fired_pre : list trans_type)
    (m_decreased   m_decreasing  m_any  : marking_type)
    (chronos   chronos_final  any_chronos : trans_type ->
                                            option chrono_type),
    stpn_class_fire_pre
      places          pre    test    inhib
      m_steady
      m_decreasing   chronos     class
    = (class_fired_pre, m_decreased, chronos_final)
    ->
    stpn_fire_pre_aux_spec
      places          pre   test   inhib
      m_steady
      m_decreased      classes_tail
      (class_fired_pre :: classes_fired_pre_tail)
      chronos     C     m_any    any_chronos
    ->
    stpn_fire_pre_aux_spec
      places                  pre   test   inhib
      m_steady
      m_decreasing
      (class :: classes_tail) classes_fired_pre_tail
      chronos    C      m_any   any_chronos.

Functional Scheme sitpn_fire_pre_aux_ind :=
  Induction for sitpn_fire_pre_aux   Sort Prop.


Section projections3.
  Context {A : Type} {B : Type} {C : Type}.

  Definition premz (p:A * B * C) := match p with
                                  | (x, y, z) => x
                                  end.
  Definition deuz (p:A * B * C) := match p with
                                  | (x, y, z) => y
                                  end. 
  Definition troiz (p:A * B * C) := match p with
                                    | (x, y, z) => z
                                    end.
End projections3.

(*
Theorem stpn_fire_pre_aux_correct :  forall
    (places : list place_type)
    (pre   test  inhib : weight_type)
    (m_steady  m_decreasing  m_decreased : marking_type)
    (classes_transs   classes_fired_pre_rec
                      classes_fired_pre : list (list trans_type))
    (chronos   chronos_final  : trans_type -> option chrono_type),
    stpn_fire_pre_aux
      places             pre   test  inhib
      m_steady           m_decreasing 
      chronos     classes_transs     classes_fired_pre_rec
    = (classes_fired_pre, m_decreased, chronos_final)
    ->
    stpn_fire_pre_aux_spec
      places              pre   test   inhib
      m_steady            m_decreasing
      classes_transs      classes_fired_pre_rec
      chronos    classes_fired_pre    m_decreased chronos_final.
Proof.
  do 12 intro.
  functional induction
             (stpn_fire_pre_aux
                places pre test inhib m_steady m_decreasing
                chronos0 classes_transs classes_fired_pre_rec)
             using stpn_fire_pre_aux_ind.
  - intro H. 
    assert (Hleft :  classes_half_fired = classes_fired_pre).
    { inversion  H. reflexivity. } 
    assert (Hmiddle :  m_decreasing = m_decreased).
    { inversion  H. reflexivity. }
    assert (Hright :  chronos0   = chronos_final).
    { inversion  H. reflexivity. } 
    rewrite Hleft. rewrite Hright. rewrite Hmiddle.
    apply classes_nil.
  - intro H.
    apply classes_cons
      with (class_fired_pre := premz (stpn_class_fire_pre
                                      places pre test inhib
                                      m_steady
                                      m_decreasing chronos0 class))
           (m_decreased := deuz (stpn_class_fire_pre
                                  places pre test inhib
                                  m_steady
                                  m_decreasing chronos0 class))
           (chronos_final := troiz (stpn_class_fire_pre
                                      places pre test inhib
                                      m_steady
                                      m_decreasing chronos0 class)).
    + rewrite e0. simpl. reflexivity.
    + rewrite e0. simpl. (* apply (IHp H). *)

      (* spec  not correct *)
Admitted.
Theorem stpn_fire_pre_aux_complete : forall
    (places : list place_type)
    (pre   test  inhib : weight_type)
    (m_steady  m_decreasing  m_decreased : marking_type)
    (classes_transs   classes_fired_pre_rec
                      classes_fired_pre : list (list trans_type))
    (chronos   chronos_final  : trans_type -> option chrono_type),
    stpn_fire_pre_aux_spec
      places              pre   test   inhib
      m_steady            m_decreasing
      classes_transs      classes_fired_pre_rec
      chronos    classes_fired_pre    m_decreased chronos_final
    ->
    stpn_fire_pre_aux
      places             pre   test  inhib
      m_steady           m_decreasing 
      chronos     classes_transs     classes_fired_pre_rec
    = (classes_fired_pre, m_decreased, chronos_final).    
Proof.
  intros. elim H.
  -  intros. simpl. reflexivity.
  -  intros. simpl. rewrite H0. rewrite <- H2.

     (* spec  not correct  *)
 Admitted. About stpn_fire_pre_aux_complete.
*)


(***  sitpn_fire_pre_aux  --->  sitpn_fire_pre_aux   *****) 

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

Inductive stpn_fire_pre_spec
         (places : list place_type)
         (pre test inhib : weight_type)
         (m_steady : marking_type)
         (chronos : trans_type -> option chrono_type)
         (classes_transs  : list (list trans_type))
  : (list (list trans_type)) ->
    marking_type ->
    (trans_type -> option chrono_type)   ->
    Prop :=
| spn_fire_pre_mk :
    forall (classes_fired_pre : list (list trans_type))
           (m_inter : marking_type)
           (chronos_next  : trans_type ->   option chrono_type),
      stpn_fire_pre_aux
        places           pre    test    inhib
        m_steady
        m_steady   chronos        classes_transs   []
      = (classes_fired_pre, m_inter,  chronos_next)
      ->
      stpn_fire_pre_spec
        places              pre  test  inhib
        m_steady
        chronos                 classes_transs
        classes_fired_pre   m_inter    chronos_next.

Functional Scheme sitpn_fire_pre_ind :=
  Induction for sitpn_fire_pre   Sort Prop.

(*
Theorem stpn_fire_pre_correct :  forall
    (places : list place_type)
    (pre   test  inhib : weight_type)
    (m_steady  m_decreased : marking_type)
    (classes_transs  classes_fired_pre : list (list trans_type))
    (chronos   chronos_final  : trans_type -> option chrono_type),
    stpn_fire_pre
      places             pre   test  inhib
      m_steady            
      chronos     classes_transs
    = (classes_fired_pre, m_decreased, chronos_final)
    ->
    stpn_fire_pre_spec
      places              pre   test   inhib
      m_steady            
      chronos      classes_transs
      classes_fired_pre    m_decreased   chronos_final.
Proof.
  do 10 intro.
  functional induction (stpn_fire_pre
                          places pre test inhib
                          m_steady chronos0    classes_transs)
             using stpn_fire_pre_ind.
  apply spn_fire_pre_mk. 
Qed.
Theorem stpn_fire_pre_complete : forall
    (places : list place_type)
    (pre   test  inhib : weight_type)
    (m_steady  m_decreased : marking_type)
    (classes_transs  classes_fired_pre : list (list trans_type))
    (chronos   chronos_final  : trans_type -> option chrono_type),
    stpn_fire_pre_spec
      places              pre   test   inhib
      m_steady            
      chronos      classes_transs
      classes_fired_pre    m_decreased   chronos_final
    ->
    stpn_fire_pre
      places             pre   test  inhib
      m_steady            
      chronos     classes_transs
    = (classes_fired_pre, m_decreased, chronos_final).
Proof.
  intros. elim H.
  intros. unfold stpn_fire_pre. assumption.
Qed.
*)

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

Inductive stpn_fire_spec   
          (places : list place_type)
          (pre test inhib post : weight_type)
          (m_steady : marking_type)
          (chronos : trans_type -> option chrono_type)
          (classes_transs : list (list trans_type))
  : (list (list trans_type))   ->
    marking_type               ->
    (trans_type -> option chrono_type)    ->
    Prop :=
| stpn_fire_mk :  forall
    (sub_Lol : list (list trans_type))
    (m_inter   m  : marking_type)
    (new_chronos : trans_type -> option chrono_type),
    (sub_Lol, m_inter, new_chronos) = stpn_fire_pre
                           places  pre test inhib 
                           m_steady  chronos  classes_transs
    ->
    m = fire_post
          places post   m_inter  sub_Lol
    ->
    stpn_fire_spec   
      places         pre test inhib post
      m_steady       chronos  classes_transs
      sub_Lol    m   new_chronos.

Functional Scheme sitpn_fire_ind :=
  Induction for  sitpn_fire   Sort Prop.
(*
Theorem stpn_fire_correct : forall
    (places : list place_type)
    (pre test inhib post : weight_type)
    (m_steady  m_next: marking_type)
    (chronos  next_chronos : trans_type -> option chrono_type)
    (classes_transs   sub_Lol: list (list trans_type)),
    stpn_fire
      places   pre  test  inhib  post
      m_steady  chronos   classes_transs
    =  (sub_Lol, m_next, next_chronos)
    ->
    stpn_fire_spec
      places   pre  test  inhib  post
      m_steady   chronos  classes_transs
      sub_Lol  m_next next_chronos.
Proof.
  do 11 intro.
  functional induction (stpn_fire
                          places pre test inhib post
                          m_steady chronos0
                          classes_transs)
             using stpn_fire_ind.
  intro H.
  assert (Hleft : sub_Lol0 = sub_Lol).
  { inversion  H. reflexivity. } 
  assert (Hmiddle :  m_next = fire_post
                                places post m_inter sub_Lol0 ).
  { inversion  H. reflexivity. }
  assert (Hright :   new_chronos = next_chronos).
  { inversion  H. reflexivity. }
  apply stpn_fire_mk with (m_inter := m_inter).
  - rewrite Hleft in e. rewrite e. rewrite Hright. reflexivity.
  - rewrite <-  Hleft. assumption. 
Qed.
Theorem stpn_fire_complete : forall
    (places : list place_type)
    (pre test inhib post : weight_type)
    (m_steady  m_next: marking_type)
    (chronos  next_chronos : trans_type -> option chrono_type)
    (classes_transs   sub_Lol: list (list trans_type)),
    stpn_fire_spec
      places   pre  test  inhib  post
      m_steady   chronos  classes_transs
      sub_Lol  m_next next_chronos
    ->
    stpn_fire
      places   pre  test  inhib  post
      m_steady  chronos   classes_transs
    =  (sub_Lol, m_next, next_chronos).
Proof.
  intros. elim H.
  intros. unfold stpn_fire. rewrite <- H0. rewrite H1. reflexivity.
Qed.
*)

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

Inductive stpn_cycle_spec
          (stpn : STPN) :
  list (list trans_type)    ->
  STPN                       ->
  Prop :=
| stpn_fired_mk : forall
    (sub_Lol  Lol: list (list trans_type))
    (next_m   m : marking_type)
    (next_stpn : STPN)
    (places : list place_type)
    (transs  enabled : list trans_type)
    (pre  post test inhib : weight_type)
    (chronos  chronos_incr next_chronos : trans_type
                                          -> option chrono_type),
    stpn = mk_STPN
             (mk_SPN
                places  transs  
                pre  post test inhib    m
                (mk_prior
                   Lol))
             chronos
    ->
    enabled = list_enabled_stpn
                stpn
    ->
    chronos_incr = increment_time_enabled
                     chronos      enabled
    -> 
    (sub_Lol, next_m, next_chronos ) =
    (stpn_fire
       places  pre  test  inhib  post   m
       chronos_incr    Lol)
    ->
    next_stpn = mk_STPN
                  (mk_SPN
                     places   transs  
                     pre      post    test   inhib    next_m
                     (mk_prior
                        Lol))
                  next_chronos
    -> 
    stpn_cycle_spec
      stpn   sub_Lol  next_stpn.

Functional Scheme stpn_cycle_ind :=
  Induction for stpn_cycle   Sort Prop.
(*
Theorem stpn_cycle_correct :
  forall (stpn  next_stpn : STPN)
         (sub_Lol : list (list trans_type)),
    stpn_cycle
      stpn    =  (sub_Lol, next_stpn)
    ->
    stpn_cycle_spec
      stpn   sub_Lol  next_stpn.
Proof.
  intros  stpn  next_stpn  sub_Lol.
  functional induction (stpn_cycle stpn)
             using stpn_cycle_ind. 
  intro H. apply stpn_fired_mk
             with (Lol:=Lol) (next_m:=new_m) (m:=marking)
                  (places:=places) (transs:=transs)
                  (pre:=pre) (post:=post) (test:=test)
                  (inhib:=inhib) (chronos:=chronos0)
                  
                  (enabled := (list_enabled_stpn
                                 {|
                                   spn := {|
                                           places := places;
                                           transs := transs;
                                           pre := pre;
                                           post := post;
                                           test := test;
                                           inhib := inhib;
                                           marking := marking;
                                           priority :=
                                             {| Lol := Lol |} |};
                                   chronos := chronos0 |}))
                  (chronos_incr := increment_time_enabled
                                     chronos0
                                     (list_enabled_stpn
                                        {|
                                          spn := {|
                                                  places := places;
                                                  transs := transs;
                                                  pre := pre;
                                                  post := post;
                                                  test := test;
                                                  inhib := inhib;
                                                  marking := marking;
                                                  priority :=
                                             {| Lol := Lol |} |};
                                          chronos := chronos0 |}))

                  (next_chronos :=
                     troiz (stpn_fire
                              places  pre  test  inhib  post marking
                              (increment_time_enabled
                                 chronos0
                                 (list_enabled_stpn
                                    {|
                                      spn := {|
                                              places := places;
                                              transs := transs;
                                              pre := pre;
                                              post := post;
                                              test := test;
                                              inhib := inhib;
                                              marking := marking;
                                              priority :=
                                                {| Lol := Lol |} |};
                                      chronos := chronos0 |}))  Lol)).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite e2. 
    assert (Hleft : transs_fired = sub_Lol).
    { inversion  H. reflexivity. } rewrite Hleft. simpl. reflexivity. 
  - rewrite e2. simpl. inversion H. reflexivity.
Qed.
Theorem stpn_cycle_complete :
 forall (stpn  next_stpn : STPN)
        (sub_Lol : list (list trans_type)),
   stpn_cycle_spec
     stpn   sub_Lol  next_stpn
   ->
   stpn_cycle
      stpn    =  (sub_Lol, next_stpn).
Proof.
  intros. elim H.
  intros. unfold stpn_cycle.
  rewrite  H0. rewrite  H4. simpl.
  assert (H23left : sub_Lol0 =
            premz (stpn_fire places pre test inhib post m
                           (increment_time_enabled
                              chronos0
                              (list_enabled transs places pre test inhib m))
                           Lol)).
  {unfold list_enabled_stpn in H1. unfold list_enabled_spn in H1.
   rewrite H0 in H1. rewrite <- H1.
   rewrite H2 in H3. inversion  H3. simpl. reflexivity. }
  rewrite H23left. (* unfold prod. *)

Admitted.

 *)

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

Inductive stpn_animate_spec
          (stpn : STPN)
  : nat ->
    list
      (list (list trans_type)  *
       list (place_type * nat) *
       (list (trans_type * option (nat * nat * nat)))) -> Prop :=
| animate_stpn_O : stpn_animate_spec
                    stpn   O  [ ( [] , [] , [] ) ]
| animate_stpn_S :
    forall (next_stpn : STPN)
           (Lol_fired : list (list trans_type))
           (m_visuel : list (place_type * nat))
           (chronos_visuels : list (trans_type * option (nat * nat * nat)))
           (n : nat)
           (TAIL : list (list (list trans_type) *
                         list (place_type * nat) *
                         (list (trans_type * option (nat * nat * nat))))),
     
      (Lol_fired, next_stpn) = stpn_cycle stpn
      ->
      m_visuel = marking2list
                   (marking (spn next_stpn))   (places (spn next_stpn))
      ->
      chronos_visuels = (intervals2list
                           (transs (spn  next_stpn)) (chronos   next_stpn))
      ->
      stpn_animate_spec
        next_stpn    n    TAIL
      -> 
      stpn_animate_spec
        stpn   (S n)   ((Lol_fired, m_visuel, chronos_visuels) :: TAIL)
.

Functional Scheme stpn_animate_ind :=
  Induction for stpn_animate   Sort Prop.
(* Reset projections3. *)
(*
Theorem stpn_animate_correct :
  forall (stpn   : STPN)
         (n : nat)
         (truc : list (list (list trans_type)  *
                       list (place_type * nat) *
                       list (trans_type * option (nat * nat * nat)))),
    stpn_animate
      stpn    n   =  truc
    ->
    stpn_animate_spec
      stpn    n     truc.
Proof.
  intros stpn n.
  functional induction (stpn_animate stpn n)
             using stpn_animate_ind.
  - intros truc H. rewrite <- H. apply animate_stpn_O.
  - intros truc H. rewrite <- H.
    apply animate_stpn_S with (next_stpn := snd (stpn_cycle stpn)).
    + rewrite e0. simpl. reflexivity.
    + rewrite e0. simpl. reflexivity.
    + rewrite e0. simpl. reflexivity. 
    + rewrite e0. simpl. apply (IHl (stpn_animate next_stpn n')). reflexivity.
Qed. 
Theorem stpn_animate_complete :
  forall (stpn   : STPN)
         (n : nat)
         (truc : list (list (list trans_type)  *
                       list (place_type * nat) *
                       list (trans_type * option (nat * nat * nat)))),
    stpn_animate_spec
      stpn    n     truc
    ->
    stpn_animate
      stpn    n   =  truc.
Proof.
  intros. elim H.
  - simpl. reflexivity. 
  - intros. simpl.
    rewrite <- H0. rewrite <- H1. rewrite <- H2. rewrite <- H4.
    reflexivity.
Qed. 
*)