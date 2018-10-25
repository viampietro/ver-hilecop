Require Export STPN.
From Coq Require Extraction.

(* ~/.opam/4.06.1/lib/coq/theories/  *)

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


Definition conditions_type := trans_type -> option bool.
(* some transitions don't have any condition *)

Definition scenar_type := list conditions_type.
(***  a list of size n allows one to compute up to n cycles  ***) 

Structure SITPN : Set := mk_SITPN { 
                             stpn : STPN;
                             scenario : scenar_type
                         }.

Definition check_condition
           (conditions : conditions_type)
           (t : trans_type) : bool :=
  match (conditions t) with
  | None => true
  | Some b => b
  end.

Inductive check_condition_spec
          (conditions : conditions_type)
          (t : trans_type)
  : Prop :=
| check_condition_none : 
    (conditions t) = None                             -> 
    check_condition_spec
      conditions  t
| check_condition_some_if : 
    (conditions t) = Some true 
    ->
    check_condition_spec
      conditions  t.
Functional Scheme check_condition_ind :=
  Induction for check_condition Sort Prop.
Theorem check_condition_correct : forall
    (conditions : conditions_type)
    (t : trans_type),
    (check_condition
      conditions t)  = true
    ->
    (check_condition_spec
       conditions t).
Proof.
  intros conditions t.
  functional induction (check_condition  conditions t) using check_condition_ind.
  - intro H. apply check_condition_some_if. rewrite e. rewrite H.
    reflexivity.
  - intro H. apply check_condition_none. assumption.
Qed.
Theorem check_condition_complete : forall
    (conditions : conditions_type)
    (t : trans_type),
    (check_condition_spec
       conditions t)                    ->
    (check_condition
      conditions t)  = true.    
Proof.
  intros conditions t H. elim H.
  - intro H'. unfold check_condition. rewrite H'. reflexivity.
  - intro H'. unfold check_condition. rewrite H'. reflexivity.
Qed.



(*****************************************************************
******************************************************************
*********   FIRING ALGORITHM    for SITPN     ********************
******************************************************************)

Print SITPN.
Print stpn_class_fire_pre_aux.
(** compared with STPN it just add an "if clause"  : *) 

Fixpoint sitpn_class_fire_pre_aux
         (full_class : list trans_type)
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
    if (check_all_edges places (pre t) (test t) (inhib t) m_steady m_decreasing)
        && (check_chrono (chronos t))
        && (check_condition conditions t)
    then
      let new_decreasing := update_marking_pre t pre m_decreasing places in
      let new_chronos :=
          reset_all_chronos0 (reset_chrono0 chronos t)
                             (list_disabled full_class places pre test inhib m_steady new_decreasing) in
      sitpn_class_fire_pre_aux full_class places pre test inhib m_steady new_decreasing new_chronos
                               tail (subclass_half_fired ++ [t]) conditions
    else
      sitpn_class_fire_pre_aux full_class places pre test inhib m_steady
                               m_decreasing chronos tail subclass_half_fired conditions
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

Print check_all_edges. 
Inductive sitpn_class_fire_pre_aux_spec
          (whole_class : list trans_type)
          (places : list place_type)
          (pre   test   inhib : weight_type)  
          (m_steady     : marking_type)
          (conditions : conditions_type) :
  marking_type                          ->   (* m_decreasing *)
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
    sitpn_class_fire_pre_aux_spec
      whole_class    places       pre  test  inhib
      m_steady            conditions 
      m_decreased          chronos
      []                   subclass_fired_pre
      subclass_fired_pre   m_decreased     chronos
| class_cons_if :  forall
    (t : trans_type)
    (tail    subclass_fired_pre  sub : list trans_type)
    (m_decreasing_low  m_decreasing_high  m : marking_type)
    (chronos  new_chronos   chronos_final : trans_type -> option chrono_type),
    check_all_edges
      places    (pre t) (test t) (inhib t)
      m_steady  m_decreasing_high               = true   /\
    check_chrono (chronos  t)                     = true   /\
    (check_condition conditions t)              = true
    -> 
    m_decreasing_low = (update_marking_pre
                          t   pre   m_decreasing_high places)
    ->
     new_chronos =
     (reset_all_chronos0
        (reset_chrono0 chronos t)    (* ! reset de t *)
        (list_disabled
           whole_class   places     pre    test    inhib
           m_steady       m_decreasing_low))
    ->    
    sitpn_class_fire_pre_aux_spec
      whole_class     places      pre  test  inhib
      m_steady               conditions
      m_decreasing_low             new_chronos
      tail                         (subclass_fired_pre ++ [t])
      sub                          m     chronos_final
    ->
    sitpn_class_fire_pre_aux_spec
      whole_class     places     pre  test  inhib
      m_steady           conditions
      m_decreasing_high    chronos
      (t::tail)            subclass_fired_pre
      sub                  m           chronos_final
| class_cons_else :  forall
    (t : trans_type)
    (tail   subclass_half_fired   sub : list trans_type)
    (m_decreasing   m : marking_type)
    (chronos     chronos_final : trans_type -> option chrono_type),
    check_all_edges
      places    (pre t) (test t) (inhib t)
      m_steady  m_decreasing                   = false   \/
    check_chrono (chronos  t)                    = false   \/
    (check_condition conditions t)             = false
    ->
    sitpn_class_fire_pre_aux_spec
      whole_class     places      pre  test  inhib
      m_steady          conditions
      m_decreasing          chronos 
      tail                  subclass_half_fired
      sub                   m       chronos_final
    ->
    sitpn_class_fire_pre_aux_spec
      whole_class     places      pre  test  inhib
      m_steady          conditions
      m_decreasing          chronos     
      (t::tail)             subclass_half_fired
      sub                  m   chronos_final.

Functional Scheme sitpn_class_fire_pre_aux_ind :=
  Induction for sitpn_class_fire_pre_aux   Sort Prop.

Lemma andb3_true_iff :
  forall b1 b2 b3:bool,
    b1 && b2 && b3 = true   <-> b1 = true /\ b2 = true /\ b3 = true.
Proof.
  destr_bool; tauto.
Qed.

Lemma andb3_false_iff :
  forall b1 b2 b3:bool,
    b1 && b2 && b3  = false <-> b1 = false \/ b2 = false \/ b3 = false.
Proof.
  destr_bool; tauto.
Qed.
Hint Resolve ->  andb3_true_iff andb3_false_iff: mybool.

Theorem sitpn_class_fire_pre_aux_correct : forall
    (whole_class : list trans_type)
    (places : list place_type)
    (pre  test  inhib : weight_type)
    (m_steady      m_decreasing      m_final : marking_type)
    (class_transs  subclass_fired_pre  sub_final : list trans_type)
    (chronos chronos_final : trans_type -> option chrono_type)
    (conditions : conditions_type),
    sitpn_class_fire_pre_aux
      whole_class     places         pre   test   inhib   
      m_steady       
      m_decreasing    chronos      
      class_transs   subclass_fired_pre     conditions
    = (sub_final, m_final, chronos_final)
    ->
    sitpn_class_fire_pre_aux_spec
      whole_class     places          pre   test  inhib   
      m_steady           conditions
      m_decreasing    chronos     
      class_transs    subclass_fired_pre
      sub_final       m_final   chronos_final.
Proof.
   
  intros whole_class  places  pre test inhib  m_steady
         m_decreasing  m_final
         class_transs   subclass_fired_pre    sub_final
         chronos  chronos_final   conditions.
  functional induction 
             (sitpn_class_fire_pre_aux
                whole_class places  pre test inhib
                m_steady  m_decreasing    chronos 
                class_transs  subclass_fired_pre  conditions)
             using sitpn_class_fire_pre_aux_ind.
  - intro H. inversion H.  apply class_nil.
  - intro H.
    apply class_cons_if
      with (m_decreasing_low := (update_marking_pre
                                   t pre m_decreasing  places))
           (new_chronos :=
              (reset_all_chronos0
                 (reset_chrono0 chronos t)    (* ! reset de t *)
                 (list_disabled
                    whole_class   places     pre    test    inhib
                    m_steady    (update_marking_pre
                                   t pre m_decreasing  places)))).
    +  auto with mybool. 
    + reflexivity.
    + reflexivity.
    + apply (IHp H).      
  - intro H. apply class_cons_else.
    + apply andb3_false_iff. assumption. 
    + apply (IHp H).
Qed. 
Theorem stpn_class_fire_pre_aux_complete :  forall
    (whole_class : list trans_type)
    (places : list place_type)
    (pre  test  inhib : weight_type)
    (m_steady   m_decreasing     m_final : marking_type)
    (class_transs  subclass_fired_pre  sub_final : list trans_type)
    (chronos chronos_final : trans_type -> option chrono_type)
    (conditions : conditions_type),
    sitpn_class_fire_pre_aux_spec
      whole_class      places               pre test inhib   
      m_steady        conditions
      m_decreasing        chronos 
      class_transs         subclass_fired_pre
      sub_final   m_final    chronos_final
    ->
    sitpn_class_fire_pre_aux
      whole_class      places          pre test inhib   
      m_steady
      m_decreasing    chronos       
      class_transs    subclass_fired_pre    conditions
    = (sub_final , m_final, chronos_final).
Proof.
  intros. elim H.
  - simpl. reflexivity.
  - intros. simpl.
    assert (H0' : check_all_edges
                    places (pre t) (test t) 
                    (inhib t) m_steady m_decreasing_high &&
                    check_chrono (chronos0 t)               &&
                    (check_condition conditions t) = true).
      { apply andb3_true_iff. assumption. }  
      rewrite H0'. rewrite <- H1. rewrite <- H2. rewrite H4.
      reflexivity.
  - intros. simpl.
    assert (H0' : check_all_edges
                    places (pre t) (test t) 
                    (inhib t) m_steady m_decreasing0 &&
                    check_chrono (chronos0 t)           &&
                    (check_condition conditions t) = false).
      { apply andb3_false_iff. assumption. } 
    rewrite H0'. rewrite H2.  reflexivity. 
Qed.
 

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
    class_transs  places    pre test inhib m_steady m_decreasing
    chronos     class_transs []   conditions.


Inductive sitpn_class_fire_pre_spec
          (places : list place_type)
          (pre   test   inhib : weight_type)  
          (m_steady    m_decreasing    : marking_type)
          (chronos  :  trans_type -> option chrono_type)
          (class_transs : list trans_type)
          (conditions : conditions_type)
  : (list trans_type)                     ->
    marking_type                          ->
    (trans_type -> option chrono_type)    ->
    Prop :=
| sitpn_sub_fire_pre_mk :
    forall (subclass_fired_pre : list trans_type)
           (m_fired_pre_class : marking_type)
           (chronos_final: trans_type -> option chrono_type),
      sitpn_class_fire_pre_aux
        class_transs     places          pre    test    inhib
        m_steady
        m_decreasing     chronos
        class_transs    []    conditions
      = (subclass_fired_pre, m_fired_pre_class, chronos_final)
      ->
      sitpn_class_fire_pre_spec
        places          pre  test  inhib
        m_steady
        m_decreasing    chronos     class_transs   conditions
        subclass_fired_pre  m_fired_pre_class  chronos_final
.

Functional Scheme sitpn_class_fire_pre_ind :=
  Induction for sitpn_class_fire_pre   Sort Prop.
Theorem sitpn_class_fire_pre_correct : forall
    (places : list place_type)
    (pre  test  inhib : weight_type)
    (m_steady   m_decreasing     m_decreased : marking_type)
    (class_transs     subclass_fired_pre  : list trans_type)
    (chronos chronos_final: trans_type -> option chrono_type)
    (conditions : conditions_type),
    sitpn_class_fire_pre
      places    pre    test    inhib
      m_steady
      m_decreasing   chronos     class_transs   conditions
    = (subclass_fired_pre, m_decreased, chronos_final)
    ->
    sitpn_class_fire_pre_spec
      places          pre  test  inhib
      m_steady
      m_decreasing    chronos    class_transs  conditions
      subclass_fired_pre  m_decreased  chronos_final.
Proof.
  intros places pre test inhib m_steady m_decreasing m_decreased
         class_transs  subclass_fired_pre chronos chronos_final
         conditions  H.
  functional induction (sitpn_class_fire_pre
                          places    pre test inhib
                          m_steady  m_decreasing
                          chronos   class_transs  conditions)
             using sitpn_class_fire_pre_ind.
  apply sitpn_sub_fire_pre_mk. assumption.
Qed. 
Theorem sitpn_class_fire_pre_complete : forall
    (places : list place_type)
    (pre  test  inhib : weight_type)
    (m_steady   m_decreasing     m_decreased : marking_type)
    (class_transs     subclass_fired_pre  : list trans_type)
    (chronos chronos_final: trans_type -> option chrono_type)
    (conditions : conditions_type),
    sitpn_class_fire_pre_spec
      places          pre  test  inhib
      m_steady
      m_decreasing    chronos    class_transs  conditions 
      subclass_fired_pre  m_decreased  chronos_final
    -> 
    sitpn_class_fire_pre
      places    pre    test    inhib
      m_steady
      m_decreasing   chronos     class_transs   conditions
    = (subclass_fired_pre, m_decreased, chronos_final).
Proof.
  intros. elim H.
  intros. assumption.  (* no need to unfold ?  great *)
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
          (conditions : conditions_type)
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
    sitpn_fire_pre_aux_spec
      places               pre   test  inhib
      m_steady       conditions
      m_decreased      []       classes_fired_pre    chronos 
      classes_fired_pre    m_decreased          chronos
| classes_cons : forall
    (classes_tail classes_fired_pre_tail C : list (list trans_type))
    (class     class_fired_pre : list trans_type)
    (m_decreased   m_decreasing  m_any  : marking_type)
    (chronos   chronos_final  any_chronos : trans_type ->
                                            option chrono_type),
    sitpn_class_fire_pre
      places          pre    test    inhib
      m_steady
      m_decreasing   chronos     class    conditions
    = (class_fired_pre, m_decreased, chronos_final)
    ->
    sitpn_fire_pre_aux_spec
      places          pre   test   inhib
      m_steady      conditions 
      m_decreased      classes_tail
      (class_fired_pre :: classes_fired_pre_tail)
      chronos_final     C     m_any    any_chronos
    ->
    sitpn_fire_pre_aux_spec
      places                  pre   test   inhib
      m_steady        conditions 
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


Theorem sitpn_fire_pre_aux_correct :  forall
    (places : list place_type)
    (pre   test  inhib : weight_type)
    (m_steady  m_decreasing  m_decreased : marking_type)
    (classes_transs   classes_fired_pre_rec
                      classes_fired_pre : list (list trans_type))
    (chronos   chronos_final  : trans_type -> option chrono_type)
    (conditions : conditions_type),
    sitpn_fire_pre_aux
      places             pre   test  inhib
      m_steady           m_decreasing 
      chronos  classes_transs  classes_fired_pre_rec    conditions  
    = (classes_fired_pre, m_decreased, chronos_final)
    ->
    sitpn_fire_pre_aux_spec
      places              pre   test   inhib
      m_steady         conditions    m_decreasing
      classes_transs      classes_fired_pre_rec
      chronos    classes_fired_pre    m_decreased chronos_final.
Proof.
  do 13 intro.
  functional induction
             (sitpn_fire_pre_aux
                places pre test inhib m_steady m_decreasing
                chronos
                classes_transs classes_fired_pre_rec conditions)
             using sitpn_fire_pre_aux_ind.
  - intro H. 
    assert (Hleft :  classes_half_fired = classes_fired_pre).
    { inversion  H. reflexivity. } 
    assert (Hmiddle :  m_decreasing = m_decreased).
    { inversion  H. reflexivity. }
    assert (Hright :  chronos   = chronos_final).
    { inversion  H. reflexivity. } 
    rewrite Hleft. rewrite Hright. rewrite Hmiddle.
    apply classes_nil.
  - intro H.
    apply classes_cons
      with (class_fired_pre := premz (sitpn_class_fire_pre
                                        places pre test inhib
                                        m_steady
                                        m_decreasing chronos
                                        class  conditions))
           (m_decreased := deuz (sitpn_class_fire_pre
                                   places pre test inhib
                                   m_steady
                                   m_decreasing chronos
                                   class   conditions ))
           (chronos_final := troiz (sitpn_class_fire_pre
                                      places pre test inhib
                                      m_steady
                                      m_decreasing chronos
                                      class  conditions)).
    + rewrite e0. simpl. reflexivity.
    + rewrite e0. simpl.  apply (IHp H). 
Qed.

Theorem sitpn_fire_pre_aux_complete : forall
    (places : list place_type)
    (pre   test  inhib : weight_type)
    (m_steady  m_decreasing  m_decreased : marking_type)
    (classes_transs   classes_fired_pre_rec
                      classes_fired_pre : list (list trans_type))
    (chronos   chronos_final  : trans_type -> option chrono_type)
    (conditions : conditions_type),
    sitpn_fire_pre_aux_spec
      places              pre   test   inhib
      m_steady         conditions    m_decreasing
      classes_transs      classes_fired_pre_rec
      chronos    classes_fired_pre    m_decreased chronos_final
    ->
    sitpn_fire_pre_aux
      places             pre   test  inhib
      m_steady           m_decreasing 
      chronos  classes_transs  classes_fired_pre_rec  conditions  
    = (classes_fired_pre, m_decreased, chronos_final).    
Proof.
  intros. elim H.
  -  intros. simpl. reflexivity.
  -  intros. simpl. rewrite H0. rewrite <- H2. reflexivity.
Qed. 


(***  sitpn_fire_pre_aux  --->  sitpn_fire_pre_aux   *****) 

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
         (chronos : trans_type -> option chrono_type)
         (classes_transs  : list (list trans_type))
         (conditions : conditions_type)
  : (list (list trans_type)) ->
    marking_type ->
    (trans_type -> option chrono_type)   ->
    Prop :=
| sitpn_fire_pre_mk :
    forall (classes_fired_pre : list (list trans_type))
           (m_inter : marking_type)
           (chronos_next  : trans_type ->   option chrono_type),
      sitpn_fire_pre_aux
        places           pre    test    inhib
        m_steady
        m_steady   chronos   classes_transs   []  conditions
      = (classes_fired_pre, m_inter,  chronos_next)
      ->
      sitpn_fire_pre_spec
        places              pre  test  inhib
        m_steady
        chronos        classes_transs    conditions
        classes_fired_pre   m_inter    chronos_next.

Functional Scheme sitpn_fire_pre_ind :=
  Induction for sitpn_fire_pre   Sort Prop.


Theorem stpn_fire_pre_correct :  forall
    (places : list place_type)
    (pre   test  inhib : weight_type)
    (m_steady  m_decreased : marking_type)
    (classes_transs  classes_fired_pre : list (list trans_type))
    (chronos   chronos_final  : trans_type -> option chrono_type)
    (conditions : conditions_type),
    sitpn_fire_pre
      places             pre   test  inhib
      m_steady            
      chronos     classes_transs    conditions
    = (classes_fired_pre, m_decreased, chronos_final)
    ->
    sitpn_fire_pre_spec
      places              pre   test   inhib
      m_steady            
      chronos      classes_transs    conditions
      classes_fired_pre    m_decreased   chronos_final.
Proof.
  do 11 intro.
  functional induction (sitpn_fire_pre
                          places pre test inhib
                          m_steady   chronos
                          classes_transs  conditions )
             using sitpn_fire_pre_ind.
  apply sitpn_fire_pre_mk. 
Qed.
Theorem sitpn_fire_pre_complete : forall
    (places : list place_type)
    (pre   test  inhib : weight_type)
    (m_steady  m_decreased : marking_type)
    (classes_transs  classes_fired_pre : list (list trans_type))
    (chronos   chronos_final  : trans_type -> option chrono_type)
    (conditions : conditions_type),
    sitpn_fire_pre_spec
      places              pre   test   inhib
      m_steady            
      chronos      classes_transs   conditions
      classes_fired_pre    m_decreased   chronos_final
    ->
    sitpn_fire_pre
      places             pre   test  inhib
      m_steady            
      chronos     classes_transs   conditions
    = (classes_fired_pre, m_decreased, chronos_final).
Proof.
  intros. elim H.
  intros. assumption.  (* unfold sitpn_fire_pre. not even needed *)
Qed.

(*********************************************************)
(******* for  DEBUGGING  only  ..  ***********************)
Search SPN.
Print stpn_print_fire_pre. 
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
    new_chronos   transs).

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
          (chronos : trans_type -> option chrono_type)
          (classes_transs : list (list trans_type))
          (conditions : conditions_type)
  : (list (list trans_type))   ->
    marking_type               ->
    (trans_type -> option chrono_type)    ->
    Prop :=
| sitpn_fire_mk :  forall
    (sub_Lol : list (list trans_type))
    (m_inter   m  : marking_type)
    (new_chronos : trans_type -> option chrono_type),
    (sub_Lol, m_inter, new_chronos) = sitpn_fire_pre
                           places  pre test inhib 
                           m_steady  chronos
                           classes_transs  conditions 
    ->
    m = fire_post
          places post   m_inter  sub_Lol
    ->
    sitpn_fire_spec   
      places         pre test inhib post
      m_steady       chronos  classes_transs    conditions
      sub_Lol    m   new_chronos.

Functional Scheme sitpn_fire_ind :=
  Induction for  sitpn_fire   Sort Prop.

Theorem sitpn_fire_correct : forall
    (places : list place_type)
    (pre test inhib post : weight_type)
    (m_steady  m_next: marking_type)
    (chronos  next_chronos : trans_type -> option chrono_type)
    (classes_transs   sub_Lol: list (list trans_type))
    (conditions : conditions_type),
    sitpn_fire
      places   pre  test  inhib  post
      m_steady  chronos   classes_transs   conditions 
    =  (sub_Lol, m_next, next_chronos)
    ->
    sitpn_fire_spec
      places   pre  test  inhib  post
      m_steady   chronos  classes_transs   conditions
      sub_Lol  m_next next_chronos.
Proof.
  do 12 intro.
  functional induction (sitpn_fire
                          places pre test inhib post
                          m_steady      chronos
                          classes_transs   conditions )
             using sitpn_fire_ind.
  intro H.
  assert (Hleft : sub_Lol0 = sub_Lol).
  { inversion  H. reflexivity. } 
  assert (Hmiddle :  m_next = fire_post
                                places post m_inter sub_Lol0 ).
  { inversion  H. reflexivity. }
  assert (Hright :   new_chronos = next_chronos).
  { inversion  H. reflexivity. }
  apply sitpn_fire_mk with (m_inter := m_inter).
  - rewrite Hleft in e. rewrite e. rewrite Hright. reflexivity.
  - rewrite <-  Hleft. assumption. 
Qed.
Theorem sitpn_fire_complete : forall
    (places : list place_type)
    (pre test inhib post : weight_type)
    (m_steady  m_next: marking_type)
    (chronos  next_chronos : trans_type -> option chrono_type)
    (classes_transs   sub_Lol: list (list trans_type))
    (conditions : conditions_type),
    sitpn_fire_spec
      places   pre  test  inhib  post
      m_steady   chronos  classes_transs   conditions
      sub_Lol  m_next next_chronos
    ->
    sitpn_fire
      places   pre  test  inhib  post
      m_steady  chronos   classes_transs    conditions
    =  (sub_Lol, m_next, next_chronos).
Proof.
  intros. elim H.
  intros. unfold sitpn_fire. rewrite <- H0. rewrite H1. reflexivity.
Qed.

(***************************************************************)
(* The marking and the "intervals" (their counter) 
   are evolving !!  
but we want to see also the fired transitions ! *)
(******************************* CYCLE **********************)

(* wait a minute *)

Definition list_sensitized_sitpn
           (sitpn : SITPN)
  : list trans_type :=
  match sitpn with
  | mk_SITPN
      (mk_STPN
         spn
         chronos)
      scenario
    =>
    list_sensitized_spn
      spn
  end.
Print SITPN. 
Inductive list_sensitized_sitpn_spec
           (sitpn : SITPN)
  : list trans_type  ->  Prop  :=
| list_sensitized_sitpn_mk : forall
    (spn : SPN)
    (enabled_transs : list trans_type)
    (chronos : trans_type -> option chrono_type)
    (scenario : scenar_type),
    sitpn = mk_SITPN
              (mk_STPN
                 spn
                 chronos)
              scenario
    ->
    list_sensitized_spn 
      spn
    = enabled_transs
    ->
    list_sensitized_sitpn_spec
      sitpn 
      enabled_transs.
Functional Scheme list_sensitized_sitpn_ind :=
  Induction for list_sensitized_sitpn Sort Prop.
Theorem list_sensitized_sitpn_correct :  forall
    (sitpn : SITPN) (enabled : list trans_type),
    list_sensitized_sitpn
      sitpn = enabled        ->
    list_sensitized_sitpn_spec
      sitpn  enabled.
Proof.
  intros sitpn  enabled.
  functional induction (list_sensitized_sitpn
                          sitpn)
             using list_sensitized_sitpn_ind.
  intro H. apply list_sensitized_sitpn_mk with
               (spn := spn) (chronos := _x0) (scenario := _x).
  + reflexivity.
  + assumption.   
Qed.
Theorem list_sensitized_sitpn_complete : forall
    (sitpn : SITPN) (enabled : list trans_type),
    list_sensitized_sitpn_spec
      sitpn  enabled                  -> 
    list_sensitized_sitpn
      sitpn = enabled.
Proof.
  intros sitpn  enabled H. elim H.
  intros. unfold list_sensitized_sitpn. rewrite H0. rewrite H1.
  reflexivity. 
Qed.

(*  now it's easier *)
Print list_sensitized. 
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
    | [] => ([], sitpn)   (* dangerous ? 
freeze !  or continue with no more constraints ?  *)
    | C :: tail =>
      let chronos_incr := increment_all_chronos
                            chronos
                            (list_sensitized_spn
                               (mk_SPN
                                  places  transs
                                  (* nodup_places  nodup_transitions *)  
                                  pre     post    test   inhib   marking
                                  (mk_prior
                                     Lol) ))
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

Print list_sensitized_sitpn. Print scenar_type. 

Inductive sitpn_cycle_spec
          (sitpn : SITPN) :
  list (list trans_type)    ->
  SITPN                       ->
  Prop :=
| sitpn_fired_mk_nil : forall
    (Lol: list (list trans_type))
    (m : marking_type)
    (places : list place_type)
    (transs   : list trans_type)
    (pre  post test inhib : weight_type)
    (chronos  : trans_type  -> option chrono_type)
    (scenario : scenar_type),
    sitpn = mk_SITPN
             (mk_STPN
                (mk_SPN
                   places  transs  pre  post test inhib    m
                   (mk_prior
                      Lol))
                chronos)
             scenario
    ->
    scenario = []
    ->
    sitpn_cycle_spec
      sitpn   []  sitpn
| sitpn_fired_mk : forall
    (sub_Lol  Lol: list (list trans_type))
    (next_m   m : marking_type)
    (next_sitpn : SITPN)
    (next_stpn stpn : STPN)
    (next_spn  spn : SPN)
    (places : list place_type)
    (transs  enabled : list trans_type)
    (pre  post test inhib : weight_type)
    (chronos  chronos_incr next_chronos : trans_type
                                          -> option chrono_type)
    (scenario   Tail : scenar_type)
    (C : conditions_type),

    spn = mk_SPN
            places  transs  pre  post test inhib    m
            (mk_prior
               Lol)
    ->
    stpn = mk_STPN
                spn
                chronos
    ->
    sitpn = mk_SITPN
              stpn
              scenario
    ->
    scenario = C :: Tail
    ->    
    enabled = list_sensitized_spn
                spn
    ->
    chronos_incr = increment_all_chronos
                     chronos      enabled
    -> 
    (sub_Lol, next_m, next_chronos ) =
    (sitpn_fire
       places  pre  test  inhib  post   m
       chronos_incr    Lol    C)
    ->
    next_sitpn = mk_SITPN
                   (mk_STPN
                      (mk_SPN
                         places   transs  
                         pre      post    test   inhib    next_m (* ! *)
                         (mk_prior
                            Lol))
                      next_chronos)  (* ! *)
                   Tail      (* ! *)
    -> 
    sitpn_cycle_spec
      sitpn   sub_Lol  next_sitpn.

Functional Scheme sitpn_cycle_ind :=
  Induction for sitpn_cycle   Sort Prop.

Theorem sitpn_cycle_correct :
  forall (sitpn  next_sitpn : SITPN)
         (sub_Lol : list (list trans_type)),
    sitpn_cycle
      sitpn    =  (sub_Lol, next_sitpn)
    ->
    sitpn_cycle_spec
      sitpn   sub_Lol  next_sitpn.
Proof.
  intros  sitpn  next_sitpn  sub_Lol.
  functional induction (sitpn_cycle sitpn)
             using sitpn_cycle_ind.
  - intro H.  inversion H.  
    apply sitpn_fired_mk_nil
                   with (Lol:=Lol) (m:=marking)
                        (places:=places) (transs:=transs)
                        (pre:=pre) (post:=post) (test:=test)
                        (inhib:=inhib) (chronos:=chronos)
                        (scenario := []).
    + reflexivity.
    + reflexivity.
  - intro H. apply sitpn_fired_mk
               with
                 (Lol:=Lol) (next_m:=new_m) (m:=marking)
                 (places:=places) (transs:=transs)
                 (pre:=pre) (post:=post) (test:=test)
                 (inhib:=inhib) (chronos:=chronos)
                 (scenario:=C::_x) (C:=C) (Tail:=_x)
                 (spn := {|
                          places := places;
                          transs := transs;
                          pre := pre;
                          post := post;
                          test := test;
                          inhib := inhib;
                          marking := marking;
                          priority :=
                            {| Lol := Lol |} |})
                 (stpn := {|
                           spn := {|
                                   places := places;
                                   transs := transs;
                                   pre := pre;
                                   post := post;
                                   test := test;
                                   inhib := inhib;
                                   marking := marking;
                                   priority :=
                                     {| Lol := Lol |} |} ;
                           all_chronos := chronos |})
                                 
                 (enabled := list_sensitized_spn
                               {|
                                 places := places;
                                 transs := transs;
                                 pre := pre;
                                 post := post;
                                 test := test;
                                 inhib := inhib;
                                 marking := marking;
                                 priority :=
                                   {| Lol := Lol |} |})    
                 (chronos_incr := increment_all_chronos
                                    chronos
                                    (list_sensitized_spn
                                       {|
                                         places := places;
                                         transs := transs;
                                         pre := pre;
                                         post := post;
                                         test := test;
                                         inhib := inhib;
                                         marking := marking;
                                         priority :=
                                           {| Lol := Lol |} |}))
                 (next_chronos :=
                    troiz (sitpn_fire
                             places  pre  test  inhib  post marking
                             (increment_all_chronos
                                chronos
                                (list_sensitized_spn
                                       {|
                                         places := places;
                                         transs := transs;
                                         pre := pre;
                                         post := post;
                                         test := test;
                                         inhib := inhib;
                                         marking := marking;
                                         priority :=
                                           {| Lol := Lol |} |}))
                             Lol
                             C)).
    + apply (stpn next_sitpn).
    + apply (spn (stpn next_sitpn)).
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + rewrite e4. 
    assert (Hleft : transs_fired = sub_Lol).
    { inversion  H. reflexivity. } rewrite Hleft. simpl. reflexivity.
    + inversion H. rewrite e4. simpl. reflexivity.
Qed.
Theorem sitpn_cycle_complete :
 forall (sitpn  next_sitpn : SITPN)
        (sub_Lol : list (list trans_type)),
   sitpn_cycle_spec
     sitpn   sub_Lol  next_sitpn
   ->
   sitpn_cycle
      sitpn    =  (sub_Lol, next_sitpn).
Proof.
  intros  sitpn next_sitpn  sub_Lol H. elim H.
  - intros Lol  m places transs pre post test inhib
           chronos  scenario0 H0 H1.
    rewrite H1 in H0. rewrite H0. simpl. reflexivity. 
  - intros sub_Lol0 Lol   next_m   m     next_sitpn0
           next_stpn stpn0 next_spn  spn
           places transs  enabled  pre  post  test  inhib 
           chronos chronos_incr
           next_chronos  scenario0 Tail  C  H0 H1 H2 H3 H4  H5 H6 H7.

    unfold sitpn_cycle.

    rewrite  H2. rewrite H1. rewrite H0. simpl.
    rewrite H3. simpl.
    unfold list_sensitized_spn in H4. rewrite H0 in H4.

    rewrite <- H4.
    rewrite <- H5. rewrite  <- H6. rewrite H7. reflexivity. 
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
                  (all_chronos (stpn   next_sitpn))
                  (transs (spn (stpn   next_sitpn))))
             ) 
               ::
               (sitpn_animate
                  next_sitpn
                  n')
  end.

Inductive sitpn_animate_spec
          (sitpn : SITPN)
  : nat ->
    list
      (list (list trans_type)  *
       list (place_type * nat) *
       (list (trans_type * option (nat * nat * nat)))) -> Prop :=
| animate_sitpn_O : sitpn_animate_spec
                    sitpn   O  [ ( [] , [] , [] ) ]
| animate_sitpn_S :
    forall (next_sitpn : SITPN)
           (Lol_fired : list (list trans_type))
           (m_visuel : list (place_type * nat))
           (chronos_visuels : list (trans_type * option (nat * nat * nat)))
           (n : nat)
           (TAIL : list (list (list trans_type) *
                         list (place_type * nat) *
                         (list (trans_type * option (nat * nat * nat))))),
     
      (Lol_fired, next_sitpn) = sitpn_cycle sitpn
      ->
      m_visuel = marking2list
                   (marking (spn (stpn next_sitpn)))
                   (places (spn  (stpn next_sitpn)))
      ->
      chronos_visuels = intervals2list
                          (all_chronos      (stpn next_sitpn))
                          (transs (spn  (stpn next_sitpn)))
                          
      ->
      sitpn_animate_spec
        next_sitpn    n    TAIL
      -> 
      sitpn_animate_spec
        sitpn   (S n)   ((Lol_fired, m_visuel, chronos_visuels) :: TAIL).

Functional Scheme sitpn_animate_ind :=
  Induction for sitpn_animate   Sort Prop.

Theorem sitpn_animate_correct :
  forall (sitpn   : SITPN)
         (n : nat)
         (digeste : list (list (list trans_type)  *
                       list (place_type * nat) *
                       list (trans_type * option (nat * nat * nat)))),
    sitpn_animate
      sitpn    n   =  digeste
    ->
    sitpn_animate_spec
      sitpn    n     digeste.
Proof.
  intros sitpn n.
  functional induction (sitpn_animate sitpn n)
             using sitpn_animate_ind.
  - intros digeste  H. rewrite <- H. apply animate_sitpn_O.
  - intros digeste  H. rewrite <- H.
    apply animate_sitpn_S with (next_sitpn := snd (sitpn_cycle sitpn)).
    + rewrite e0. simpl. reflexivity.
    + rewrite e0. simpl. reflexivity.
    + rewrite e0. simpl. reflexivity. 
    + rewrite e0. simpl. apply (IHl (sitpn_animate
                                       next_sitpn n')). reflexivity.
Qed. 
Theorem sitpn_animate_complete :
  forall (sitpn   : SITPN)
         (n : nat)
         (digeste : list (list (list trans_type)  *
                          list (place_type * nat) *
                          list (trans_type * option (nat * nat * nat)))),
    sitpn_animate_spec
      sitpn    n     digeste
    ->
    sitpn_animate
      sitpn    n   =  digeste.
Proof.
  intros. elim H.
  - simpl. reflexivity. 
  - intros. simpl.
    rewrite <- H0. rewrite <- H1. rewrite <- H2. rewrite <- H4.
    reflexivity.
Qed. 

Recursive Extraction  sitpn_animate.
Extraction "animator" sitpn_animate.