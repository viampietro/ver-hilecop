(***********************)
(**** by ML, DD, DA ****)
(***********************)

Require Export Arith Omega List Bool.
(* Require Import Nat. *)
Search nat. Search list.

(*********************************************************)
(***** Syntax of (generalized, extended) Petri nets ******)

Inductive place_type : Set :=
| mk_place : nat -> place_type.
(* places indexed by natural numbers *)

Inductive trans_type : Set :=
| mk_trans : nat -> trans_type.
(* transitions indices and constructor *)

(*   4 "TYPES" of arcs : pred, post, pred_inhib, pred_test 
    along with "some" weight   (default is 1 in real).       *)

Structure nat_star : Set := mk_nat_star
                              { int : nat ;
                                posi : int > 0 }.
(* a given arc has some weight >= 1 *)
Definition weight_type := trans_type -> place_type -> option nat_star.
(*  Why not this inductive definition with 4 constructors ????
Inductive arc_type : Set :=
| mk_arc_pt : place_type -> transition_type -> nat -> arc_type
| mk_arc_tp : transition_type -> place_type -> nat -> arc_type
(* extended (generalized = nat) Petri nets *)
| mk_arc_inhi : place_type -> transition_type -> nat -> arc_type
| mk_arc_test : place_type -> transition_type -> nat -> arc_type.
 *)

Definition marking_type := place_type -> nat.

(*****************************************************************)
(***  priority relation  ..................................   
  to DETERMINE the Petri net (along with imperative semantic) ***)

(*
Require Import Relations. Print relation. 
Search relation. Print transitive. 
Require Import RelationClasses. Print RelationClasses.
Print Asymmetric.

Inductive prior_type0 : Set :=
  mk_prior_type0 :
    forall (rel : trans_type -> trans_type -> bool),
      (forall (x : trans_type), (rel x x) = false) -> (* irreflexive *)
      (forall (x y : trans_type), (rel x y) = true -> (* asymmetric *)
                                  (rel y x = false)) ->
      (forall (x y z : trans_type), (rel x y) = true -> (* transitive *)
                                    (rel y z) = true ->
                                    (rel x z) = true) ->
      prior_type0.

(* transitive + asymmetric -> irreflexive ? 
   no cycle *)

Search list.
Print Equivalence. 
Definition prio_over0
           (t1 t2 : trans_type)
           (prior : prior_type1)
  : bool :=
  match prior with
  | mk_prior_type1
      rel
      asymm
      irref
      trans => if rel t1 t2
               then true
               else false
  end.
Notation "t1 >> t2" := (prio_over1 t1 t2 _)
                          (at level 50) : type_scope.
*)

Inductive prior_type : Set :=
  mk_prior { Lol : list (list trans_type) ; }.
    (*
      no_inter :
        forall (l1 l2 : list trans_type),
        forall (x : trans_type),
          (In l1 list_lists) -> (In l2 list_lists) ->
          (In x l1) -> (In x l2) ->
          (l1 = l2) ;  }.
  cover :
       forall (x : trans_type),
         (In x transs) ->
         exists (l : list trans_type),
           (In x l) -> (In l list_lists) }. *)

Print prior_type.


(*** fonctions en cours de construction, peut-etre utile ...   ***)
Definition prio_over
           (t1 t2 : trans_type)
           (prior : prior_type)
  : bool :=
  match prior with
  | mk_prior
      L
     (* no_inter
       cover *) => (* t1 devant t2 dans 1 m�me sous-liste 
                       Fixpoint ...  *)  false
  end.

(****************************************************************)
Print NoDup. Print nodup. Print NoDup_nodup. (* opaque proof ? *)
Print find_some.  (* maybe useful *)
(* split  / combine   ... *)

Structure SPN : Set := mk_SPN
                         {
                           places : list place_type ;
                           transs : list trans_type ;
                           nodup_places : NoDup places ;
                           nodup_transitions : NoDup transs ;
                           
                           pre : weight_type ;
                           post : weight_type ;
                           
                           test : weight_type ;
                           inhib : weight_type ;
                           
                           marking : marking_type ;
                           (* marking : list (place_type * nat)   
                            *)
                           priority : prior_type ; }.


(**************************************************************)
(************ are 2 nat/places/transitions equal ? ************)
Print beq_nat. Print Nat.eqb.
SearchPattern (forall x y : _, {x = y} + {x <> y}).
Print N.eq_dec.   (* awful but useful ! *) 
(* verify if 2 places have same index, return a boolean *)
Definition beq_places (p p' : place_type) : bool :=
  match (p, p') with
  | (mk_place n, mk_place n') => beq_nat n n'
  end.
(* verify if 2 transitions have same index, return a bool *)
Definition beq_transs (t t' : trans_type) : bool :=
  match (t, t') with
  | (mk_trans n, mk_trans n') => beq_nat n n'
  end.

Definition places_eq_dec : forall x y : place_type,
    {x = y} + {x <> y}.
Proof.
  decide equality.
  decide equality.
Defined.
Definition transs_eq_dec : forall x y : trans_type,
    {x = y} + {x <> y}.
Proof.
  decide equality.
  decide equality.
Defined.

Definition option_eq {A: Type} (eqA: forall (x y: A), {x=y} + {x<>y}):
  forall (x y: option A), {x=y} + {x<>y}.
Proof.
  decide equality.
Defined.
Global Opaque option_eq.  (*** ??? Defined/Qed  Opaque  Global  ***)


(**********************************************************)
(************ Semantics of these SPN   ********************)

(********** given a marking m, set j tokens in place p **********)
Print marking_type. Print place_type.
Definition set_mark (m:marking_type) (p:place_type) (j:nat)
  : marking_type :=
  fun p' =>  if beq_places p p'
             then j             (* set j tokens in place p *)
             else m p'.         (* other tokens left unchanged  *)
Definition reset (m:marking_type) (p:place_type) (j:nat)
  : marking_type := set_mark m p 0.     (*** reset a place ***)
(* useless for now...     
unlike reseting the local clocks... *)

(* given a marking m, add/remove j tokens inside place p *)  
Definition modif_mark
           (m : marking_type)
           (p : place_type)
           (j : option nat_star)  (** option nat because of weight_type **)
           (op : nat -> nat -> nat)
  : marking_type :=
  fun p' =>
    if beq_places p p'
    then match j with
          | None => m p              (* no change *)
          | Some i => match i with
                      | mk_nat_star
                          inti
                          carei => op (m p) inti     (* j=i tokens added/removed *)
                      end
         end
           
    else m p'.         (* other places left unchanged  *)

Print Nat.sub. Print Nat.add.   (** the 2 op(erators) to use ... **)
(* Require Import Nat. (* for Nat.leb != (Bool.)leb *) 
   library "Nat" is included into "Arith"  ? *)

(*************   update marking   *********************)
Fixpoint update_marking_pre
         (places : list place_type)
         (t : trans_type)
         (pre : weight_type)
         (m : marking_type)
  (* structural induction over list of places *)
  : marking_type :=
  match places with
  | nil => m
  | cons p tail => update_marking_pre
                     tail
                     t
                     pre
                     (modif_mark
                           m
                           p
                           (pre t p)
                           Nat.sub)
  end.

(**** downhill (output set, postset) ***)
Fixpoint update_marking_post
         (places : list place_type) 
         (t : trans_type)
         (post : weight_type)
         (m : marking_type)         
  (* structural induction over list of places *)
  : marking_type :=
  match places with
  | nil => m
  | cons p tail => update_marking_post
                     tail
                     t
                     post
                     (modif_mark
                           m
                           p
                           (post t p)
                           Nat.add)
  end.

Definition update_marking
           (places : list place_type) 
           (t : trans_type)
           (pre post : weight_type)
           (m : marking_type)         
  (* structural induction over list of places *)
  : marking_type :=
  update_marking_post
    places  
    t
    post
    (update_marking_pre
       places 
       t
       pre
       m).
(***** useless function !!!!
    because one has to decompose step by step 
 and fire several transitions in 1 step  ***)

(**********   to print the markings  ***********************)
(*** list the tokens !!!! ***)
Fixpoint marking2list
         (places : list place_type)
         (m : marking_type)
  : list (place_type * nat) :=
  match places with
  | nil => nil
  | p :: tail => (p, m p) :: (marking2list
                                tail m)
  end.


(****************************************************************)
(*** CHECKING IF there are enough tokens in predecessor places **)

Locate "<?". Print Nat.ltb. Print Nat.leb.
Print pre. Print weight_type.
(**** uphill (input set, preset) ***)
Fixpoint pre_or_test_check
         (places : list place_type)
         (pre_classic_or_test_t : place_type -> option nat_star)
         (** "classic" and "test" arcs **)
         (m : marking_type)
  : bool :=
  match places with
  | nil => true
  | cons h tail => match pre_classic_or_test_t h with
                   | None => pre_or_test_check
                               tail
                               pre_classic_or_test_t
                               m
                   | Some n => match n with
                               | mk_nat_star
                                   int 
                                   careful =>
                                 (int <=? (m h))
                                   &&
                                   (pre_or_test_check
                                      tail
                                      pre_classic_or_test_t
                                      m)
                               end
                   end
  end.

Fixpoint inhib_check
         (places : list place_type)
         (pre_inhi_t : place_type -> option nat_star) (* inhibitor arcs *)
         (m : marking_type)
  : bool :=
  match places with
  | nil => true
  | cons h tail => match pre_inhi_t h with
                   | None => inhib_check
                               tail
                               pre_inhi_t
                               m
                   | Some n => match n with
                               | mk_nat_star
                                   int 
                                   careful =>
                                 ((m h) <? int)
                                   &&
                                   (inhib_check
                                      tail
                                      pre_inhi_t
                                      m)
                               end
                   end
  end.

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
   checking arcs with different markings ... 
 --->    useful only for _asynchronous_ Petri nets **)

(**   useless fonction ?  
needed to list the enabled transitions :

1) to increment time, at the beginning of the cycle

2) to reset disabled transitions during "fire_pre"
*)



(*****************************************************************)
(*********   FIRING ALGORITHM    for SPN      ********************)

Export ListNotations.
Check update_marking_pre.
(** given 1 ordered class of transitions 
in structural conflict (a list class_of_transs), 
return 1 list of transitions "subclass_half_fired" 
and marking "m_intermediate" accordingly ...   *)
Fixpoint spn_sub_fire_pre
         (places : list place_type)
         (pre test inhib : weight_type)  (* 3 *)
         (m_init m_intermediate : marking_type)    (* 2 *)
         (class_transs subclass_half_fired : list trans_type) (* 2 *)
         (* "subclass_half_fired"  is meant to be empty at first *) 
  : (list trans_type) * marking_type :=
  match class_transs with
  | t :: tail => if (pre_or_test_check
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
                 then spn_sub_fire_pre
                        places pre test inhib
                        m_init (update_marking_pre
                                  places t pre m_intermediate)
                        tail (subclass_half_fired ++ [t])
                        (* concatener derriere pour garder ordre *)
                 else spn_sub_fire_pre
                        places pre test inhib
                        m_init m_intermediate
                        tail subclass_half_fired
  | []  => (subclass_half_fired, m_intermediate)
  end.
(* 
there are 2 parallel calculus in this function : 
1) pumping tokens to get "m_intermediate"  (half fired)
2) returning subclass of transitions (half fired)
and 2 markings are recorded : 
1) the initial one to check with inhib and test arcs
2) a floating (decreasing) intermediate marking to check classic arcs
*)

(*
 given a marking "m_intermediate" got by above,
after a given subclass of transs has been half fired, 
and this list of transitions "subclass_half_fired", 
 returns the marking increased by the post arcs  
*)
Fixpoint sub_fire_post
         (places : list place_type)
         (post : weight_type)
         (m_intermediate : marking_type)
         (subclass_half_fired : list trans_type)  
  : marking_type := 
  match subclass_half_fired with
  | []  => m_intermediate
  | t :: tail  => sub_fire_post
                    places post
                    (update_marking_post
                       places t post m_intermediate)
                    tail
  end.

(*
 Apply sub_fire_pre over ALL classes of transitions. 
 Begin with initial marking, 
  end with half fired marking.  
 "classes_half_fired" is empty at first 
 (a bit like for sub_fire_pre) 
*)
Fixpoint spn_fire_pre
         (places : list place_type)
         (pre test inhib : weight_type)
         (marking : marking_type)
         (classes_transs classes_half_fired : list (list trans_type))
  : (list (list trans_type))   * marking_type :=
  match classes_transs with
  | [] => (classes_half_fired , marking)
  | l :: Ltail => let m := (snd (spn_sub_fire_pre
                                  places  pre test inhib
                                  marking marking
                                  l []))
                  in
                  spn_fire_pre
                    places  pre test inhib
                    m
                    Ltail
                    ((fst (spn_sub_fire_pre
                             places  pre test inhib
                             marking marking
                             l [])) :: classes_half_fired)         
  end.

Print SPN.  (*** for nice prints  only  !  **)
Definition fire_pre_print
           (places : list place_type) (pre test inhib : weight_type)
           (marking : marking_type)
           (classes_transs classes_half_fired : list (list trans_type))
  : (list (list trans_type)) * list (place_type * nat) :=
  let res := (spn_fire_pre
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



(* 
 Begin with intermediate marking
 (computed above by "fire_pre" ,
 after half (pre arcs) firing ALL the transitions choosen),
 End with the _final_ marking !   Houra ! *)
Fixpoint fire_post
         (places : list place_type)
         (post : weight_type)
         (marking_half : marking_type)
         (subclasses_half_fired : list (list trans_type))
  : marking_type := 
  match subclasses_half_fired with
  | []  => marking_half
  | l :: Ltail  => fire_post
                     places post
                     (sub_fire_post
                        places post
                        marking_half
                        l)
                     Ltail                     
  end. 


(* Returns  [transitions fired + final marking] *)
Definition spn_fire  
           (places : list place_type)
           (pre test inhib post : weight_type)
           (m_init : marking_type)
           (classes_transs : list (list trans_type))
  : (list (list trans_type)) * marking_type :=
  let res := spn_fire_pre
               places  pre test inhib 
               m_init
               classes_transs []
  in
  ( (fst res) , fire_post
                  places post
                  (snd res)
                  (fst res) ).


(**************************************************)
(************* to animate a SPN   *****************)


Print SPN. Print prior_type.
(* Only the marking is evolving ! 
but we want to keep trace of the fired transitions ! *)
Definition spn_fired (spn : SPN)
   : (list (list trans_type)) * SPN :=
  ((fst
      (spn_fire
         (places spn)
         (pre spn)
         (test spn)
         (inhib spn)
         (post spn)
         (marking spn)
         match (priority spn) with
         | mk_prior
             (* partition *)
             Lol => Lol
         end
      )
   ) ,
   (mk_SPN
      (places spn)
      (transs spn)
      (nodup_places spn)
      (nodup_transitions spn)
      (pre spn)
      (post spn)
      (test spn)
      (inhib spn)
      (* marking *)
      (snd
         (spn_fire
            (places spn)
            (pre spn)
            (test spn)
            (inhib spn)
            (post spn)
            (marking spn)
            match (priority spn) with
            | mk_prior
                (* partition *)
                Lol => Lol
            end
      ))
      (priority spn))
  ).

Check spn_fired.
(* n steps calculus  *)   
Fixpoint animate_spn
         (spn : SPN)
         (n : nat)
  : list
      (list (list trans_type)  *
       list (place_type * nat) ) :=
  match n with
  | O => [ ( [] , marking2list
                    (places spn)
                    (marking spn) ) ]
  | S n' =>  let next_spn := (spn_fired spn) in
             ( (fst next_spn) ,
               (marking2list
                  (places (snd next_spn))
                  (marking (snd next_spn))) ) 
               ::
               (animate_spn
                  (snd next_spn)
                  n')
  end.    (* split / combine ... *)
           

(****************************************************************)
(******************** to print and test with the eye ************)
Print marking_type.
Search list.


Definition fire_spn_listing (spn : SPN) :=
  marking2list
    (places spn)
    (marking (snd (spn_fired spn))).


(******************************************************************)
(******************************************************************)
(****   example of David Andreu       written within TINA    ******)
(******************************************************************)

Print NoDup. Print nodup. Print NoDup_nodup. (* opaque proof ? *)
(* 3 places *)
Definition ex_places : (list place_type) :=
  nodup
    places_eq_dec
    [ mk_place 0 ;
      mk_place 1 ;
      mk_place 2 ;
      mk_place 3 ;
      mk_place 4 ;
      mk_place 5 ; (* 6 is missing *)
      mk_place 7 ; 
      mk_place 8 ;
      mk_place 9 ;
      mk_place 10 ;
      mk_place 11 ;
      mk_place 12 ].
Definition ex_nodup_places : NoDup ex_places :=
  NoDup_nodup
    places_eq_dec
    ex_places. 

(* 3 transitions *)
Definition ex_transs : (list trans_type) :=
  [ mk_trans 0 ;
    mk_trans 1 ;
    mk_trans 2 ;
    mk_trans 3 ;
    mk_trans 4 ;
    mk_trans 5 ;
    mk_trans 6 ;  (* 7 is missing *)
    mk_trans 8 ;
    mk_trans 9 ;  (* 10, 11 are missing *)
    mk_trans 12 ;
    mk_trans 13 ;
    mk_trans 14 ; (* 15 is missing *)
    mk_trans 16 ].
Definition ex_nodup_transs : NoDup ex_transs :=
  NoDup_nodup
    transs_eq_dec
    ex_transs. 

(**********************************************)
Print nat_star. Print weight_type.
Lemma one_positive : 1 > 0. Proof. omega. Qed.
Lemma two_positive : 2 > 0. Proof. omega. Qed.
(* one lemma for each arc weight ... *)

(* many arcs PT (place transition)  "incoming" *) 
Definition ex_pre (t : trans_type) (p : place_type)
  : option nat_star :=
  (* transitions 7, 10, 11, 15  missing *)
  (* place 6 missing *)
  match (t,p) with
  (* trans 0 *)
  | (mk_trans 0, mk_place 0) => Some (mk_nat_star
                                        1
                                        one_positive)               
  | (mk_trans 0, mk_place 7) => Some (mk_nat_star
                                        1
                                        one_positive)               
  | (mk_trans 0, mk_place 12) => Some (mk_nat_star
                                        1
                                        one_positive)
  (* trans 1 *)
  | (mk_trans 1, mk_place 1) => Some (mk_nat_star
                                        1
                                        one_positive)
  (* trans 2 *)
  | (mk_trans 2, mk_place 2) => Some (mk_nat_star
                                        1
                                        one_positive)
  (* trans 3 *)
  | (mk_trans 3, mk_place 3) => Some (mk_nat_star
                                        1
                                        one_positive)
  (* trans 4 *)
  | (mk_trans 4, mk_place 4) => Some (mk_nat_star
                                        1
                                        one_positive)
  (* trans 5 *)
  | (mk_trans 5, mk_place 5) => Some (mk_nat_star
                                        1
                                        one_positive)
  (* trans 6 *)
  | (mk_trans 6, mk_place 8) => Some (mk_nat_star
                                        1
                                        one_positive)
  | (mk_trans 6, mk_place 9) => Some (mk_nat_star
                                        1
                                        one_positive)
  (* trans 8 *)
  | (mk_trans 8, mk_place 10) => Some (mk_nat_star
                                        2
                                        two_positive)
  (* trans 9 *)
  | (mk_trans 9, mk_place 11) => Some (mk_nat_star
                                        1
                                        one_positive)
  (* trans 12 *)
  | (mk_trans 12, mk_place 1) => Some (mk_nat_star
                                        1
                                        one_positive)
  (* trans 13 *)
  | (mk_trans 13, mk_place 11) => Some (mk_nat_star
                                        1
                                        one_positive)
  (* trans 14 *)
  | (mk_trans 14, mk_place 11) => Some (mk_nat_star
                                        1
                                        one_positive)
  (* trans 16 *)
  | (mk_trans 16, mk_place 3) => Some (mk_nat_star
                                        1
                                        one_positive)
  | (mk_trans 16, mk_place 10) => Some (mk_nat_star
                                        1
                                        one_positive)
  | _ => None
  end.

(* many  arcs TP       "outcoming" *)
Definition ex_post (t : trans_type) (p : place_type)
  : option nat_star :=
  (* transitions 7, 10, 11, 15  missing *)
  (* place 6 missing *)
  match (t, p) with
  (* trans 0 *)
  | (mk_trans 0, mk_place 4) => Some (mk_nat_star
                                        1
                                        one_positive)               
  | (mk_trans 0, mk_place 5) => Some (mk_nat_star
                                        1
                                        one_positive)               
  | (mk_trans 0, mk_place 12) => Some (mk_nat_star
                                        1
                                        one_positive)
  (* trans 1 *)
  | (mk_trans 1, mk_place 2) => Some (mk_nat_star
                                        1
                                        one_positive)
  (* trans 2 *)
  | (mk_trans 2, mk_place 3) => Some (mk_nat_star
                                        1
                                        one_positive)
  (* trans 3 *)
  | (mk_trans 3, mk_place 1) => Some (mk_nat_star
                                        1
                                        one_positive)
  (* trans 4 *)
  | (mk_trans 4, mk_place 8) => Some (mk_nat_star
                                        1
                                        one_positive)
  (* trans 5 *)
  | (mk_trans 5, mk_place 9) => Some (mk_nat_star
                                        1
                                        one_positive)
  (* trans 6 *)
  | (mk_trans 6, mk_place 10) => Some (mk_nat_star
                                        1
                                        one_positive)
  (* trans 8 *)
  | (mk_trans 8, mk_place 11) => Some (mk_nat_star
                                        1
                                        one_positive)
  (* trans 9 *)
  | (mk_trans 9, mk_place 0) => Some (mk_nat_star
                                        2
                                        two_positive)
  (* trans 12 *)
  | (mk_trans 12, mk_place 2) => Some (mk_nat_star
                                        1
                                        one_positive)
  (* trans 13 *)
  | (mk_trans 13, mk_place 0) => Some (mk_nat_star
                                         2
                                         two_positive)
  (* trans 14 *)
  | (mk_trans 14, mk_place 0) => Some (mk_nat_star
                                         2
                                         two_positive)
  (* trans 16 *)
  | (mk_trans 16, mk_place 3) => Some (mk_nat_star
                                        1
                                        one_positive)
  | (mk_trans 16, mk_place 10) => Some (mk_nat_star
                                        1
                                        one_positive)
  | _ => None
  end.

(*************************************)
(*** tokens of the initial marking ***)
Definition ex_marking (p : place_type) :=
  match p with
  | mk_place 0 => 2
  | mk_place 1 => 2
  | mk_place 7 => 1
  | mk_place 12 => 1
  | _ => 0
  end. Print ex_marking. Check marking_type.
(* ? reductions, simplifications ? *)

Print SPN.
Definition ex_test (t : trans_type) (p : place_type) :=
  (* transitions 7, 10, 11, 15  missing *)
  (* place 6 missing *)
  match (t, p) with
  (* trans 5 *)
  | (mk_trans 5, mk_place 2) => Some (mk_nat_star
                                        1
                                        one_positive)               
  | (mk_trans 5, mk_place 12) => Some (mk_nat_star
                                        1
                                        one_positive)
  | _ => None
  end.

(* many  arc of type "inhibitor"  *)
Definition ex_inhib (t : trans_type) (p : place_type) :=
  (* transitions 7, 10, 11, 15  missing *)
  (* place 6 missing *)
  match (t, p) with
  (* trans 2 *)
  | (mk_trans 2, mk_place 5) => Some (mk_nat_star
                                        1
                                        one_positive)               
  (* trans 4 *)
  | (mk_trans 4, mk_place 11) => Some (mk_nat_star
                                         1
                                         one_positive)               
  | _ => None
  end.

(*
Definition ex_prior1 (t1 t2 : trans_type) : bool :=
  (* transitions squared  ---> lot's of match branches ... *)
  match (t1 , t2) with
  | (mk_trans 0, mk_trans 0) => false
  | (mk_trans 0, mk_trans 1) => true
  | (mk_trans 0, mk_trans 2) => true
  | (mk_trans 1, mk_trans 0) => false
  | (mk_trans 1, mk_trans 1) => false
  | (mk_trans 1, mk_trans 2) => true
  | (mk_trans 2, mk_trans 0) => false
  | (mk_trans 2, mk_trans 1) => false
  | (mk_trans 2, mk_trans 2) => false
  | (_,_) => false  (* False or True     who care ? -> option bool?*) 
  end.    *)

Print prior_type.
Definition ex_prior_aux :=
  [
    [mk_trans 1 ; mk_trans 12] ;
    [mk_trans 0 ; mk_trans 2 ; mk_trans 5] ;
    [mk_trans 3 ; mk_trans 8 ; mk_trans 16] ;
    [mk_trans 4 ; mk_trans 9 ; mk_trans 13 ; mk_trans 14] ;
    [mk_trans 6]
  ].
Definition ex_prior :=
  mk_prior
    ex_prior_aux.    
    
Print pre. Print weight_type.
Definition ex_spn := mk_SPN
                      ex_places
                      ex_transs
                      ex_nodup_places
                      ex_nodup_transs
                      
                      ex_pre
                      ex_post
                      ex_test
                      ex_inhib                 
                      
                      ex_marking
                      ex_prior.

Check ex_spn. Compute (marking ex_spn). (* initial marking *)

Search SPN.
Compute (animate_spn
           ex_spn
           10).  (* 11 markings *)

(******** deuxi�me exemple (permutation des sous-listes)  **********)

Definition ex_prior_aux2 :=
  [
    [mk_trans 1 ; mk_trans 12] ;
    [mk_trans 2 ; mk_trans 0 ; mk_trans 5] ;
    [mk_trans 16 ; mk_trans 8 ; mk_trans 3] ;
    [mk_trans 9 ; mk_trans 4 ; mk_trans 14 ; mk_trans 13] ;
    [mk_trans 6]
  ].
Definition ex_prior2 :=
  mk_prior
    ex_prior_aux2.    
Definition ex_spn2 := mk_SPN
                        ex_places
                        ex_transs
                        ex_nodup_places
                        ex_nodup_transs
                        
                        ex_pre
                        ex_post
                        ex_test
                        ex_inhib                 
                        
                        ex_marking
                        ex_prior2.
Compute (animate_spn
           ex_spn2
           10).  (* 11 markings *)

(********  SPN numero 3  (apres permuation des sous-listes)  ******)
Definition ex_prior_aux3 :=
  [
    [mk_trans 12 ; mk_trans 1] ;
    [mk_trans 0 ; mk_trans 2 ; mk_trans 5] ;
    [mk_trans 16 ; mk_trans 3 ; mk_trans 8] ;
    [mk_trans 9 ; mk_trans 14 ; mk_trans 4 ; mk_trans 13] ;
    [mk_trans 6]
  ].
Definition ex_prior3 :=
  mk_prior
    ex_prior_aux3.    
Definition ex_spn3 := mk_SPN
                        ex_places
                        ex_transs
                        ex_nodup_places
                        ex_nodup_transs
                        
                        ex_pre
                        ex_post
                        ex_test
                        ex_inhib                 
                        
                        ex_marking
                        ex_prior3.
Compute (animate_spn
           ex_spn3
           10).  (* 11 markings *)


(********   debuggage   ******)

Compute (fire_spn_listing
           ex_spn).  (* donne juste le marquage final *)

(*************************************************************
**************************************************************
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

Search trans_type. 
Fixpoint in_list_enabled    (* must exist in library List *)
         (enabled_transs : list trans_type)
         (trans : trans_type)
  : bool :=
  match enabled_transs with
  | [] => false
  | t :: tail => if (beq_transs trans t)
                 then true
                 else false
  end.  

(************************************ TIME clocks, counters ***)
(****** need to increment only _enabled_ transitions ??? ****)

(* Fixpoint list_enabled
         (places : list place_type)
         (pre test inhib : weight_type)
         (m : marking_type)   (* the marking got at the end !!! *)
         (transs enabled_transs : list trans_type) (*input/output*)
  : list trans_type :=
*)
Print STPN. Print chronos.
Fixpoint increment_time
         (chronos : trans_type -> option chrono_type)
         (enabled_transs : list trans_type)
  : trans_type -> option chrono_type :=
  
  match enabled_transs with
  | [] => chronos
  | t :: tail =>   match (chronos t) with
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
 2) pour quelles transitions faut-il le faire ?
 *)

(* reset time counters of several transitions ... *)
Fixpoint reset_time_list
           (chronos : trans_type -> option chrono_type)
           (subclass : list trans_type)
  : trans_type -> option chrono_type :=

  match subclass with
  | [] => chronos
  | t :: tail => reset_time_list
                   (reset_time
                      chronos
                      t)
                   tail
  end.


(*****************************************************************)
(*********   FIRING ALGORITHM    for SPN      ********************)

Print STPN.
Check update_marking_pre.
(** given 1 ordered class of transitions 
in structural conflict (a list class_of_transs), 
return 1 list of transitions "subclass_half_fired" 
and marking "m_intermediate" accordingly ...   *)
Fixpoint stpn_sub_fire_pre
         (places : list place_type)
         (pre test inhib : weight_type)  (* 3 *)
         (m_init m_intermediate : marking_type)    (* 2 *)
         (* to reset clocks .. *)
         (enabled_transs : list trans_type)
         (intervals : trans_type -> option chrono_type)
         (* to reset clocks .. *)
         (class_transs subclass_half_fired : list trans_type) (* 2 *)
         (* "subclass_half_fired"  is meant to be empty at first *) 
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
  | l :: Ltail => let '(sub_l, new_m, new_i) := stpn_sub_fire_pre
                                                  places
                                                  pre test inhib
                                                  marking marking
                                                  enabled_transs
                                                  chronos
                                                  l []
                  in
                  stpn_fire_pre
                    places
                    pre  test  inhib
                    new_m
                    enabled_transs  new_i
                    Ltail
                    (sub_l :: classes_half_fired)         
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
    marking_type *
    (trans_type -> option chrono_type)  :=

  let '(L, m, i) := stpn_fire_pre
                      places  pre test inhib 
                      m_init
                      enabled_transs  chronos
                      classes_transs []
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
Print list_enabled. Print STPN. Print SPN.
Definition stpn_cycle (stpn : STPN)
           
  : (list (list trans_type)) * STPN  :=

  match stpn with
  | mk_STPN
      (mk_SPN
         places
         transs
         nodup_places 
         nodup_transitions           
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
                      nodup_places 
                      nodup_transitions 
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
(************* to animate a STPN   *****************)

(* n steps calculus  *)
Print STPN. Check intervals2list.
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

Check ex_stpn. Compute (marking (spn
                                   ex_stpn)). (* initial marking *)

Search STPN.
Compute (animate_stpn
           ex_stpn
           10).  (* 11 markings *)





(*
(*****************************************************************)
(**** HOW TO get the classes of transitions...    from what ? ****)
(*************** sections sorting ********************************)

Require Import Coq.Sorting.Sorted. Search sort.

Section insertion_sort.


  Print prior_type1. Print prior_type2.
  Fixpoint insert
           (a : trans_type)
           (l : list trans_type)
           (prior1 : prior_type1)
  : list trans_type :=
    match l with
    | nil  => [a]
    | b::l' => match prior1 with
               | mk_prior_type1
                   rel
                   irre
                   assym
                   trans => if (rel a b)
                            then a :: l
                            else b :: (insert
                                         a l' prior1)
               end
    end.
  
  Fixpoint sort
           (l: list trans_type)
           (prior1 : prior_type1)
    : list trans_type :=
    match l with
    | [ ] => [ ]
    | a::l' => insert
                 a (sort l' prior1) prior1
    end.
  
  (* Fixpoint find_highest (A:Type) (l:list A) : (A * list A) :=
    match l with
    | nil => (a, nil)
    | b::l' => if leb a b
               then find_highest b l'
               else find_highest a l'
    end.*)

  Definition sort_transs
             (prior1 : prior_type1)
             (l : list trans_type)
    : list trans_type :=
    sort
      l
      prior1.
  
End insertion_sort.

(********************************************************)

Section structural_conflicts.
  Variable pre : weight_type.
  (* Variable places : list place_type. *)

  Fixpoint common_pre
           (t t' : trans_type)
           (places : list place_type)
    : bool :=
    match places with
    | [ ] => false
    | p :: places' => match ((pre t p), (pre t' p)) with
                      | (Some _, Some _) => true
                      | (_, _) => common_pre
                                    t t'
                                    places'                                  
                      end
    end.

  Fixpoint common_pre_with_somebody
           (t : trans_type) (sometranss : list trans_type)
           (places : list place_type)
    : bool :=
    match sometranss with
    | [ ] => false
    | tr :: lesstranss => if common_pre
                               t tr
                               places
                          then true
                          else common_pre_with_somebody
                                 t lesstranss
                                 places
    end.

  Fixpoint somebody_common_pre_with_somebody
           (sometranss1 sometranss2 : list trans_type)
           (places : list place_type)
    : bool :=
    match sometranss1 with
    | [ ] => false
    | t :: lesstranss1 => if common_pre_with_somebody
                               t sometranss2
                               places
                          then true
                          else somebody_common_pre_with_somebody
                                 lesstranss1 sometranss2
                                 places
  end.    

  Search list.
  Section fusionning_lists.
    Variables (A : Type).
    
    Fixpoint fusion_two_lists
             (L : list (list A))
             (l1 l2 : list A)
      (* l1 , l2  in L *)
      : list (list A) :=
      (*match L with
    | l1 :: L'  => fusion_two_lists
                     L'
                     l1 l2
    | l2 :: L'  => fusion_two_lists
                     L'
                     l1 l2
    | _ :: L'   => fusion_two_lists
                     L
                     l1 l2
    | [ ]      => (l1 ++ l2) :: L 
    end.*)
      [].
  End fusionning_lists.
  
  Fixpoint merging_list_in_list_of_lists
           (L : list (list trans_type))      
           (sometranss1 : list trans_type)
           (places : list place_type) {struct L}
    : list (list trans_type) :=
    match L with
    | [] => L
    | sometranss2 :: L' => if somebody_common_pre_with_somebody
                                sometranss1 sometranss2
                                places
                           then ((sometranss1 ++ sometranss2) :: L')
                                  
                           else sometranss2 :: (merging_list_in_list_of_lists
                                                  L'
                                                  sometranss1
                                                  places)
  end.

  Definition building_structural_conflicts
             (transs : list (list trans_type))
             (places : list place_type)
    : list (list trans_type) :=
    match transs with
    | []  => transs
    | l :: tail  => merging_list_in_list_of_lists
                      tail
                      l
                      (places : list place_type)
    end.

End structural_conflicts.

Section effective_conflicts.
  Variable struct_conflicts : list (list trans_type).
  Variable firable_transs : list trans_type.

  Fixpoint conforming_data_pruning
           (struct_conflicts : list (list trans_type))
           (firable_transs : list trans_type)
    : list (list trans_type) :=
    [].
  (* il suffit de garder de struct_conflicts
  en supprimant toutes les transitions n'apparaissant pas dans firable_transs *)

  Print SITPN.
  Fixpoint conforming_data_ordering
           (firable_transs : list (list trans_type)) (* better *)
           (priority : prior_type2)
    : list (list trans_type) :=
    [].
  (* il suffit d'ordonner chacune des listes *)


  Definition to_be_fired
             (conformed_firable : list (list trans_type))
             (sitpn : SITPN)
    : SITPN :=
    sitpn.
  (* on peut tirer les transitions autant que possible 
 il suffit de tirer les premi�res de listes (updating le marking)
en retirant les transitions suivantes qui ne sont plus tirables
 
et en recomman�ant avec la liste de listes restante
qui n'est pas forcement plus courte (zut !) *)

  
End effective_conflicts.

*)
