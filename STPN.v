(***********************)
(**** by ML, DD, DA ****)
(***********************)

Require Import Arith Omega List Bool.
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

Inductive prior_type : Set :=
  mk_prior_type { Lol : list (list trans_type) ; }.
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
  | mk_prior_type
      L
     (* no_inter
       cover *) => (* t1 devant t2 dans 1 même sous-liste 
                       Fixpoint ...  *)  false
  end.

(****************************************************************)
Print NoDup. Print nodup. Print NoDup_nodup. (* opaque proof ? *)
Print find_some.  (* maybe useful *)
(* split  / combine   ... *)

(* Structure SPN : Set := mk_SPN  ... *)                        

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

Structure interval_type : Set :=
  mk_inter
    {
      mini : nat_star ; (* no [0, in synchronous time Petri nets !*) 
      maxi : nat_star ;
      min_le_max : mini o<= maxi  ;
      cpt  : nat ;   (* nat_star ? *)
      (* in_range  : bool      mini <= cpt <= maxi ; *)
    }.

Structure STPN : Set := mk_STPN
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
                             priority : prior_type ;
                             intervals :
                               trans_type ->
                               option interval_type ;}.

(* there is an interval iff there is a local clock *)
(*** but if conditions are meant to evolve through time .... *)

Print STPN.

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

(**********   TO PRINT the markings  ***********************)
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
           (pre test inhib : weight_type)
           (m : marking_type)
  : trans_type -> bool :=  
  fun t => (pre_or_test_check places (pre t) m)
             &&
             (pre_or_test_check places (test t) m)
             &&
             (inhib_check places (inhib t) m). 
(**   useless fonction ?  (unless for STPN and SITPN ...)
 because 
 firing a bunch of transitions synchronously implies
   checking arcs with different markings ... 
 --->    useful only for _asynchronous_ Petri nets **)

Import ListNotations.
Fixpoint list_enabled
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
                 then list_enabled
                        places
                        pre test inhib
                        m
                        tail (t::enabled_transs)
                 else list_enabled
                        places
                        pre test inhib
                        m
                        tail enabled_transs
  end.

Search trans_type.
Fixpoint in_list_enabled
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
Print STPN. Print interval_type.
Definition increment_time
           (intervals : trans_type -> option interval_type)
  : trans_type -> option interval_type :=
  fun trans =>
    match (intervals trans) with
    | Some (mk_inter        (* immutable ... *)
              mini
              maxi
              min_le_max
              cpt ) => Some (mk_inter
                               mini
                               maxi
                               min_le_max
                               (cpt + 1))
    | None => None
    end.

Definition reset_time
           (intervals : trans_type -> option interval_type)
           (t : trans_type)
  : trans_type -> option interval_type :=
  match (intervals t) with
  | None  => intervals
  | Some inter => match inter with
                  | mk_inter
                      mini
                      maxi
                      min_le_max
                      cpt => (fun trans =>
                                if beq_transs
                                     trans t
                                then Some (mk_inter
                                             mini
                                             maxi
                                             min_le_max
                                             0   (* 1 ? *) )
                                else (intervals trans)
                             )             
                  end
  end.



(*****************************************************************)
(*********   FIRING ALGORITHM    for SPN      ********************)

Print STPN.
Check update_marking_pre.
(** given 1 ordered class of transitions 
in structural conflict (a list class_of_transs), 
return 1 list of transitions "subclass_half_fired" 
and marking "m_intermediate" accordingly ...   *)
Fixpoint sub_fire_pre
         (places : list place_type)
         (pre test inhib : weight_type)  (* 3 *)
         (m_init m_intermediate : marking_type)    (* 2 *)
         (* to reset clocks .. *)
         (enabled_transs : list trans_type)
         (intervals : trans_type -> option interval_type)
         (* to reset clocks .. *)
         (class_transs subclass_half_fired : list trans_type) (* 2 *)
         (* "subclass_half_fired"  is meant to be empty at first *) 
  : (list trans_type) *
    marking_type *
    (trans_type -> option interval_type) :=
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
                 then sub_fire_pre
                        places pre test inhib
                        m_init (update_marking_pre
                                  places t pre m_intermediate)
                        enabled_transs  intervals
                        tail (subclass_half_fired ++ [t])
                        (* concatener derriere pour garder ordre *)
                 else if in_list_enabled
                           enabled_transs
                           t
                      then (* reset the local counter *)
                        sub_fire_pre
                          places pre test inhib
                          m_init m_intermediate
                          enabled_transs
                          (reset_time
                             intervals
                             t )
                          tail subclass_half_fired
                      else
                        sub_fire_pre
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
Print nth.
Fixpoint fire_pre
         (places : list place_type)
         (pre test inhib : weight_type)
         (marking : marking_type)
         (* ......... to reset clocks .................. *)
         (enabled_transs : list trans_type)
         (intervals : trans_type -> option interval_type)
         (* .......... to reset clocks ................. *)
         (classes_transs classes_half_fired : list (list trans_type))
  : (list (list trans_type)) *
    marking_type *
    (trans_type -> option interval_type)  :=
  match classes_transs with
  | [] => (classes_half_fired , marking, intervals)
  | l :: Ltail => let '(sub_l, m, i) := sub_fire_pre
                                          places  pre test inhib
                                          marking marking
                                          enabled_transs intervals
                                          l []
                  in
                  fire_pre
                    places  pre  test  inhib
                    m
                    enabled_transs  i
                    Ltail
                    (sub_l :: classes_half_fired)         
  end.

(***************************************** warning :  

il faut _checker_ que les transitions sont bien in_range

et il faut incrémenter TOUTES les transitions 
(avec des clocks & intervalles) juste après le tir (0 -> 1 -> ...)

************************************************************)








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
Definition fire  
           (places : list place_type)
           (pre test inhib post : weight_type)
           (m_init : marking_type)
           (* ......... to reset clocks .................. *)
           (enabled_transs : list trans_type)
           (intervals : trans_type -> option interval_type)
           (* .......... to reset clocks ................. *)
           (classes_transs : list (list trans_type))
  : (list (list trans_type)) *
    marking_type *
    (trans_type -> option interval_type)  :=
  let '(L, m, i) := fire_pre
                      places  pre test inhib 
                      m_init
                      enabled_transs  intervals
                      classes_transs []
  in
  ( L ,
    fire_post
      places post
      m
      L ,
    i  ).


(**************************************************)
(************* to animate a SPN   *****************)


Print STPN. Print prior_type. Print list_enabled. Print fire.
(* Only the marking is evolving ! 
but we want to keep trace of the fired transitions ! *)
Definition stpn_fired (stpn : STPN)
   : (list (list trans_type)) * STPN :=

  let '(L,m,i) := fire
                    (places stpn)
                    (pre stpn) (test stpn) (inhib stpn)
                    (post stpn)
                    (marking stpn)
                    (list_enabled
                       (places stpn)
                       (pre stpn)
                       (test stpn)
                       (inhib stpn)
                       (marking stpn)
                       (transs stpn)
                       [])
                    (intervals stpn)
                    match (priority stpn) with
                    | mk_prior_type
                        (* partition *)
                        Lol => Lol
                    end
                    
  in
  (L ,
   (mk_STPN
      (places stpn)
      (transs stpn)
      (nodup_places stpn)
      (nodup_transitions stpn)
      (pre stpn)
      (post stpn)
      (test stpn)
      (inhib stpn)
      (* marking *)
      m
      (priority stpn)
      i)
  ).

Check increment_time.  (************* not to forget 
but of all the transitions or of just the new enabled transitions
********)

Check stpn_fired.
(* n steps calculus  *)   
Fixpoint animate_stpn
         (stpn : STPN)
         (n : nat)
  : list
      (list (list trans_type)  *
       list (place_type * nat) ) :=
  match n with
  | O => [ ( [] , marking2list
                    (places stpn)
                    (marking stpn) ) ]
  | S n' =>  let (L, next_stpn) := (stpn_fired stpn)
             in
             ( L ,
               (marking2list
                  (places next_stpn)
                  (marking next_stpn)) ) 
               ::
               (animate_stpn
                  next_stpn
                  n')
  end.    (* split / combine ... *)
           

(****************************************************************)
(******************** to print and test with the eye ************)
Print marking_type.
Search list.

(*  OLD
Definition fire_spn_listing (spn : SPN) :=
  marking2list
    (places spn)
    (marking (snd (spn_fired spn))).
*)


(******************************************************************)
(***** David Andreu's first example (redrawn in my Oxford) ********)

(* 7 places *)
Definition ex_places : (list place_type) :=
  [ mk_place 1 ;
    mk_place 2 ;
    mk_place 3 ;
    mk_place 4 ;
    mk_place 5 ;
    mk_place 6 ;
    mk_place 7 ].
Definition ex_nodup_places : NoDup ex_places :=
  NoDup_nodup
    places_eq_dec
    ex_places. 

(* 6 transitions *)
Definition ex_transs : (list trans_type) :=
  [ mk_trans 1 ;
    mk_trans 2 ;
    mk_trans 3 ;
    mk_trans 4 ;
    mk_trans 5 ;
    mk_trans 6 ].
Definition ex_nodup_transs : NoDup ex_transs :=
  NoDup_nodup
    transs_eq_dec
    ex_transs. 

(* 7 arcs PT (place transition)  "incoming" *) 
Definition ex2_pre_function (t : trans_type) (p : place_type) :=
  match (t, p) with
  | (mk_trans 0, mk_place 0) => Some 1
  | (mk_trans 1, mk_place 0) => Some 1
  | (mk_trans 2, mk_place 2) => Some 2
  | (mk_trans 2, mk_place 3) => Some 1
  | (mk_trans 3, mk_place 4) => Some 1
  | (mk_trans 4, mk_place 5) => Some 1
  | (mk_trans 5, mk_place 6) => Some 1
  | _ => None
  end.

(* 1 arc of type "test" *)
Definition ex2_pre_test_function (t : trans_type) (p : place_type) :=
  match (t, p) with
  | (mk_trans 1, mk_place 1) => Some 1
    (* place 1 needs (at least) 1 token, 
       which won't be taken by transition 1 *)
  | _ => None
  end.

(* 1 arc of type "inhibitor"  *)
Definition ex2_pre_inhi_function (t : trans_type) (p : place_type) :=
  match (t, p) with
  | (mk_trans 0, mk_place 1) => Some 1
  (* place 1 needs less than 1 token, 
     which won't be taken by transition 1 *)
  | _ => None
  end.

(* 7 arcs TP      "normal outcoming"  *)
Definition ex2_post_function (t : trans_type) (p : place_type) :=
  match (t, p) with
  | (mk_trans 0, mk_place 1) => Some 1
  | (mk_trans 0, mk_place 2) => Some 2
  | (mk_trans 0, mk_place 3) => Some 1
  | (mk_trans 1, mk_place 4) => Some 1
  | (mk_trans 2, mk_place 6) => Some 1
  | (mk_trans 3, mk_place 5) => Some 1
  | (mk_trans 4, mk_place 6) => Some 1
  | (mk_trans 5, mk_place 1) => Some 1
  | _ => None
  end.

(* tokens *)
Definition ex2_init_marking (p : place_type) :=
  match p with
  | mk_place 0 => 1
  | mk_place 1 => 0
  | mk_place 2 => 0
  | mk_place 3 => 0
  | mk_place 4 => 0
  | mk_place 5 => 0
  | mk_place 6 => 0
  | _ => 0
  end.


Definition ex2_conditions (t : trans_type) (c : gard_type) :=
  match (t, c) with
  | (mk_trans 1, mk_gard 1) => true
  | _ => false
  end.
  (* 1 condition/gard  :  Petri net influenced by environnement *)

Lemma preuve3le5 : 3 <= 5. Proof. omega. Qed.
Definition int1_35 := mk_inter
                        3
                        5
                        preuve3le5.
Print le.
Lemma preuve2le255 : 2 <= 255. Proof. omega. Qed.
Definition int1_2oo := mk_inter
                         2
                         255
                         preuve2le255.

Definition ex2_inters (t : trans_type) (i : inter_type) :=
  match (t, i) with
  | (mk_trans 3, int1_35) => true
  | (mk_trans 6, int1_2oo) => true
  | _ => false
  end.

Definition ex2_priority (t1 t2 : trans_type) : bool :=
  (* se restreindre aux conflits structurels !!!!!!!  *)
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
  | (_,_) => false  (* False or True     who care ? *) 
  end.
  
Definition itpn1 :=  mk_ITPN
                       (mk_IPN
                          (mk_PN
                              ex2_places
                              ex2_transs
                              ex2_nodup_places
                              ex2_nodup_transs
                              
                              ex2_pre_function
                              ex2_post_function
                              ex2_pre_test_function
                              ex2_pre_inhi_function
                              
                              ex2_init_marking
                              ex2_priority
                          )
                          ex2_conditions
                       )
                       ex2_inters.
