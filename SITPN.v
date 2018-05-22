(*************************************************************)
(**** by Mathieu Lasjaunias, David Delahaye, David Andreu ****)
(*************************************************************)

Require Import Arith Omega List Bool.
Search nat.
(* Require Import Nat. *)
Search list.

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
                                care : int > 0 }.
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
Require Import Relations. Print relation. 
Search relation. Print transitive. 
Require Import RelationClasses. Print RelationClasses.
Print Asymmetric.

Inductive prior_type1 : Set :=
  mk_prior_type1 :
    forall (rel : trans_type -> trans_type -> bool),
      (forall (x : trans_type), (rel x x) = false) -> (* irreflexive *)
      (forall (x y : trans_type), (rel x y) = true -> (* asymmetric *)
                                  (rel y x = false)) ->
      (forall (x y z : trans_type), (rel x y) = true -> (* transitive *)
                                    (rel y z) = true ->
                                    (rel x z) = true) ->
      prior_type1.

(* transitive + asymmetric -> irreflexive ? 
   no cycle *)

Search list.
Print Equivalence. 

Inductive prior_type2 : Set :=
  mk_prior_type2
    { list_lists : list (list trans_type) ; }.
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

Print prior_type2.

Definition prio_over1
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

(*** fonctions auxiliaires pour prio_over2 ...   ***)
Definition prio_over2
           (t1 t2 : trans_type)
           (prior : prior_type2)
  : bool :=
  match prior with
  | mk_prior_type2
      L
     (* no_inter
       cover *) => false
                     (* t1 devant t2 dans 1 même sous-liste 
                       Fixpoint ...  *)
  end.

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
                             nicer to print ... *)
                           
                           priority : prior_type2 ;
                           (* Is 2 better than 1 ? *) }.

(****************************************************)
(********* intervals of time...   for S(I)TPN   *******) 

Structure time_interval_type : Set :=
  mk_inter
    {
      mini : nat ;  (* nat_star ?    <= ... *)
      maxi : nat ;
      min_le_max : mini <= maxi  ;
      cpt  : nat ;   (* nat_star ? *)
      (* yes  : mini <= cpt <= maxi ; *)
    }.
 
Structure STPN : Set := mk_STPN
                           {
                             spn : SPN ;
                             intervals : trans_type ->
                                         option time_interval_type ;}.
(* there is an interval iff there is a local clock *)
(*** but if conditions are meant to evolve through time .... *)

(* conditions  on transitions...   for  SIPN  (interpreted) *)
Inductive cond_type : Set :=
| mk_cond : nat -> cond_type.

(*  inutile
Definition caract_funct_gards := trans_type -> cond_type -> bool.

Notation "cond [ trans ]" := (caract_funct_gards
                                trans
                                cond)  
                               (at level 50) : type_scope. *)

Structure SITPN : Set := mk_SITPN
                          {
                            stpn : STPN ;
                            conds : trans_type -> list cond_type
                            (** good to have list of conditions ??
possibly an empty list **) ;}.

(*** scenario  scenari  ....  evolving through time  ???? *)
(***   --->  central  clock ?  ***) 

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
(************ Semantics of these Petri nets  **************)

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
(***** useless... because one has to decompose step by step. ***)

(**********   for debugging ***********************)
(*** list the tokens !!!! ***)
Fixpoint function2list
         (places:list place_type)
         (m:marking_type)
  : list (place_type * nat) :=
  match places with
  | nil => nil
  | p :: tail => (p, m p) :: function2list tail m
  end.
(******************************************************)



(****************************************************************)
(*** checking if there are enough tokens in predecessor places **)

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
(** but useless fonction because 
 firing a bunch of transitions synchronously implies
   checking arcs with different markings ... 
 --->    useful only for _asynchronous_ Petri nets **)


(*****************************************************************)
(*********      firing algorithm for SPN      ********************)

Import ListNotations.
Check update_marking_pre.
(** given an ordered class of transitions 
in structural conflict (a list class_of_transs), 
return list of transitions "subclass_half_fired" 
and marking "m_intermediate" *)
Fixpoint sub_fire_aux_pre
         (places : list place_type) (pre test inhib : weight_type)
         (m_init m_intermediate : marking_type)
         (class_transs subclass_half_fired : list trans_type)
         (* "subclass_half_fired"  is empty at first *) 
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
                 then sub_fire_aux_pre
                        places pre test inhib
                        m_init (update_marking_pre
                                  places t pre m_intermediate)
                        tail (subclass_half_fired ++ [t])
                        (* concatener derriere pour garder ordre *)
                 else sub_fire_aux_pre
                        places pre test inhib
                        m_init m_intermediate
                        tail subclass_half_fired
  | []  => (subclass_half_fired, m_intermediate)
  end.
(* could have done 2 functions but ... 
these are 2 parallel calculus : pumping tokens 
to get "m_intermediate"  (half fired)
and returning subclass of transitions (half fired)
and one has to keep both marking to check correctly ... **)

(** given a marking "m_intermediate"  
(got after a subclass of transs has been half fired) 
and the list of transitions "subclass_half_fired", 
 return the marking where post arcs have been fired too **)
Fixpoint sub_fire_aux_post
         (places : list place_type) (post : weight_type)
         (m_intermediate : marking_type)
         (subclass_half_fired : list trans_type)  
  : marking_type := 
  match subclass_half_fired with
  | []  => m_intermediate
  | t :: tail  => sub_fire_aux_post
                    places post
                    (update_marking_post
                       places t post m_intermediate)
                    tail
  end.

(** apply sub_fire_aux_pre over all subclasses of transitions 
 begin with initial marking, end with half fired marking  **)
(*  "classes_half_fired" is empty at first ... *)
Fixpoint fire_aux_pre
         (places : list place_type) (pre test inhib : weight_type)
         (marking : marking_type)
         (classes_transs classes_half_fired : list (list trans_type))
  : (list (list trans_type))   * marking_type :=
  match classes_transs with
  | [] => (classes_half_fired , marking)
  | l :: Ltail => let m := (snd (sub_fire_aux_pre
                                  places  pre test inhib
                                  marking marking
                                  l []))
                  in
                  fire_aux_pre
                    places  pre test inhib
                    m
                    Ltail
                    ((fst (sub_fire_aux_pre
                             places  pre test inhib
                             marking marking
                             l [])) :: classes_half_fired)
                                    
               (*   ((fst (sub_fire_aux_pre
                          places  pre test inhib
                          marking marking
                          l [])) ::
                                 (fst (fire_aux_pre
                                         places
                                         pre test inhib 
                                         m
                                         Ltail classes_half_fired)),
                   m) *)
  end.

Print SPN.
Definition fire_aux_pre_listing (spn : SPN)
  : (list (list trans_type)) * list (place_type * nat) :=
  let res := (fire_aux_pre
                (places spn)
                (pre spn)
                (test spn)
                (inhib spn)
                (marking spn)
                match (priority spn) with
                | mk_prior_type2
                    Lol => Lol
                end
                [])
  in
  (fst res, function2list
              (places spn)
              (snd (res))
  ).
                      

(*** begin with intermediate marking
(after half firing ALL the (pre arcs) transitions choosen),
 end with the _final_ marking  ****)
Fixpoint fire_aux_post
         (places : list place_type) (post : weight_type)
         (marking_half : marking_type)
         (L_fired : list (list trans_type))
  : marking_type := 
  match L_fired with
  | []  => marking_half
  | l :: Ltail  => fire_aux_post
                     places post
                     (sub_fire_aux_post
                        places post
                        marking_half
                        l)
                     Ltail                     
  end. 

Print SPN. Print prior_type2.
Definition fire
           (places : list place_type)
           (pre test inhib post : weight_type)
           (m_init : marking_type)
           (classes_transs : list (list trans_type))
  : marking_type :=
  fire_aux_post
    places post
    m_init
    (fst (fire_aux_pre
            places  pre test inhib 
            m_init
            classes_transs [] )).

(*******************************************************************)
(************* to animate a SPN (only the marking evolves)  ********)

Print SPN. Print prior_type2.
Definition fire_spn (spn : SPN) :=
  mk_SPN
    (places spn)
    (transs spn)
    (nodup_places spn)
    (nodup_transitions spn)
    (pre spn)
    (post spn)
    (test spn)
    (inhib spn)
    (* marking *)
    (fire
       (places spn)
       (pre spn)
       (test spn)
       (inhib spn)
       (post spn)
       (marking spn)
       match (priority spn) with
       | mk_prior_type2
           (* partition *)
           Lol => Lol
       end
    )
    (priority spn).

Fixpoint animate_spn
         (spn : SPN)
         (n : nat)
  : list marking_type := 
  match n with
  | O => [ marking spn ]
  | S n' => (marking spn 
                     ::
                     (animate_spn (fire_spn spn) n'))
  end.

(******************** to print and test with the eye ************)
Print marking_type.
Search list.


Definition fire_spn_listing (spn : SPN) :=
  function2list
    (places spn)
    (marking (fire_spn spn)).


Fixpoint animate_pn_list (spn:SPN) (n:nat) :
  list (list (place_type * nat)) := 
  (* on fait n pas de calcul  
    et on retourne le chemin des marquages *)
  match n with  
  | O => [ function2list (places spn) (marking spn) ]
  | S n' => (function2list (places spn) (marking spn))
              :: (animate_pn_list (fire_spn spn) n')
  end.  


(******************************************************************)
(******************************************************************)
(**** small example of Petri net (page 24 in Ibrahim thesis) ******)
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
  | mk_place 1 => 1
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

Print prior_type2.
Definition ex_prior2_aux :=
  [
    [mk_trans 1 ; mk_trans 12] ;
    [mk_trans 0 ; mk_trans 2 ; mk_trans 5] ;
    [mk_trans 3 ; mk_trans 8 ; mk_trans 16] ;
    [mk_trans 4 ; mk_trans 9 ; mk_trans 13 ; mk_trans 14] ;
    [mk_trans 6]
  ].
  
Definition ex_prior2 :=
  mk_prior_type2 ex_prior2_aux.    
    
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
                      ex_prior2.

Check ex_spn. Compute (marking ex_spn). (* initial marking *)

Search SPN.
Compute (animate_pn_list
           ex_spn
           10).  (* 11 markings *)

(********   debuggage   ******)

Compute (fire_spn_listing
           ex_spn).
Compute (fire_aux_pre_listing ex_spn). (* cool ! *)

Print ex_prior2_aux. Print ex_places.
Search marking_type.

Print fire_aux_pre. Print sub_fire_aux_pre. Print fire.

Compute (sub_fire_aux_pre 
           (places ex_spn)
           (pre ex_spn) (test ex_spn) (inhib ex_spn)
           (marking ex_spn) (marking ex_spn)
           [mk_trans 1; mk_trans 12]
           []).

Compute (fire_aux_pre
           (places ex_spn)
           (pre ex_spn) (test ex_spn) (inhib ex_spn)
           (marking ex_spn)
           (ex_prior2_aux)
           []). 



Compute (pn_is_enabled_because_look
           (fire_pn
              ex_pn)).
Compute (pn_is_enabled_because_look
           (fire_pn
              (fire_pn
                 ex_pn))).   (* ... *)


Compute (highest_transition
           ex_priority
           (pn_is_enabled_because_look
              ex_pn)).
Compute (highest_transition
           ex_priority
           (pn_is_enabled_because_look
              (fire_pn
                 ex_pn))).   (*  t_2 est prio sur t_0   *) 

Compute (fire_trans
           ex_pn
           (highest_transition
              ex_priority
              (pn_is_enabled_because_look
                 ex_pn))). 

(**********************************************************)
(* should I also print the list of transitions 
   labelling this path of markings ?

should I print the list of all enabled transitions at each step ?

(**** transitions can be _partitioned_ :
structural conflicts are _classes_ of transitions 
  if an order is given ,  great  ***)  *)


(**********************************************************)

Print SPN. Print prior_type2.

(*** interpreted Petri net ***)
Definition ex_conditions (t : trans_type) (c : gard_type)
  : bool
  := match (t, c) with
  | (mk_trans 0, mk_gard 0) => true
  | (mk_trans 2, mk_gard 1) => true
  | _ => false
  end.

Definition ipn_ex := mk_IPN
                       ex_pn
                       ex_conditions.











(*
(******************************************************************)
(*************** ANCIEN CACA **************************************)
              
(* fire transition t, only updating the marking of the Petri net ! *)
Definition fire_one_trans
           (sitpn : SITPN)
           (t:trans_type)
  : SITPN  :=
  mk_SITPN
    (mk_SIPN
       (mk_SPN
          (places (spn (sipn sitpn)))
          (transs (spn (sipn sitpn)))
          (nodup_places (spn (sipn sitpn)))
          (nodup_transitions (spn (sipn sitpn)))
          (pre (spn (sipn sitpn)))
          (post (spn (sipn sitpn)))
          (pre_test (spn (sipn sitpn)))
          (pre_inhi (spn (sipn sitpn)))
          (update_marking 
             (places (spn (sipn sitpn)))
             t
             (pre (spn (sipn sitpn))) (post (spn (sipn sitpn)))
             (marking (spn (sipn sitpn))))
          (priority (spn (sipn sitpn)))
       )
       (conds (sipn sitpn))
    )
    (intervals sitpn).

Fixpoint fire_many_transs
           (sitpn : SITPN)
           (to_fire : list trans_type)
  : SITPN :=
  match to_fire with
  | nil => sitpn
  | t :: tail  => fire_many_transs
                    (fire_one_trans
                       sitpn
                       t)
                    tail
  end.


                      
(* for a given marking, return the list of "enabled transitions" *)
Fixpoint enabled_transs_aux
         (spn : SPN)
         (l : list trans_type) {struct l}
         (* structural induction over list of transitions *) :
  list trans_type :=
  match l with
  | nil => nil
  | cons t tail => if (trans_is_enabled
                         (places    spn)
                         (pre       spn)
                         (pre_test  spn)
                         (pre_inhi  spn)  
                         (marking   spn)
                         t)
                   then cons t (enabled_transs_aux
                                  spn
                                  tail)
                   else enabled_transs_aux
                          spn
                          tail
  end.
(*** for a Petri net, return the list of enabled transitions ***)
Definition enabled_transs (spn : SPN)
  : list trans_type :=
  enabled_transs_aux
    spn
    (transs spn).
*)

(***************************************************************)
(**************** "firable" is stronger than "enabled" *********)
(********************** conditions & intervals *****************)


Definition eval_cond (c : cond_type) : bool := true.

Fixpoint conds_firable_trans_aux
           (t : trans_type)
           (con : list cond_type)
  : bool :=
  match con with
  | []  => true
  | c :: tail => (eval_cond c)
                   && (conds_firable_trans_aux
                         t
                         tail)
  end.

Definition conds_firable_trans
           (t : trans_type)
           (conds : trans_type -> list cond_type)
  : bool :=
  conds_firable_trans_aux
    t 
    (conds t). 

Print SITPN. Print time_interval_type. Print nat_star.
Definition inter_firable_trans
           (t : trans_type)
           (intervals : trans_type -> option time_interval_type)
  : bool :=
  match (intervals t) with
  | None  => true
  | Some inter => match inter with
                  | mk_inter
                      mini
                      maxi
                      min_le_max
                      cpt => (*match (mini, maxi) with
                             | (mk_nat_star
                                  inta
                                  carea,
                                mk_nat_star
                                  intb
                                  careb) =>*) if (mini <=? cpt)
                                                   &&
                                                   (cpt <=? maxi)
                                              then true
                                              else false
                  end
                                
  end.

Definition firable_trans
           (t : trans_type)
           (conds : trans_type -> list cond_type)
           (intervals : trans_type -> option time_interval_type)
            : bool :=
  (conds_firable_trans
     t
     conds)
    &&
    (inter_firable_trans
       t
       intervals).




(*****************************************************)
(******** getting the classes of transitions *********)
(*************** sections sorting ********************)

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
 il suffit de tirer les premières de listes (updating le marking)
en retirant les transitions suivantes qui ne sont plus tirables
 
et en recommançant avec la liste de listes restante
qui n'est pas forcement plus courte (zut !) *)

  
End effective_conflicts.







(******************************************************************)
(******* David Andreu's big example (redrawn in my Oxford) ********)

(* 7 places *)
Definition ex2_places : (list place_type) :=
  [ mk_place 1 ;
    mk_place 2 ;
    mk_place 3 ;
    mk_place 4 ;
    mk_place 5 ;
    mk_place 6 ;
    mk_place 7 ].
Definition ex2_nodup_places : NoDup ex2_places :=
  NoDup_nodup
    places_eq_dec
    ex2_places. 

(* 6 transitions *)
Definition ex2_transs : (list trans_type) :=
  [ mk_trans 0 ;
    mk_trans 1 ;
    mk_trans 2 ;
    mk_trans 3 ;
    mk_trans 4 ;
    mk_trans 5 ;
    mk_trans 6 ].
Definition ex2_nodup_transs : NoDup ex2_transs :=
  NoDup_nodup
    transs_eq_dec
    ex2_transs. 

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