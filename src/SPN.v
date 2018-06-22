(***********************)
(**** by ML, DD, DA ****)
(***********************)

Require Export Arith Omega List Bool FunInd.
Export ListNotations.
Search nat. Search list.

(***********************************************************
****   syntax of (generalized, extended) Petri nets   ******
************************************************************)

Inductive place_type : Set :=
| mk_place : nat -> place_type.

Inductive trans_type : Set :=
| mk_trans : nat -> trans_type.

(*   4 "TYPES" of arcs : pred, post, pred_inhib, pred_test 
    along with "some" weight   (default is 1 usually).       *)

Structure nat_star : Set := mk_nat_star
                              { int : nat ;
                                posi : int > 0 }.
(* a given arc has some weight > 0 *)
Definition weight_type := trans_type -> place_type -> option nat_star.

(*  Why not this inductive definition as well ????
Inductive arc_type : Set :=
| mk_arc_pt : place_type -> transition_type -> nat -> arc_type
| mk_arc_tp : transition_type -> place_type -> nat -> arc_type
(* extended (generalized = nat) Petri nets *)
| mk_arc_inhi : place_type -> transition_type -> nat -> arc_type
| mk_arc_test : place_type -> transition_type -> nat -> arc_type.
 *)

Definition marking_type := place_type -> nat.

(*****************************************************************)
(***  priority relation  .................
  to DETERMINE the Petri net (along with the imperative semantic) 
***)

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

(* Inductive or Definition  ?? *) 
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

(*** fonction en construction ...  peut-etre utile ...  
Definition prio_over
           (t1 t2 : trans_type)
           (prior : prior_type)
  : option bool :=
  match prior with
  | mk_prior
      L
     (* no_inter
       cover *) => (* t1 devant t2 dans 1 meme sous-liste 
                       Fixpoint ...  *)  Some false
  end.   *)

(****************************************************************)
Print NoDup. Print nodup. Print NoDup_nodup. (* opaque proof ? *)
Print find_some.  (* maybe useful *)
(* split  / combine   ... *)

Structure SPN : Set := mk_SPN
                         {
                           places : list place_type ;
                           transs : list trans_type ;
                                                      
                           pre : weight_type ;
                           post : weight_type ;
                           
                           test : weight_type ;
                           inhib : weight_type ;
                           
                           marking : marking_type ;
                           
                           priority : prior_type ;
                         }.

(* on suppose que 
1) les places sont toutes differentes  (NoDup ...)
2) les transs sont toutes differentes  (NoDup ...)

3) priority/prior_type  
forme une partition des transitions, partition correspondante
aux classes de "conflits structurels" (arcs amonts en commum)
*) 

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
Defined.  (* the proof is important when "Defined." *)
(* Global Opaque option_eq.     ???   ***)


(**********************************************************
***********************************************************
***********   Semantics of these SPN   ********************
***********************************************************)

(********** given a marking m, set j tokens in place p **********)
Print marking_type. Print place_type.
Definition set_mark (m:marking_type) (p:place_type) (j:nat)
  : marking_type :=
  fun p' =>  if beq_places p p'
             then j             (* set j tokens in place p *)
             else m p'.         (* other tokens left unchanged  *)
(* function not used yet *)

Inductive modif_mark_spec
          (m : marking_type)
          (p  p' : place_type)
          (j : option nat_star)
          (op : nat -> nat -> nat)
  : nat -> Prop :=
| modif_mark_p_eq_p'_none :
    (beq_places p p') = true -> j = None ->
    modif_mark_spec m p p' j op (m p)
| modif_mark_p_eq_p'_some :
    forall (i : nat_star) (n : nat) (pf : n > 0),
      (beq_places p p') = true -> j = (Some i) ->
      i = (mk_nat_star n pf) ->
      modif_mark_spec m p p' j op (op (m p) n)
| modif_mark_p_neq_p' :
    (beq_places p p') = false ->
      modif_mark_spec m p p' j op (m p').
(* given a marking m, add/remove j tokens inside place p *)  
Definition modif_mark
           (m : marking_type)
           (p : place_type)
           (j : option nat_star)
           (** option nat_star     because of weight_type ? **)
           (op : nat -> nat -> nat)
           (p' : place_type) : nat :=
    if beq_places p p'
    then match j with
          | None => m p              (* no change *)
          | Some i => match i with
                      | mk_nat_star
                          inti
                          _ => op (m p) inti
                                      (* j=i tokens added/removed *)
                      end
         end
    else m p'.         (* other places left unchanged  *)

Functional Scheme modif_mark_ind :=
  Induction for modif_mark Sort Prop.
Theorem modif_mark_sound :
  forall (m : marking_type) (p : place_type) (j : option nat_star)
         (op : nat -> nat -> nat) (p' : place_type) (mp : nat),
    modif_mark m p j op p' = mp -> modif_mark_spec m p p' j op mp.
Proof.
  do 6 intro.
  functional induction (modif_mark m p j op p') using modif_mark_ind.
  Focus 3.  
  intro. rewrite <- H. apply modif_mark_p_neq_p'. assumption.
  Focus 2.
  intro. rewrite <- H. apply modif_mark_p_eq_p'_none.
  assumption. reflexivity.
  intro. rewrite <- H.
  apply modif_mark_p_eq_p'_some with
      (i:={| int := inti; posi := _x |}) (pf:=_x) ; try reflexivity. assumption.
Qed.
Theorem modif_mark_complete :
  forall (m : marking_type) (p : place_type) (j : option nat_star)
         (op : nat -> nat -> nat) (p' : place_type) (mp : nat),
    modif_mark_spec m p p' j op mp -> modif_mark m p j op p' = mp. 
Proof.
  intros. elim H.
  - intros. simpl.
Admitted.

Check Nat.sub. Check Nat.add.   (** the 2 op(erators) to use ... **)
(* Require Import Nat. (* for Nat.leb != (Bool.)leb *)  *)

(*************   update marking   *********************)
Inductive update_marking_pre_spec
          (t : trans_type)
          (pre : weight_type)
          (m : marking_type)
  : list place_type ->
    marking_type ->
    Prop :=
| update_marking_pre_nil :
    update_marking_pre_spec
      t pre m [] m 
| update_marking_pre_cons :
    forall (p p' : place_type)
           (tail : list place_type)
           (n : nat),
      update_marking_pre_spec
        t pre
        m tail (modif_mark
                  m p (pre t p) Nat.sub).
Fixpoint update_marking_pre
         (places : list place_type)
         (t : trans_type)
         (pre : weight_type)
         (m : marking_type)
  : marking_type :=
  match places with
  | [] => m
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

Functional Scheme update_marking_pre_ind :=
  Induction for update_marking_pre Sort Prop.

Theorem update_marking_pre_sound :
  forall (places : list place_type)
         (t : trans_type)
         (pre : weight_type)
         (m m' : marking_type),
    update_marking_pre places t pre m = m' ->
    update_marking_pre_spec t pre m places m'.
Proof.
  intros places t pre m m'.
  functional induction (update_marking_pre places t pre m)
             using update_marking_pre_ind.
  - intro. rewrite <- H. apply update_marking_pre_nil.
  - intro. rewrite <- H. try apply update_marking_pre_cons.
Admitted.
Theorem update_marking_pre_complete :
  forall (places : list place_type)
         (t : trans_type)
         (pre : weight_type)
         (m m' : marking_type),
    update_marking_pre_spec t pre m places m' ->
    update_marking_pre places t pre m = m'.
Proof.
  intros places t pre m m' H. elim H.
  - 
    
Admitted.

(************************************************************)
(**** downhill (output set, postset) ***)
Inductive update_marking_post_spec
          (t : trans_type)
          (post : weight_type)
          (m : marking_type)
  : list place_type ->
    marking_type ->
    Prop :=
| update_marking_post_nil :
    update_marking_post_spec
      t post m [] m 
| update_marking_post_cons :
    forall (p p' : place_type)
           (tail : list place_type)
           (n : nat),
      update_marking_post_spec
        t post
        m tail (modif_mark
                  m p (post t p) Nat.add).
Fixpoint update_marking_post
         (places : list place_type) 
         (t : trans_type)
         (post : weight_type)
         (m : marking_type)         
  (* structural induction over list of places *)
  : marking_type :=
  match places with
  | [] => m
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

Functional Scheme update_marking_post_ind :=
  Induction for update_marking_post Sort Prop.
Theorem update_marking_post_sound :
  forall (places : list place_type)
         (t : trans_type)
         (post : weight_type)
         (m m' : marking_type),
    update_marking_post places t post m = m' ->
    update_marking_post_spec t post m places m'.
Proof.
  intros places t post m m'.
  functional induction (update_marking_post places t post m)
             using update_marking_post_ind.
  - intro. rewrite <- H. apply update_marking_post_nil.
  - intro. rewrite <- H. try apply update_marking_post_cons.
Admitted.
Theorem update_marking_post_complete :
  forall (places : list place_type)
         (t : trans_type)
         (post : weight_type)
         (m m' : marking_type),
    update_marking_post_spec t post m places m' ->
    update_marking_post places t post m = m'.
Proof.
  intros places t post m m' H. elim H.
  - 
Admitted.

(**********************************************************)
(***** below a useless function !!!!
    because one has to decompose step by step 
 and fire several transitions in 1 step  ***)
Check update_marking_pre.
Inductive update_marking_spec
          (places : list place_type)
          (t : trans_type)
          (pre post : weight_type)
          (m : marking_type)
  : marking_type ->
    Prop :=
| update_marking_cst :
    update_marking_spec
      places t pre post m
      (update_marking_post
         places t post (update_marking_pre
                          places t pre m)). 
Definition update_marking
           (places : list place_type) 
           (t : trans_type)
           (pre post : weight_type)
           (m : marking_type)         
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

Functional Scheme update_marking_ind :=
  Induction for update_marking Sort Prop.
Theorem update_marking_sound :
  forall (places : list place_type)
         (t : trans_type)
         (pre post : weight_type)
         (m m' : marking_type),
    update_marking
      places t pre post m = m' ->
    update_marking_spec
      places t pre post m m'.
Proof.
Admitted.
Theorem update_marking_complete :
forall (places : list place_type)
         (t : trans_type)
         (pre post : weight_type)
         (m m' : marking_type),
    update_marking_spec
      places t pre post m m' ->
    update_marking
      places t pre post m = m'.
Proof.
Admitted.

(**********   to print the markings  ***********************)
(*** list the tokens !!!! ***)
Print update_marking_post_spec.
Inductive marking2list_spec
          (m : marking_type)
  : list place_type ->
    list (place_type * nat) ->
    Prop :=
| marking2list_nil : marking2list_spec
                 m [] []
| marking2list_cons : forall (p:place_type) (tail:list place_type)
                       (listc : list (place_type * nat))
                       (c : (place_type * nat)),
    c = (p, m p) ->
    marking2list_spec
      m (p::tail) (c::listc).          
Fixpoint marking2list
         (places : list place_type)
         (m : marking_type)
  : list (place_type * nat) :=
  match places with
  | nil => nil
  | p :: tail => (p, m p) :: (marking2list
                                tail m)
  end.

Functional Scheme marking2list_ind :=
  Induction for marking2list Sort Prop.
Theorem marking2list_sound :
  forall (places : list place_type)
         (m : marking_type)
         (truc : list (place_type * nat)),
    marking2list
      places m = truc  ->
    marking2list_spec
      m places truc.
Proof.
  intros places m truc.
  functional induction (marking2list places m)
             using marking2list_ind.
  - intro. rewrite <- H. apply marking2list_nil.
  - intro. rewrite <- H. apply marking2list_cons. reflexivity.
Qed.
Theorem marking2list_complete :
  forall (places : list place_type)
         (m : marking_type)
         (truc : list (place_type * nat)),
    marking2list_spec
      m places truc  ->
    marking2list
      places m = truc.
Proof.
  intros places m truc H. elim H.
  -
    
Admitted.


(****************************************************************)
(*** CHECKING IF there are enough tokens in predecessor places **)

Locate "<?". Print Nat.ltb. Print Nat.leb.
Print pre. Print weight_type. Print modif_mark_spec.
(**** uphill (input set, preset) ***)
Inductive pre_or_test_check_spec
          (pre_or_test_arcs_t : place_type -> option nat_star)
          (m : marking_type)
  : list place_type -> Prop :=
| pre_or_test_check_nil : pre_or_test_check_spec
                            pre_or_test_arcs_t
                            m []
| pre_or_test_check_cons_some : forall (p:place_type)
                                       (tail:list place_type)
                                       (pos:nat_star)
                                       (n:nat) (pf:n>0),
    pre_or_test_arcs_t p = Some pos ->
    pos = {| int := n; posi := pf |} ->
    pre_or_test_check_spec
      pre_or_test_arcs_t
      m (p::tail)
| pre_or_test_check_cons_none : forall (p:place_type)
                                       (tail:list place_type),
    pre_or_test_arcs_t p = None ->
    pre_or_test_check_spec
      pre_or_test_arcs_t
      m (p::tail).      
Fixpoint pre_or_test_check
         (places : list place_type)
         (pre_or_test_arcs_t : place_type -> option nat_star)
         (m : marking_type)
  : bool :=
  match places with
  | nil => true
  | cons h tail => match pre_or_test_arcs_t h with
                   | None => pre_or_test_check
                               tail
                               pre_or_test_arcs_t
                               m
                   | Some n => match n with
                               | mk_nat_star
                                   int 
                                   careful =>
                                 (int <=? (m h))
                                   &&
                                   (pre_or_test_check
                                      tail
                                      pre_or_test_arcs_t
                                      m)
                               end
                   end
  end.

Functional Scheme pre_or_test_check_ind :=
  Induction for pre_or_test_check Sort Prop.
Theorem pre_or_test_check_sound :
  forall (places : list place_type)
         (pre_or_test_arcs_t : place_type -> option nat_star)
         (m : marking_type),
    pre_or_test_check
      places
      pre_or_test_arcs_t
      (** "pre" or "test" arcs going to trans t **)
      m = true 
    ->
    pre_or_test_check_spec
      pre_or_test_arcs_t
      m
      places.
Proof.
  intros places pre_or_test_arcs_t m.
  functional induction (pre_or_test_check
                          places   pre_or_test_arcs_t   m)
             using pre_or_test_check_ind.
  - intro. apply pre_or_test_check_nil.
  - intro. (* apply marking2list_cons. reflexivity. *)

Admitted.
Theorem pre_or_test_check_complete :
  forall (places : list place_type)
         (pre_or_test_arcs_t : place_type -> option nat_star)
         (* pre or test arcs going to trans t *)
         (m : marking_type),
    pre_or_test_check_spec
      pre_or_test_arcs_t
      m
      places
    ->
    pre_or_test_check
      places
      pre_or_test_arcs_t
      (** "pre" or "test" arcs going to trans t **)
      m = true.
Proof.
  intros places  pre_or_test_arcs_t  m  H. elim H.
  - 

Admitted.

(**************************************************)
Print pre_or_test_check_spec.
Inductive inhib_check_spec
          (inhib_arcs_t : place_type -> option nat_star)
          (m : marking_type)
  : list place_type -> Prop :=
| inhib_check_nil : inhib_check_spec
                      inhib_arcs_t    m    []
| inhib_check_cons_none : forall (p:place_type)
                                 (tail:list place_type),
    inhib_check_spec
      inhib_arcs_t    m    tail
    ->
    inhib_arcs_t p = None
    ->
    inhib_check_spec
      inhib_arcs_t    m   (p::tail)
| inhib_check_cons_some : forall (p:place_type)
                                 (tail:list place_type)
                                 (pos:nat_star)
                                 (n:nat) (pf:n>0),
    inhib_check_spec
      inhib_arcs_t    m   tail
    -> 
    inhib_arcs_t p = Some pos
    ->
    pos = {| int := n; posi := pf |}
    ->
    (m p < n)
    ->
    inhib_check_spec
      inhib_arcs_t    m   (p::tail)
.
Fixpoint inhib_check
         (places : list place_type)
         (inhib_arcs_t : place_type -> option nat_star)
         (m : marking_type)
  : bool :=
  match places with
  | nil => true
  | cons h tail => match inhib_arcs_t h with
                   | None => inhib_check
                               tail
                               inhib_arcs_t
                               m
                   | Some n => match n with
                               | mk_nat_star
                                   int 
                                   careful =>
                                 ((m h) <? int)
                                   &&
                                   (inhib_check
                                      tail
                                      inhib_arcs_t
                                      m)
                               end
                   end
  end.

Functional Scheme inhib_check_ind :=
  Induction for inhib_check Sort Prop.
Theorem inhib_check_sound :
  forall (places : list place_type)
         (inhib_arcs_t : place_type -> option nat_star)
         (m : marking_type),
    inhib_check
      places    inhib_arcs_t      m
    = true 
    ->
    inhib_check_spec
      inhib_arcs_t      m      places.
Proof.
  intros places   inhib_arcs_t   m.
  functional induction (inhib_check
                          places   inhib_arcs_t   m)
             using inhib_check_ind.
  - intro. apply inhib_check_nil.
  - intro. apply inhib_check_cons_some with
               (pos := {| int := int0; posi := _x |})
               (n := int0) (pf := _x).
    + Admitted. (* apply  (IHb (right H)).
    + assumption.
    + reflexivity. *)
    
Theorem inhib_check_complete :
  forall (places : list place_type)
         (inhib_arcs_t : place_type -> option nat_star)
         (m : marking_type),
    inhib_check_spec
      inhib_arcs_t    m    places
    ->
    inhib_check
      places      inhib_arcs_t      m = true.
Proof.
  intros places  inhib_arcs_t  m  H.
  elim H.
  - (* nil *) simpl. reflexivity.
  - (* Some *) intros. simpl. rewrite H2. assumption.
Admitted.

(*****************************************************)
Print pre_or_test_check.
Inductive synchro_check_arcs_spec
          (places : list place_type)
          (pre_arcs_t : place_type -> option nat_star)
          (test_arcs_t : place_type -> option nat_star)
          (inhib_arcs_t : place_type -> option nat_star)
          (m_decreasing   m_steady : marking_type)
  :  Prop :=
| synchro_check_arcs_cst : 
    (pre_or_test_check
       places
       pre_arcs_t
       m_decreasing) = true  ->
    (pre_or_test_check
       places
       test_arcs_t
       m_steady) = true  ->
    (inhib_check
       places
       inhib_arcs_t
       m_steady) = true  ->
    synchro_check_arcs_spec
      places
      pre_arcs_t
      test_arcs_t
      inhib_arcs_t
      m_decreasing   m_steady
.  
Fixpoint synchro_check_arcs
         (places : list place_type)
         (pre_arcs_t : place_type -> option nat_star)
         (test_arcs_t : place_type -> option nat_star)
         (inhib_arcs_t : place_type -> option nat_star)
         (m_decreasing   m_steady : marking_type)
  : bool :=
  if (pre_or_test_check
        places
        pre_arcs_t
        m_decreasing)
       &&
       (pre_or_test_check
          places
          test_arcs_t
          m_steady)
       &&
       (inhib_check
          places
          inhib_arcs_t
          m_steady)
  then true
  else false.

Functional Scheme synchro_check_arcs_ind :=
  Induction for synchro_check_arcs Sort Prop. (* warning *)
Theorem synchro_check_arcs_sound :
  forall (places : list place_type)
         (pre_arcs_t : place_type -> option nat_star)
         (test_arcs_t : place_type -> option nat_star)
         (inhib_arcs_t : place_type -> option nat_star)
         (m_decreasing   m_steady : marking_type),
    synchro_check_arcs
      places      pre_arcs_t   test_arcs_t   inhib_arcs_t
      m_decreasing   m_steady 
    = true 
    ->
    synchro_check_arcs_spec
      places      pre_arcs_t   test_arcs_t   inhib_arcs_t
      m_decreasing   m_steady.
Proof.
  intros places  pre_arcs_t   test_arcs_t   inhib_arcs_t
         m_decreasing   m_steady.
 (* functional induction (synchro_check_arcs
                          places
                          pre_arcs_t   test_arcs_t   inhib_arcs_t
                          m_decreasing   m_steady)
             using synchro_check_arcs_ind. *)
  apply synchro_check_arcs_cst.
  - intro. apply inhib_check_nil.
  - intro. (* apply inhib_check_cons_some. reflexivity. *)
    
Admitted.
Theorem synchro_check_arcs_complete :
  forall (places : list place_type)
         (pre_arcs_t : place_type -> option nat_star)
         (test_arcs_t : place_type -> option nat_star)
         (inhib_arcs_t : place_type -> option nat_star)
         (m_decreasing   m_steady : marking_type),
    synchro_check_arcs_spec
      places
      pre_arcs_t
      test_arcs_t
      inhib_arcs_t
      m_decreasing   m_steady
    ->
    synchro_check_arcs
      places
      pre_arcs_t
      test_arcs_t
      inhib_arcs_t
      m_decreasing   m_steady 
    = true.
Proof.
Admitted.

(*****************************************************************)
(*********   FIRING ALGORITHM    for SPN      ********************)

Inductive spn_sub_fire_pre_spec
          (places : list place_type)
          (pre   test   inhib : weight_type)  
          (m_decreasing    m_steady  : marking_type)
  : (list trans_type) ->
    (list trans_type) ->
    marking_type ->
    Prop :=
| class_transs_nil : forall (subclass_half_fired : list trans_type),
    spn_sub_fire_pre_spec
      places  pre  test  inhib
      m_decreasing   m_steady  
      []  subclass_half_fired  m_decreasing
| class_transs_cons_if :  forall (subclass_half_fired : list trans_type)
                                 (class_transs : list trans_type)
                                 (t : trans_type)
                                 (tail : list trans_type),
    class_transs = t::tail      ->
    synchro_check_arcs
      places
      (pre t)
      (test t)
      (inhib t)
      m_decreasing   m_steady 
    = true                      ->  
    spn_sub_fire_pre_spec
      places  pre  test  inhib
      m_decreasing   m_steady  
      class_transs  (subclass_half_fired ++ [t])
      (update_marking_pre
         places t pre m_decreasing)
| class_transs_cons_else :  forall (subclass_half_fired : list trans_type)
                                   (class_transs : list trans_type)
                                   (t : trans_type)
                                   (tail : list trans_type),
    class_transs = t::tail      ->
    synchro_check_arcs
      places
      (pre t)
      (test t)
      (inhib t)
      m_decreasing   m_steady 
    = false                      ->  
    spn_sub_fire_pre_spec
      places  pre  test  inhib
      m_decreasing   m_steady  
      class_transs  subclass_half_fired
      m_decreasing
.
(** given 1 ordered class of transitions 
in structural conflict (a list class_of_transs), 
return 1 list of transitions "subclass_half_fired" 
and marking "m_intermediate" accordingly ...   *)
Fixpoint spn_sub_fire_pre
         (places : list place_type)
         (pre test inhib : weight_type)  
         (m_decreasing    m_steady  : marking_type)   
         (class_transs subclass_half_fired : list trans_type) 
         (* "subclass_half_fired"  is meant to be empty at first *) 
  : (list trans_type) * marking_type :=
  match class_transs with
  | t :: tail => if (synchro_check_arcs
                       places
                       (pre t) (test t) (inhib t)
                       m_decreasing  m_steady)
                 then
                   let
                     (m_decreasing_again, subclass_half_fired_plus) :=
                     ((update_marking_pre
                         places t pre m_decreasing),
                      subclass_half_fired ++ [t]
                     (* concatener derriere pour garder ordre *))
                   in
                   spn_sub_fire_pre
                     places pre test inhib
                     m_steady m_decreasing_again 
                     tail subclass_half_fired_plus
                 else (* no change, but inductive progress *)
                   spn_sub_fire_pre
                     places pre test inhib
                     m_steady m_decreasing
                     tail subclass_half_fired
  | []  => (subclass_half_fired, m_decreasing)
  end.
(* 
there are 2 parallel calculus in this function : 
1) pumping tokens to get "m_intermediate_decreasing"  (half fired)
2) returning subclass of transitions (half fired)
and 2 markings are recorded : 
1) the initial one to check with inhib and test arcs
2) a floating (decreasing) intermediate marking to check classic arcs
 *)

Functional Scheme spn_sub_fire_pre_ind :=
  Induction for spn_sub_fire_pre   Sort Prop.
Check spn_sub_fire_pre_spec.
Theorem spn_sub_fire_pre_sound :
  forall (places : list place_type)
         (pre  test  inhib : weight_type)
         (m_decreasing   m_steady   m_final : marking_type)
         (class_transs  subclass_half_fired  sub_final : list trans_type),
    spn_sub_fire_pre
      places
      pre test inhib   
      m_decreasing    m_steady   
      class_transs subclass_half_fired 
    = (subclass_half_fired, m_final)
    ->
    spn_sub_fire_pre_spec
      places 
      pre test inhib   
      m_decreasing    m_steady     
      class_transs subclass_half_fired 
      m_final.
Proof.
Admitted.
Theorem spn_sub_fire_pre_complete :
  forall (places : list place_type)
         (pre  test  inhib : weight_type)
         (m_decreasing   m_steady  m_final : marking_type)
         (class_transs  subclass_half_fired  sub_final : list trans_type),
    spn_sub_fire_pre_spec
      places 
      pre test inhib   
      m_decreasing    m_steady     
      class_transs subclass_half_fired 
      m_final
    ->
    spn_sub_fire_pre
      places
      pre test inhib   
      m_decreasing    m_steady   
      class_transs subclass_half_fired 
    = (subclass_half_fired, m_final).
Proof.
Admitted.

(*********************************************************)
(*
 given a marking "m_intermediate" got by above,
after a given subclass of transs has been half fired, 
and this list of transitions "subclass_half_fired", 
 returns the marking increased by the post arcs  
*)
Inductive sub_fire_post_spec 
          (places : list place_type)
          (post : weight_type)  
          (m_increasing : marking_type)
  : list trans_type ->
    marking_type ->
    Prop :=
| subclass_half_fired_nil :
    sub_fire_post_spec
      places  post
      m_increasing
      []  m_increasing
| subclass_half_fired_cons :
    forall (subclass_half_fired : list trans_type)
           (t : trans_type)
           (tail : list trans_type)
           (m : marking_type),
      subclass_half_fired = t::tail
      ->
      sub_fire_post_spec
        places   post   (update_marking_post
                           places t post m)
        tail  m_increasing
      ->
      sub_fire_post_spec
        places   post    m_increasing
        subclass_half_fired   m_increasing
.  (* faux *)
Fixpoint sub_fire_post
         (places : list place_type)
         (post : weight_type)
         (m_increasing : marking_type)
         (subclass_half_fired : list trans_type)  
  : marking_type := 
  match subclass_half_fired with
  | []  => m_increasing
  | t :: tail  => sub_fire_post
                    places post
                    (update_marking_post
                       places t post m_increasing)
                    tail
  end.

Functional Scheme sub_fire_post_ind :=
  Induction for sub_fire_post   Sort Prop.
Check sub_fire_post_spec. Check sub_fire_post.
Theorem sub_fire_post_sound :
  forall (places : list place_type)
         (post : weight_type)
         (m_decreasing  m_final : marking_type)
         (subclass_half_fired : list trans_type),
    sub_fire_post
      places   post     m_decreasing
      subclass_half_fired   =   m_final
    ->
    sub_fire_post_spec
      places   post     m_decreasing        
      subclass_half_fired       m_final.
Proof.
Admitted.
Theorem sub_fire_post_complete :
  forall (places : list place_type)
         (post : weight_type)
         (m_decreasing   m_final : marking_type)
         (subclass_half_fired  : list trans_type),
    sub_fire_post_spec
      places   post    m_decreasing        
      subclass_half_fired      m_final
    ->
    sub_fire_post
      places   post    m_decreasing
      subclass_half_fired    = m_final.
Proof.
Admitted.

(************************************************************)
Inductive spn_fire_pre_spec
          (places : list place_type)
          (pre test inhib : weight_type)
          (m_steady m_decreasing : marking_type)
        (*  (classes_half_fired : list (list trans_type)) *)
  : list (list trans_type) ->
    list (list trans_type) -> 
    marking_type -> Prop :=
| classes_transs_nil :
    forall (classes_half_fired : list (list trans_type)),
      spn_fire_pre_spec
        places
        pre   test  inhib
        m_steady   m_decreasing
        classes_half_fired
        []  m_decreasing
| classes_transs_cons :
    forall (classes_transs  Ctail  classes_half_fired  Tail : list (list trans_type))
           (class     class_half_fired : list trans_type)
           (m : marking_type),
      classes_transs = class :: Ctail
      -> 
      classes_half_fired = class_half_fired :: Tail
      ->
      (class_half_fired, m) = (spn_sub_fire_pre
                                 places
                                 pre  test  inhib
                                 m_steady   m
                                 class_half_fired  [])
      ->
      spn_fire_pre_spec
        places   pre   test   inhib
        m_steady    m
        Tail  classes_half_fired
        m
      ->
      spn_fire_pre_spec
        places   pre   test   inhib
        m_steady   m_decreasing
        classes_half_fired    Tail
        m
.
(*
 Apply sub_fire_pre over ALL classes of transitions. 
 Begin with initial marking, 
  end with half fired marking.  
 "classes_half_fired" is empty at first 
*)
Fixpoint spn_fire_pre
         (places : list place_type)
         (pre   test  inhib : weight_type)
         (m_steady   m_decreasing : marking_type)
         (classes_transs   classes_half_fired : list (list trans_type))
  : (list (list trans_type)) *
    marking_type :=
  match classes_transs with
  | [] => (classes_half_fired , m_decreasing)
  | l :: Ltail => let (sub_l, new_m) := (spn_sub_fire_pre
                                           places
                                           pre   test   inhib
                                           m_steady   m_decreasing
                                           l [])
                  in
                  spn_fire_pre
                    places
                    pre test inhib
                    m_steady   new_m
                    Ltail
                    (sub_l :: classes_half_fired)         
  end.

Functional Scheme spn_fire_pre_ind :=
  Induction for spn_fire_pre   Sort Prop.
Theorem spn_fire_pre_sound :
  forall (places : list place_type)
         (post : weight_type)
         (m_decreasing  m_final : marking_type)
         (subclass_half_fired : list trans_type),
    sub_fire_post
      places   post     m_decreasing
      subclass_half_fired   =   m_final
    ->
    sub_fire_post_spec
      places   post     m_decreasing        
      subclass_half_fired       m_final.
Proof.
Admitted.
Theorem spn_fire_pre_complete :
  forall (places : list place_type)
         (post : weight_type)
         (m_decreasing   m_final : marking_type)
         (subclass_half_fired  : list trans_type),
    sub_fire_post_spec
      places   post    m_decreasing        
      subclass_half_fired      m_final
    ->
    sub_fire_post
      places   post    m_decreasing
      subclass_half_fired    = m_final.
Proof.
Admitted.

(******************************************************)
Inductive fire_post_spec
          (places : list place_type)
          (post : weight_type)
          (marking_increasing : marking_type)
  : list (list trans_type)  ->  marking_type -> Prop  := 
| subclasses_fired_uphill_nil : fire_post_spec
                                  places
                                  post
                                  marking_increasing
                                  []  marking_increasing
| subclasses_fired_uphill_cons : fire_post_spec
                                   places
                                   post
                                   marking_increasing
                                   []  marking_increasing
.
(*  meant to begin with 
 intermediate marking computed by "fire_pre",
 after half (pre arcs) firing of ALL the chosen transitions.
 End with the FINAL marking of the cycle !  *)
Fixpoint fire_post
         (places : list place_type)
         (post : weight_type)
         (marking_increasing : marking_type)
         (subclasses_fired_uphill : list (list trans_type))
  : marking_type := 
  match subclasses_fired_uphill with
  | []  => marking_increasing
  | l :: Ltail  => let new_m := sub_fire_post
                                  places post
                                  marking_increasing
                                  l
                   in
                   fire_post
                     places post
                     new_m
                     Ltail                     
  end. 

Functional Scheme fire_post_ind :=
  Induction for fire_post   Sort Prop.
Theorem fire_post_sound :
  forall (places : list place_type)
         (post : weight_type)
         (m_increasing  m_final : marking_type)
         (subclasses_firind : list (list trans_type)),
    fire_post
      places   post     m_increasing
      subclasses_firind   =   m_final
    ->
    fire_post_spec
      places   post     m_increasing        
      subclasses_firind       m_final.
Proof.
Admitted.
Theorem fire_post_complete :
  forall (places : list place_type)
         (post : weight_type)
         (m_increasing  m_final : marking_type)
         (subclasses_firind : list (list trans_type)),
    fire_post_spec
      places   post     m_increasing        
      subclasses_firind       m_final
    ->
    fire_post
      places   post     m_increasing
      subclasses_firind   =   m_final
.
Proof.
Admitted.

(****************************************************)
Inductive fire_spn_spec   
          (places : list place_type)
          (pre test inhib post : weight_type)
          (m_steady : marking_type)
          (classes_transs : list (list trans_type))
  : (list (list trans_type)) -> marking_type -> Prop :=
| spn_fire_constr : fire_spn_spec   
                      places
                      pre test inhib post
                      m_steady 
                      classes_transs
                      (*  calcul   *)
                      classes_transs m_steady.
(* (almost) main function, 
  returning  "transitions fired (Lol)" + "final marking" ,
   branching spn_fire_post with spn_fire_pre   *)
Definition fire_spn  
           (places : list place_type)
           (pre test inhib post : weight_type)
           (m_steady : marking_type)
           (classes_transs : list (list trans_type))
  : (list (list trans_type)) * marking_type :=
  let (sub_Lol, m_decreased) := spn_fire_pre
                                  places  pre test inhib 
                                  m_steady   m_steady
                                  classes_transs []
  in
  (sub_Lol, fire_post
              places post
              m_decreased
              sub_Lol).

Functional Scheme fire_spn_ind :=
  Induction for fire_spn   Sort Prop.
Theorem fire_spn_sound :
  forall (places : list place_type)
         (pre  test  inhib   post : weight_type)
         (m_steady   m_after : marking_type)
         (classes_transs   sub_Lol : list (list trans_type)),
    fire_spn
      places   pre  test  inhib  post
      m_steady  classes_transs   =  (sub_Lol, m_after)
    ->
    fire_spn_spec
      places   pre  test  inhib  post
      m_steady   classes_transs   sub_Lol  m_after.
Proof.
Admitted.
Theorem fire_spn_complete :
 forall (places : list place_type)
         (pre  test  inhib   post : weight_type)
         (m_steady   m_after : marking_type)
         (classes_transs   sub_Lol : list (list trans_type)),
   fire_spn_spec
     places   pre  test  inhib  post
     m_steady   classes_transs   sub_Lol  m_after
   ->
   fire_spn
     places   pre  test  inhib  post
     m_steady  classes_transs   =  (sub_Lol, m_after).
Proof.
Admitted.

(***********************************************************)
(************* to animate a SPN  (and debug)  **************)

Print SPN.  (*** for nice and easy    prints   ***)
(*** list of transitions fired +   INTERMEDIATE   marking  ***)
Definition spn_fire_pre_print
           (places : list place_type) (pre test inhib : weight_type)
           (marking : marking_type)
           (classes_transs  : list (list trans_type))
  : (list (list trans_type)) * list (place_type * nat) :=
  let (sub_Lol, m) := (spn_fire_pre
                         places 
                         pre  test  inhib 
                         marking   marking
                         classes_transs []
                      )
  in
  (sub_Lol, marking2list
              places 
              m ).    (* go with snp_debug_pre *)
Definition spn_debug_pre (spn : SPN)
           (* gives transitions fired  +  marking_pre  *)
  : (list (list trans_type)) * list (place_type * nat) :=
  match spn with
  | mk_SPN
      places
      transs
      pre  post test inhib
      m
      (mk_prior
         Lol)
    =>  spn_fire_pre_print
          places
          pre test inhib
          m
          Lol
  end.

(*********************************************************)
Print SPN. Print prior_type.
Check fire_spn_spec. (* != spn_fire_spec *)
Inductive spn_fired_spec
          (spn : SPN) :
  list (list trans_type) -> SPN -> Prop :=
| spn_fired_mk : spn_fired_spec
                   spn [] spn.
(* Only the marking is evolving ! 
but we also record the fired transitions ! *)
Definition spn_fired (spn : SPN)
  : (list (list trans_type)) * SPN :=
  match spn with
  | mk_SPN
      places  transs  
      pre  post test inhib
      m
      (mk_prior
         Lol)
    =>  let (sub_Lol, final_m) := (fire_spn
                                     places 
                                     pre  test  inhib  post
                                     m
                                     Lol)
        in (sub_Lol,
            mk_SPN
              places  transs  
              pre  post test inhib
              final_m
              (mk_prior
                 Lol))
  end.

Functional Scheme spn_fired_ind :=
  Induction for spn_fired   Sort Prop.
Theorem spn_fired_sound :
  forall (places : list place_type)
         (pre  test  inhib   post : weight_type)
         (m_steady   m_after : marking_type)
         (classes_transs   sub_Lol : list (list trans_type)),
    fire_spn
      places   pre  test  inhib  post
      m_steady  classes_transs   =  (sub_Lol, m_after)
    ->
    fire_spn_spec
      places   pre  test  inhib  post
      m_steady   classes_transs   sub_Lol  m_after.
Proof.
  intros. Admitted.
Theorem spn_fired_complete :
 forall (places : list place_type)
         (pre  test  inhib   post : weight_type)
         (m_steady   m_after : marking_type)
         (classes_transs   sub_Lol : list (list trans_type)),
   fire_spn_spec
     places   pre  test  inhib  post
     m_steady   classes_transs   sub_Lol  m_after
   ->
   fire_spn
     places   pre  test  inhib  post
     m_steady  classes_transs   =  (sub_Lol, m_after).
Proof.
  intros. Admitted.

(*******************************************************)
Check spn_fired. Check spn_fired_spec.
Inductive animate_spn_spec
          (spn : SPN)
  : nat ->
    list
      (list (list trans_type)  *
       list (place_type * nat) ) -> Prop :=
| animate_spn_O : animate_spn_spec
                    spn
                    O
                    []
| animate_spn_S :
    forall (next_spn : SPN)
           (Lol_fired : list (list trans_type))
           (m : marking_type)
           (m_visuel : list (place_type * nat))
           (n p : nat)
           (TAIL : list (list (list trans_type) * list (place_type * nat))),
      n = S p
      ->
      (Lol_fired, next_spn) = spn_fired spn
      ->
      m_visuel = marking2list
                       (places next_spn)
                       (marking next_spn)
      ->
      animate_spn_spec
        next_spn    p    TAIL
      -> 
      animate_spn_spec
        spn   n   ((Lol_fired, m_visuel) :: TAIL)   .
(* n steps calculus, n "cycles" with both markings and transs *)
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
  | S n' =>  let (Lol_fired, next_spn) :=  spn_fired spn 
             in
             ( Lol_fired ,
               (marking2list
                  (places next_spn)
                  (marking next_spn))) 
               ::
               (animate_spn
                  next_spn
                  n')
  end.    (* split / combine ... *)
           
Functional Scheme animate_spn_ind :=
  Induction for animate_spn   Sort Prop.
Theorem animate_spn_sound :
  forall (spn   : SPN)
         (n : nat)
         (truc : list (list (list trans_type)  *
                       list (place_type * nat) )),
    animate_spn
      spn    n   =  truc
    ->
    animate_spn_spec
      spn    n     truc.
Proof.
  intros. Admitted.
Theorem animate_spn_complete :
  forall (spn   : SPN)
         (n : nat)
         (truc : list (list (list trans_type)  *
                       list (place_type * nat) )),
    animate_spn_spec
      spn    n     truc
    ->
    animate_spn
      spn    n   =  truc.
Proof.
  intros. Admitted.



(*****************************************************************)
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
 il suffit de tirer les premières de listes (updating le marking)
en retirant les transitions suivantes qui ne sont plus tirables
 
et en recommançant avec la liste de listes restante
qui n'est pas forcement plus courte (zut !) *)

  
End effective_conflicts.

*)

