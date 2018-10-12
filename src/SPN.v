Require Export Arith Omega List Bool FunInd.
Export ListNotations.
Search nat. Search list.

(******************************************************************)
(* Syntax of generalized (weight on transitions > or equal to 1), *)
(* extended (test and inhibiting edges) Petri nets.               *)
(******************************************************************)

(* A place is identified by an index which is unique. *)
Inductive place_type : Set :=
| mk_place : nat -> place_type.

Notation "'pl' nat" := (mk_place nat) (at level 100, no associativity).

(* A transition is identified by an index which is unique. *)
Inductive trans_type : Set :=
| mk_trans : nat -> trans_type.

Notation "'tr' nat" := (mk_trans nat) (at level 100, no associativity).

(* There are 4 kinds of edges : pred, post, pred_inhib, pred_test 
 * along with "some" positive weight (default is 1 usually).       
 *)

(* Set of natural numbers that are strictly over zero.   *)
(* The second member, posi, must be a lemma of the form "n > 0" *)
Structure nat_star : Set := mk_nat_star { int : nat ; posi : int > 0 }.

(* A given transition, either reaching in or coming out of a place,
 * has some weight over 0 or no weight at all (which is why
 * weight_type returns a option nat_star that can take the None value). 
 *)
Definition weight_type := trans_type -> place_type -> option nat_star.

(* Associates a nat to some place p, corresponding to the 
 * current number of tokens marking p.
 *)
Definition marking_type := place_type -> nat.

(*******************************************************************)
(**********************  Priority relation *************************)
(* to DETERMINE the Petri net (along with the imperative semantic) *)
(*******************************************************************)

(*

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
Inductive prior_type : Set := mk_prior { Lol : list (list trans_type); }.
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

(**************************************************)
(*** Defines the structure of Simple Petri Nets ***)
(**************************************************)
Structure SPN : Set :=
  mk_SPN {
      places : list place_type;
      transs : list trans_type;
      (*  different_place : NoDup places ;
          different_trans : NoDup transs ; *)
      pre : weight_type;
      post : weight_type;
      test : weight_type ;
      inhib : weight_type ;
      marking : marking_type ;                     
      priority : prior_type ;
  }.

(* Let's suppose that 
1) all places are different (NoDup ...)
2) all transitions are different (NoDup ...)

3) priority/prior_type  
forme une partition des transitions, partition correspondante
aux classes de "conflits structurels" (arcs amonts en commum)
*) 

(**************************************************************)
(************ Are 2 nat/places/transitions equal ? ************)
(**************************************************************)

(*** Formal specification : beq_places ***)
Inductive beq_places_spec : place_type -> place_type -> Prop :=
| beq_places_mk :
    forall (p p' : place_type) (n : nat), 
    p = mk_place n /\ p' = mk_place n -> beq_places_spec p p'.

(* Function : Returns true if p and p' have the same index. 
 *            false otherwise.
 *)
Definition beq_places (p p' : place_type) : bool :=
  match (p, p') with
  | (mk_place n, mk_place n') => beq_nat n n'
  end.

Functional Scheme beq_places_ind :=
  Induction for beq_places Sort Prop.

(*** Correctness proof : beq_places ***)
Theorem beq_places_correct :
  forall (p p' : place_type),
  beq_places p p' = true -> beq_places_spec p p'.
Proof.
  intros p p'.
  functional induction (beq_places  p p') using beq_places_ind.
  intro H. rewrite beq_nat_true_iff in H. rewrite H.
  apply beq_places_mk with (n:=n').
  split; reflexivity. 
Qed.

(*** Completeness proof : beq_places ***)
Theorem beq_places_complete :
  forall (p p' : place_type),
  beq_places_spec p p' -> beq_places p p' = true. 
Proof.
  intros p p' H. elim H.
  intros  p0 p1  n  H01.
  assert (H0 : p0 = mk_place n).  { firstorder. }  
  assert (H1 : p1 = mk_place n).  { firstorder. }                   
  unfold beq_places. rewrite H1. rewrite H0.
  rewrite beq_nat_true_iff. reflexivity.
Qed.

(*** Formal specification : beq_transs ***)
Inductive beq_transs_spec : trans_type -> trans_type -> Prop :=
| beq_transs_mk :
    forall (t t' : trans_type) (n : nat), 
      t = mk_trans n /\ t' = mk_trans n -> beq_transs_spec t t'.

(* Function : Returns true if t and t' have the same index.
 *            false otherwise.
 *)
Definition beq_transs (t t' : trans_type) : bool :=
  match (t, t') with
  | (mk_trans n, mk_trans n') => beq_nat n n'
  end.

Functional Scheme beq_transs_ind :=
  Induction for beq_transs Sort Prop.

(*** Correctness prooof : beq_transs ***)
Theorem beq_transs_correct :
  forall (t t' : trans_type),
    beq_transs      t t' = true        ->
    beq_transs_spec t t'.
Proof.
  intros t t'.
  functional induction (beq_transs  t t') using beq_transs_ind.
  intro H. rewrite beq_nat_true_iff in H. rewrite H.
  apply beq_transs_mk with (n:=n').
  split; reflexivity. 
Qed.

(*** Completeness proof : beq_transs ***)
Theorem beq_transs_complete :
  forall (t t' : trans_type),
    beq_transs_spec t t'               ->
    beq_transs      t t' = true. 
Proof.
  intros t t' H. elim H.
  intros  t0 t1  n  H01.
  assert (H0 : t0 = mk_trans n). { firstorder. }  
  assert (H1 : t1 = mk_trans n). { firstorder. }                   
  unfold beq_transs. rewrite H1. rewrite H0.
  rewrite beq_nat_true_iff. reflexivity.
Qed.

(*** Equality decidability for place_type. ***)
Definition places_eq_dec :
  forall x y : place_type, {x = y} + {x <> y}.
Proof.
  decide equality.
  decide equality.
Defined.

(*** Equality decidability for trans_type. ***)
Definition transs_eq_dec :
  forall x y : trans_type, {x = y} + {x <> y}.
Proof.
  decide equality.
  decide equality.
Defined.

(*********************************************************)
(************** ANIMATING THE PETRI NET ******************)
(************** (semantics definition)  ******************)
(*********************************************************)

(*==================================================*)
(*=============== MODIFY MARKING ===================*)
(*==================================================*)

(*** Formal specification : modif_mark ***)
Inductive modif_mark_spec
          (m : marking_type)
          (p2modif : place_type)
          (j : option nat_star)
          (op : nat -> nat -> nat)
          (p2get : place_type) : nat -> Prop :=
(* Case where j = None. *)
| modif_mark_eq_none :
    (beq_places p2modif p2get) = true ->
    j = None ->
    modif_mark_spec m p2modif j op p2get (m p2modif)
(* Case where j = Some nat_star. *)
| modif_mark_eq_some :
    forall (i : nat_star) (n : nat) (pf : n > 0),
      (beq_places p2modif p2get) = true          ->
      j = (Some i)                      ->
      i = (mk_nat_star n pf)            ->
      modif_mark_spec
        m p2modif j op p2get  (op (m p2modif) n)
(* Case where p2modif and p2get are two different places. *)
| modif_mark_neq :
    (beq_places p2modif p2get) = false           ->
    modif_mark_spec
      m p2modif j op p2get (m p2get).

(* Function : Given a marking m, add/remove j tokens (if j is not None)
 *            inside place p2modif and give the marking in place p2get.
 *
 * Param p2get : extra place argument, if not given, the modif_mark
 *               function returns a marking application (place_type -> nat).  
 *)
Definition modif_mark
           (m : marking_type)
           (p2modif : place_type)
           (j : option nat_star)
           (op : nat -> nat -> nat)  (* add or substract *)
           (p2get : place_type) : nat :=
  if beq_places p2modif p2get
  then
    match j with
    | None => m p2modif          (*  (m p2get) works too *)
    | Some i => match i with
                | mk_nat_star inti _ => op (m p2modif) inti
                end
    end
  else m p2get.         (* other places left unchanged  *) 

Functional Scheme modif_mark_ind :=
  Induction for modif_mark Sort Prop.

(*** Correctness proof : modif_mark ***)
Theorem modif_mark_correct :
  forall (m : marking_type)
         (p2modif p2get : place_type)
         (j : option nat_star)
         (op : nat -> nat -> nat)
         (mp : nat),
    modif_mark m p2modif j op p2get = mp ->
    modif_mark_spec m p2modif j op p2get mp.
Proof.
  intros m p2modif p2get j op mp.
  functional induction (modif_mark m p2modif j op p2get)
             using modif_mark_ind.
  - intro H.
    rewrite <- H.
    apply modif_mark_eq_some
      with (i:= {| int := inti; posi := _x |}) (pf := _x);
      try reflexivity;
      assumption.
  - intro H. rewrite <- H. apply modif_mark_eq_none.
    assumption. reflexivity.
  - intro H. rewrite <- H. apply modif_mark_neq. assumption.
Qed.

(*** Completeness proof : modif_mark ***)
Theorem modif_mark_complete :  forall
    (m : marking_type) (p2modif p2get : place_type)
    (j : option nat_star) (op : nat -> nat -> nat) (mp : nat),
    modif_mark_spec m p2modif j op p2get mp ->
    modif_mark m p2modif j op p2get = mp. 
Proof.
  intros m p2modif p2get j op  mp H. elim H.
  - intros Hbeq_true Hnone_j. unfold modif_mark.
    rewrite Hbeq_true. rewrite Hnone_j. reflexivity.
  - intros i n pf Hsome_j Hji Hi_n_pf. unfold modif_mark.
    rewrite Hsome_j. rewrite Hji. rewrite Hi_n_pf. reflexivity.
  - intros Hbeq_false. unfold modif_mark. rewrite Hbeq_false. reflexivity.
Qed.

(*=================================================*)
(*=============== UPDATE MARKING ==================*)
(*=================================================*)

(*** Formal specification : update_marking_pre ***)
Inductive update_marking_pre_spec
          (t : trans_type)
          (pre : weight_type)
          (m : marking_type)
  : list place_type -> marking_type -> Prop :=
| update_marking_pre_nil :
    update_marking_pre_spec t pre m [] m 
| update_marking_pre_cons :
    forall (p : place_type)
           (tail : list place_type)
           (m_modif m_fin : marking_type),
    m_modif = (modif_mark m p (pre t p) Nat.sub) ->
    update_marking_pre_spec t pre m_modif tail m_fin ->
    update_marking_pre_spec t pre m (p :: tail) m_fin.

(*
 * Function : Remove some tokens - accordingly to the firing of t. 
 *            Returns a new marking function.
 *)
Fixpoint update_marking_pre
         (t : trans_type)
         (pre : weight_type)
         (m : marking_type)
         (places : list place_type)
  : marking_type :=
  match places with
  | [] => m
  | cons p tail => update_marking_pre
                     t
                     pre
                     (modif_mark m p (pre t p) Nat.sub)
                     tail
  end.

Functional Scheme update_marking_pre_ind :=
  Induction for update_marking_pre Sort Prop.

(*** Correctness proof : update_marking_pre ***)
Theorem update_marking_pre_correct :
  forall (places : list place_type)
         (t : trans_type)
         (pre : weight_type)
         (m m_updated : marking_type),
    (update_marking_pre t pre m places) = m_updated ->
    (update_marking_pre_spec t pre m places m_updated).
Proof.
  intros places t pre m m_updated.
  functional induction (update_marking_pre  t pre m places)
             using update_marking_pre_ind.
  - intro Hnil. rewrite <- Hnil. apply update_marking_pre_nil.
  - intro Hcons.
    apply update_marking_pre_cons
      with (m_modif := modif_mark m p (pre t p) Nat.sub).
    + reflexivity.
    + apply (IHm0 Hcons). 
Qed.

(*** Completeness proof : update_marking_pre ***)
Theorem update_marking_pre_complete :
  forall (places : list place_type)
         (t : trans_type)
         (pre : weight_type)
         (m m_updated : marking_type),
    (update_marking_pre_spec t pre m places m_updated) ->
    (update_marking_pre t pre m places) = m_updated.
Proof.
  intros places t pre m m_updated Hspec. elim Hspec.
  - simpl. reflexivity.
  - intros m_init p tail m_modif m_fin Hmodif Htailspec Htail.
    simpl. rewrite <- Hmodif. rewrite Htail. reflexivity.
Qed.

(************************************************************)
(************** Downhill (output set, postset) **************)
(************************************************************)

(*** Formal specification : update_marking_post ***)
Inductive update_marking_post_spec
          (t : trans_type)
          (post : weight_type)
          (m : marking_type)
  : list place_type -> marking_type -> Prop :=
  
| update_marking_post_nil :
    update_marking_post_spec t post m [] m
                             
| update_marking_post_cons :
    forall (p : place_type)
           (tail : list place_type)
           (m_modif m_fin : marking_type),
    m_modif = (modif_mark m p (post t p) Nat.add) ->
    (update_marking_post_spec t post m_modif tail m_fin) ->
    (update_marking_post_spec t post m (p :: tail) m_fin).

(* 
 * Function : Add some tokens - accordingly to the firing of t.
 *            Returns a new marking application. 
 *)
Fixpoint update_marking_post (* structural induction over list of places *)
         (t : trans_type)
         (post : weight_type)
         (m : marking_type)
         (places : list place_type) : marking_type :=
  match places with
  | [] => m
  | cons p tail => (update_marking_post
                      t
                      post
                      (modif_mark m p (post t p) Nat.add)
                      tail) 
  end.

Functional Scheme update_marking_post_ind :=
  Induction for update_marking_post Sort Prop.

(*** Correctness proof : update_marking_post ***)
Theorem update_marking_post_correct : forall
    (places : list place_type)     (t : trans_type)
    (post : weight_type)   (m m_updated : marking_type),
    update_marking_post        t post m places  = m_updated     ->
    update_marking_post_spec   t post m places    m_updated.
Proof.
  intros places t post m m_updated.
  functional induction (update_marking_post  t post m places)
             using update_marking_post_ind.
  - intro Hnil. rewrite <- Hnil. apply update_marking_post_nil.
  - intro Hcons.
    apply update_marking_post_cons
      with (m_modif := modif_mark m p (post t p) Nat.add).
    + reflexivity. 
    + apply (IHm0 Hcons).      
Qed.

(*** Completeness proof : update_marking_post ***)
Theorem update_marking_post_complete : forall
    (places : list place_type)    (t : trans_type)
    (post : weight_type)    (m m_updated : marking_type),
    update_marking_post_spec  t post m places    m_updated       ->
    update_marking_post       t post m places  = m_updated.
Proof.
  intros places t post m m_updated Hspec. elim Hspec.
  - simpl. reflexivity.
  - intros m_init p tail m_modif m_fin Hmodif Htail_spec Htail.
    simpl. rewrite <- Hmodif. rewrite Htail. reflexivity.
Qed.  

(****************************************************)
(***          Update marking post and pre.        ***)
(*** (only useful for asynchronous Petri nets...) ***)
(****************************************************)

(*** Formal specification : update_marking ***)
(* Only one trivial case, because we already 
 * have the proof that update_marking_pre and
 * update_marking_post are correct and complete regarding
 * their specs. 
 * update_marking just calls the update_marking_pre
 * then the update_marking_post functions. 
 *)
Inductive update_marking_spec
          (places : list place_type)
          (t : trans_type)
          (pre post : weight_type)
          (m : marking_type) : marking_type -> Prop :=
| update_marking_mk :
    (update_marking_spec places
                         t
                         pre
                         post
                         m
                         (update_marking_post t
                                              post
                                              (update_marking_pre t pre m places)
                                              places)).

(* Function : Updates the marking for all the places in
 *            the list places, resulting of the firing
 *            of transition t.
 *            Returns an updated marking application.
 *)
Definition update_marking
           (places : list place_type) 
           (t : trans_type)
           (pre post : weight_type)
           (m : marking_type) : marking_type :=
  (update_marking_post t
                       post
                       (update_marking_pre t pre m places)
                       places).

Functional Scheme update_marking_ind :=
  Induction for update_marking Sort Prop.

(*** Correctness proof : update_marking ***)
Theorem update_marking_correct :
  forall (places : list place_type)
         (t : trans_type)
         (pre post : weight_type)
         (m m_updated : marking_type),
  (update_marking places t pre post m) = m_updated ->
  (update_marking_spec places t pre post m m_updated).
Proof.
  intros places t pre post m m_updated.
  functional induction (update_marking places t pre post m)
             using update_marking_ind.
  intro H. rewrite <- H. apply update_marking_mk.
Qed.

(*** Completeness proof : update_marking ***)
Theorem update_marking_complete :
  forall (places : list place_type)
         (t : trans_type)
         (pre post : weight_type)
         (m m_updated : marking_type),
  (update_marking_spec places t pre post m m_updated) ->
  (update_marking places t pre post m) = m_updated.
Proof.
  intros places t pre post m m_updated H. elim H.
  unfold update_marking. reflexivity.
Qed.

(**********   To print the markings  ***********************)
(*** list the tokens !!!! ***)

(*** Formal specification : marking2list ***)
Inductive marking2list_spec (m : marking_type) :
  list place_type -> list (place_type * nat) -> Prop :=
| marking2list_nil : marking2list_spec m [] []
| marking2list_cons :
    forall (p : place_type)
           (tail : list place_type)
           (couples_tail : list (place_type * nat)),
    marking2list_spec m tail couples_tail ->  
    marking2list_spec m (p :: tail) ((p, m p) :: couples_tail).

(*  
 * Function : Returns a list of couple (place, nat)
 *            associating each place with its marking.
 *)
Fixpoint marking2list
         (m : marking_type)
         (places : list place_type) : list (place_type * nat) :=
  match places with
  | [] => []
  | p :: tail =>  (p, m p) :: (marking2list m tail)
  end.

Functional Scheme marking2list_ind :=
  Induction for marking2list Sort Prop.

(*** Correctness proof : marking2list ***)
Theorem marking2list_correct :
  forall (places : list place_type)
         (m : marking_type)
         (couples : list (place_type * nat)),
  marking2list m places = couples ->
  marking2list_spec m places couples.
Proof.
  intros places m.
  functional induction (marking2list  m  places)
             using marking2list_ind.
  - intros couples H. rewrite <- H. apply marking2list_nil.
  - intros couples H. rewrite <- H. apply marking2list_cons.
    apply (IHl (marking2list m tail)). reflexivity. 
Qed.    

(*** Completeness proof : marking2list ***)
Theorem marking2list_complete :
  forall (places : list place_type)
         (m : marking_type)
         (couples : list (place_type * nat)),
  marking2list_spec m places couples ->
  marking2list m places = couples.
Proof.
  intros places m couples Hspec. elim Hspec.
  - simpl. reflexivity.
  - intros p tail couples_tail  Hspectail Htail.
    simpl. rewrite Htail. reflexivity. 
Qed. 

(******************************************************************)
(*** Checks that there are enough tokens in predecessor places. ***)
(******************************************************************)

Search bool.
Print modif_mark_spec.

(**** uphill (input set, preset) ***)

(*** Formal specification : pre_or_test_check ***)
Inductive pre_or_test_check_spec
          (pre_or_test_arcs_t : place_type -> option nat_star)
          (m : marking_type) : list place_type -> Prop :=
| pre_or_test_check_nil :
    pre_or_test_check_spec pre_or_test_arcs_t m []
                           
| pre_or_test_check_cons_none :
    forall (p:place_type)
           (tail:list place_type),
    pre_or_test_arcs_t p = None ->
    pre_or_test_check_spec pre_or_test_arcs_t m tail ->
    pre_or_test_check_spec pre_or_test_arcs_t m (p :: tail)
                           
| pre_or_test_check_cons_some :
    forall (p:place_type)
           (tail:list place_type)
           (pos:nat_star)
           (n:nat)
           (pf : n > 0),
    pre_or_test_arcs_t p = Some pos ->
    pos = {| int := n; posi := pf |} ->
    (n <= (m p)) -> (* marquage suffisant en place p *)           
    pre_or_test_check_spec pre_or_test_arcs_t m tail ->
    pre_or_test_check_spec pre_or_test_arcs_t m (p :: tail).

(*
 * Function : Returns true if all places in the places list
 *            have a marking superior or equal to pre(t)(p)
 *            or test(t)(p).
 *
 * Param pre_or_test_arcs_t : pre(t) and test(t) returning
 *                            the weight of the edge coming
 *                            from some place p towards transition t.
 *                            
 *)
Fixpoint pre_or_test_check
         (pre_or_test_arcs_t : place_type -> option nat_star)
         (m : marking_type)
         (places : list place_type) : bool :=
  match places with
  | nil => true
  | cons h tail => match pre_or_test_arcs_t h with
                   | None => pre_or_test_check pre_or_test_arcs_t m tail 
                   | Some n => match n with
                               | mk_nat_star int posi =>
                                 (int <=? (m h)) && (pre_or_test_check
                                                       pre_or_test_arcs_t
                                                       m
                                                       tail)
                               end
                   end
  end.

Functional Scheme pre_or_test_check_ind :=
  Induction for pre_or_test_check Sort Prop.

(*** Correctness proof : pre_or_test_check ***)
Theorem pre_or_test_check_correct :
  forall (places : list place_type)
         (pre_or_test_arcs_t : place_type -> option nat_star)
         (m : marking_type),
    (pre_or_test_check pre_or_test_arcs_t m places = true) ->
    (pre_or_test_check_spec pre_or_test_arcs_t m places).
Proof.
  intros places pre_or_test_arcs_t m.
  functional induction (pre_or_test_check
                          pre_or_test_arcs_t   m  places)
             using pre_or_test_check_ind.
  - intro Htrue. apply pre_or_test_check_nil.
  - intro Hconj.
    SearchPattern ( ?a = true /\ ?b = true ). (* and_prop *)
    assert (Hconjb : int0 <=? m h = true  /\
                     pre_or_test_check
                       pre_or_test_arcs_t   m   tail  = true).
    { apply andb_prop. apply Hconj. }    
    apply pre_or_test_check_cons_some with
        (pos:={| int := int0; posi := _x |})
        (n:=int0) (pf:=_x).
    + assumption.
    + reflexivity.
    + apply leb_complete. apply (proj1 Hconjb).
    + apply (IHb (proj2 Hconjb)).
  - intro Htail. apply pre_or_test_check_cons_none.
    + assumption.
    + apply (IHb Htail).    
Qed.

(*** Completeness proof : pre_or_test_check ***)
Theorem pre_or_test_check_complete :
  forall (places : list place_type)
         (pre_or_test_arcs_t : place_type -> option nat_star)
         (m : marking_type),
    (pre_or_test_check_spec pre_or_test_arcs_t m places) ->
    (pre_or_test_check pre_or_test_arcs_t m places) = true.
Proof.
  intros places  pre_or_test_arcs_t  m  H. elim H.
  - simpl. reflexivity.
  - intros p tail Hnone Hspectail Htail. simpl.
    rewrite Hnone. assumption.
  - intros p tail pos n pf Hsome Hposnpf Hnmp Hspectail Htail.
    simpl. rewrite Hsome. rewrite Hposnpf.
    SearchPattern ( ?a && ?b = true ).
    apply andb_true_intro. split.
    + apply leb_correct.  apply Hnmp. 
    + assumption.
Qed.

Print pre_or_test_check_spec.

(**************************************************)
(**************************************************)

(*** Formal specification : inhib_check ***)
Inductive inhib_check_spec
          (inhib_arcs_t : place_type -> option nat_star)
          (m : marking_type) : list place_type -> Prop :=
| inhib_check_nil : inhib_check_spec inhib_arcs_t m []

| inhib_check_cons_none :
    forall (p:place_type)
           (tail:list place_type),
    inhib_arcs_t p = None ->
    inhib_check_spec inhib_arcs_t m tail ->
    inhib_check_spec inhib_arcs_t m (p::tail)

| inhib_check_cons_some :
    forall (p:place_type)
           (tail:list place_type)
           (pos:nat_star)
           (n:nat) (pf : n > 0),
    inhib_arcs_t p = Some pos ->
    pos = {| int := n; posi := pf |} ->
    (m p < n) ->
    inhib_check_spec inhib_arcs_t m tail -> 
    inhib_check_spec inhib_arcs_t m (p::tail).

(*
 * Function : Returns true if all places in the places list
 *            have a marking less equal than inhib(t)(p).
 *            inhib(t)(p) denoting the function associating
 *            a weight to a inhibiting edge coming from place
 *            p to transition t. 
 *)
Fixpoint inhib_check
         (inhib_arcs_t : place_type -> option nat_star)
         (m : marking_type)
         (places : list place_type) : bool :=
  match places with
  | nil => true
  | cons h tail => match inhib_arcs_t h with
                   | None => (inhib_check inhib_arcs_t m tail)
                   | Some n => match n with
                               | mk_nat_star int posi =>
                                   ((m h) <? int) && (inhib_check inhib_arcs_t m tail)
                               end
                   end
  end.

Functional Scheme inhib_check_ind :=
  Induction for inhib_check Sort Prop.

(*** Correctness proof : inhib_check ***)
Theorem inhib_check_correct :
  forall (places : list place_type)
         (inhib_arcs_t : place_type -> option nat_star)
         (m : marking_type),
    inhib_check        inhib_arcs_t  m   places  = true        ->
    inhib_check_spec   inhib_arcs_t  m   places.
Proof.
  intros places   inhib_arcs_t   m.
  functional induction (inhib_check
                          inhib_arcs_t   m  places)
             using inhib_check_ind.
  - intro H. apply inhib_check_nil.
  - intro Hconj. SearchPattern ( ?a = true /\ ?b = true ).
    assert (Hconjb : m h <? int0 = true      /\
                     inhib_check
                       inhib_arcs_t   m  tail = true).
    { apply andb_prop. apply Hconj. }    
    apply inhib_check_cons_some with
        (pos:={| int := int0; posi := _x |})
        (n:=int0) (pf:=_x).
    + assumption.
    + reflexivity.
    + unfold Nat.ltb in Hconjb. unfold lt.
      apply leb_complete. apply (proj1 Hconjb). 
    + apply (IHb (proj2 Hconjb)).
  - intro Htail. apply inhib_check_cons_none.
    + assumption.
    + apply (IHb Htail).    
Qed.

(*** Completeness proof inhib_check ***)
Theorem inhib_check_complete :
  forall (places : list place_type)
         (inhib_arcs_t : place_type -> option nat_star)
         (m : marking_type),
    inhib_check_spec   inhib_arcs_t  m  places     ->
    inhib_check        inhib_arcs_t  m  places  = true.
Proof.
  intros places  inhib_arcs_t  m  Hspec. elim Hspec.
  - simpl. reflexivity.
  - intros p tail Hnone Hspectail Htail. simpl.
    rewrite Hnone. assumption.
  - intros p tail pos n pf Hsome Hposnpf Hmpn Hspectail Htail.
    simpl. rewrite Hsome. rewrite Hposnpf.
    SearchPattern ( ?a && ?b = true ). apply andb_true_intro. split.
    + apply leb_correct. unfold lt in Hmpn. assumption.
    + assumption.
Qed.

(*****************************************************)
(*****************************************************)

Print pre_or_test_check.
Inductive synchro_check_arcs_spec
          (places : list place_type)
          (pre_arcs_t : place_type -> option nat_star)
          (test_arcs_t : place_type -> option nat_star)
          (inhib_arcs_t : place_type -> option nat_star)
          (m_steady m_decreasing : marking_type) : Prop :=
| synchro_check_arcs_mk : 
    (pre_or_test_check
       pre_arcs_t
       m_decreasing
       places) &&
    (pre_or_test_check
       test_arcs_t
       m_steady
       places) &&
    (inhib_check
       inhib_arcs_t
       m_steady
       places) = true ->
    (synchro_check_arcs_spec places
                             pre_arcs_t
                             test_arcs_t
                             inhib_arcs_t
                             m_steady
                             m_decreasing).
(* 
 * Function : Returns true if a certain transition t
 *            is sensitized according to a marking m_steady
 *            (or m_decreasing) on the list of places "places" and
 *            to some weight fuctions pre_arcs_t, test_arcs_t
 *            and inhib_arcs_t.
 *)
Definition synchro_check_arcs
           (places : list place_type)
           (pre_arcs_t : place_type -> option nat_star)
           (test_arcs_t : place_type -> option nat_star)
           (inhib_arcs_t : place_type -> option nat_star)
           (m_steady m_decreasing : marking_type) : bool :=
  (pre_or_test_check pre_arcs_t m_decreasing places) &&
  (pre_or_test_check test_arcs_t m_steady places) &&
  (inhib_check inhib_arcs_t m_steady places).

Functional Scheme synchro_check_arcs_ind :=
  Induction for synchro_check_arcs Sort Prop.  (* warning *)

(*** Correctness proof : synchro_check_arcs ***)
Theorem synchro_check_arcs_correct :
  forall (places : list place_type)
         (pre_arcs_t : place_type -> option nat_star)
         (test_arcs_t : place_type -> option nat_star)
         (inhib_arcs_t : place_type -> option nat_star)
         (m_steady     m_decreasing    : marking_type),
    synchro_check_arcs
      places      pre_arcs_t   test_arcs_t   inhib_arcs_t
      m_steady    m_decreasing    
    = true 
    ->
    synchro_check_arcs_spec
      places      pre_arcs_t   test_arcs_t   inhib_arcs_t
      m_steady    m_decreasing.
Proof.
  intros places  pre_arcs_t   test_arcs_t   inhib_arcs_t
         m_steady   m_decreasing    H.
  unfold synchro_check_arcs in H. 
  apply synchro_check_arcs_mk. assumption.
Qed.

(*** Completeness proof synchro_check_arcs ***)
Theorem synchro_check_arcs_complete :
  forall (places : list place_type)
         (pre_arcs_t : place_type -> option nat_star)
         (test_arcs_t : place_type -> option nat_star)
         (inhib_arcs_t : place_type -> option nat_star)
         (m_steady     m_decreasing    : marking_type),
    synchro_check_arcs_spec
      places    pre_arcs_t     test_arcs_t    inhib_arcs_t
      m_steady    m_decreasing   
    ->
    synchro_check_arcs
      places    pre_arcs_t     test_arcs_t    inhib_arcs_t
      m_steady    m_decreasing    
                                          = true.
Proof.
  intros places pre_arcs_t test_arcs_t inhib_arcs_t
  m_steady   m_decreasing   Hspec. elim Hspec.
  intros H3true. unfold synchro_check_arcs. assumption.
Qed.

(*****************************************************************)
(*********   FIRING ALGORITHM    for SPN      ********************)
(*****************************************************************)

(*** Formal specification : spn_class_fire_pre_aux ***)
Inductive spn_class_fire_pre_aux_spec
          (places : list place_type)
          (pre test inhib : weight_type)  
          (m_steady : marking_type)
  : (list trans_type) ->   (* class *)
    (list trans_type) ->   (* fired_pre_class *)
    marking_type      ->   (* m_decreasing *)

    (list trans_type) ->   (* fired_pre_class *)
     marking_type     ->   (* m_decreasing *)
    Prop :=
| class_nil :
    forall
      (m_decreased : marking_type)
      (fired_pre_class : list trans_type),
      spn_class_fire_pre_aux_spec
        places            pre  test  inhib  m_steady              
        []
        fired_pre_class   m_decreased
        fired_pre_class   m_decreased
| class_cons_if :
    forall
      (t : trans_type)
      (tail    fired_pre_class  fpc : list trans_type)
      (m_decreasing_low  m_decreasing_high  m : marking_type),
    synchro_check_arcs
      places    (pre t) (test t) (inhib t)
      m_steady  m_decreasing_high
    = true
    ->
    m_decreasing_low = (update_marking_pre
                          t   pre   m_decreasing_high  places)
    ->
    spn_class_fire_pre_aux_spec
      places          pre  test  inhib   m_steady
      tail
      (fired_pre_class ++ [t])  m_decreasing_low
      fpc                          m
    ->
    spn_class_fire_pre_aux_spec
      places          pre  test  inhib   m_steady
      (t::tail)
      fired_pre_class       m_decreasing_high
      fpc                   m
| class_cons_else :
    forall
      (t : trans_type)
      (tail   fired_pre_class   fpc : list trans_type)
      (m_decreasing   m : marking_type),
    synchro_check_arcs
      places    (pre t) (test t) (inhib t)
      m_steady  m_decreasing
    = false
    ->
    spn_class_fire_pre_aux_spec
      places           pre  test  inhib   m_steady
      tail
      fired_pre_class    m_decreasing  
      fpc                m 
    ->
    spn_class_fire_pre_aux_spec
      places           pre  test  inhib   m_steady                   
      (t::tail)
      fired_pre_class    m_decreasing
      fpc                m.

(* Function : Given 1 ordered class of transitions 
 *            in structural conflict (a list class_transs), 
 *            returns 1 list of transitions "subclass_half_fired" 
 *            and marking "m_intermediate" accordingly ...
 *
 *            Returns a couple (list of transitions, marking)
 *            For each transition of the list that are sensitized
 *            the marking of the pre-condition places are updated (the 
 *            transition is fired). "marking" is then the resulting marking.
 *)
Fixpoint spn_class_fire_pre_aux
         (places : list place_type)
         (pre test inhib : weight_type)  
         (m_steady : marking_type)
         (* "fired_pre_class" meant  to be empty at first *)
         (class_transs fired_pre_class : list trans_type)  
         (m_decreasing : marking_type) : (list trans_type) * marking_type :=
  match class_transs with
  | t :: tail => if (synchro_check_arcs places (pre t) (test t) (inhib t) m_steady m_decreasing)
                 then (* change and inductive progress *)  
                   let new_decreasing := (update_marking_pre t pre m_decreasing places)
                   in (spn_class_fire_pre_aux places
                                              pre
                                              test
                                              inhib
                                              m_steady
                                              tail
                                              (fired_pre_class ++ [t])
                                              new_decreasing)
                 else (* no change but inductive progress *)
                   (spn_class_fire_pre_aux places
                                           pre
                                           test
                                           inhib
                                           m_steady   
                                           tail
                                           fired_pre_class
                                           m_decreasing)
  | []  => (fired_pre_class, m_decreasing)
  end.

(* 
 * There are 2 parallel calculus in spn_class_fire_pre_aux : 
 * 1. pumping tokens to get "m_intermediate_decreasing" (half fired)
 * 2. returning subclass of transitions (half fired)
 *
 * and 2 markings are recorded : 
 * 1. the initial one to check with inhib and test arcs
 * 2. a floating (decreasing) intermediate marking to check classic arcs
 *)

Functional Scheme spn_class_fire_pre_aux_ind :=
  Induction for spn_class_fire_pre_aux Sort Prop.

(*** Correctness proof : spn_class_fire_pre_aux ***)
Theorem spn_class_fire_pre_aux_correct :
  forall (places : list place_type)
         (pre  test  inhib : weight_type)
         (m_steady      m_decreasing      m_final : marking_type)
         (class_transs  fired_pre_class  fpc_final : list trans_type),
    spn_class_fire_pre_aux
      places    pre   test   inhib   m_steady
      class_transs
      fired_pre_class     m_decreasing 
    = (fpc_final,         m_final)
    ->
    spn_class_fire_pre_aux_spec
      places    pre   test   inhib   m_steady                 
      class_transs
      fired_pre_class   m_decreasing
      fpc_final         m_final.
Proof. 
  intros places pre test inhib  m_steady  m_decreasing m_final
  class_transs fired_pre_class  fpc_final.
  functional induction (spn_class_fire_pre_aux
                          places  pre test inhib  m_steady  
                          class_transs
                          fired_pre_class    m_decreasing)
             using spn_class_fire_pre_aux_ind.
  - intro Heq. inversion Heq. apply class_nil.
  - intro Htail.
    apply class_cons_if
      with (m_decreasing_low := (update_marking_pre
                                   t pre m_decreasing  places)).
    + assumption. 
    + reflexivity.
    + apply (IHp Htail).      
  - intro Htail. apply class_cons_else.
    + assumption. 
    + apply (IHp Htail).
Qed.

(*** Completeness proof : spn_class_fire_pre_aux ***)
Theorem spn_class_fire_pre_aux_complete :
  forall (places : list place_type)
         (pre  test  inhib : weight_type)
         (m_steady   m_decreasing     m_final : marking_type)
         (class_transs  fired_pre_class  fpc_final : list trans_type),
    spn_class_fire_pre_aux_spec
      places         pre test inhib   m_steady               
      class_transs
      fired_pre_class      m_decreasing
      fpc_final            m_final
    ->
    spn_class_fire_pre_aux
      places         pre test inhib   m_steady         
      class_transs
      fired_pre_class      m_decreasing 
    = (fpc_final ,         m_final).
Proof.
  intros places  pre  test  inhib m_steady   m_decreasing   m_final
         class_transs  fired_pre_class  fpc_final Hspec. elim Hspec.
  - simpl. reflexivity.
  - intros  t  tail fired_pre_class0  fpc_final0
            m_decreasing_low  m_decreasing_high  m
            Hsynchro Hdecreasing_low Hspectail Htail. simpl.
    rewrite Hsynchro. rewrite <- Hdecreasing_low. rewrite Htail.
    reflexivity.
  - intros  t  tail fired_pre_class0  fpc_final0
            m_decreasing0  m Hnsynchro Hspectail Htail. simpl.
    rewrite Hnsynchro. rewrite Htail. reflexivity. 
Qed.

(****** spn_class_fire_pre_aux  ----> spn_class_fire_pre ********)

(*** Formal specification : spn_class_fire_pre ***)
Inductive spn_class_fire_pre_spec
          (places : list place_type)
          (pre   test   inhib : weight_type)  
          (m_steady     : marking_type)
          (class_transs : list trans_type)
          (m_decreasing : marking_type) : (list trans_type) -> marking_type -> Prop :=
| spn_sub_fire_pre_mk :
    forall (subclass_fired_pre : list trans_type)
           (m_fired_pre_class : marking_type),
      (spn_class_fire_pre_aux
         places pre test inhib m_steady class_transs [] m_decreasing)   
      = (subclass_fired_pre, m_fired_pre_class) ->
      (spn_class_fire_pre_spec
         places pre test inhib m_steady class_transs m_decreasing
         subclass_fired_pre m_fired_pre_class).

(*  
 * Function : Wrapper function around spn_class_fire_pre_aux.
 *)
Definition spn_class_fire_pre
           (places : list place_type)
           (pre test inhib : weight_type) 
           (m_steady : marking_type) 
           (class_transs : list trans_type)
           (m_decreasing : marking_type) : (list trans_type) * marking_type :=
  (spn_class_fire_pre_aux
     places pre test inhib m_steady class_transs [] m_decreasing).

Functional Scheme spn_class_fire_pre_ind :=
  Induction for spn_class_fire_pre Sort Prop.

(*** Correctness proof : spn_class_fire_pre ***)
Theorem spn_class_fire_pre_correct :
  forall (places : list place_type)
         (pre  test  inhib : weight_type)
         (m_steady   m_decreasing     m_decreased : marking_type)
         (class_transs     fired_pre_class  : list trans_type),
    spn_class_fire_pre
      places        pre test inhib    m_steady             
      class_transs
                         m_decreasing
    = (fired_pre_class,  m_decreased)
    ->
    spn_class_fire_pre_spec
      places        pre test inhib    m_steady               
      class_transs
                         m_decreasing
      fired_pre_class    m_decreased.
Proof.
  intros places pre test inhib m_steady m_decreasing m_decreased
         class_transs  fired_pre_class.
  functional induction (spn_class_fire_pre
                          places  pre test inhib   m_steady  
                          class_transs    m_decreasing)
             using spn_class_fire_pre_ind.
  apply spn_sub_fire_pre_mk. 
Qed. 

(*** Completeness proof : spn_class_fire_pre ***)
Theorem spn_class_fire_pre_complete :
  forall (places : list place_type)
         (pre  test  inhib : weight_type)
         (m_steady   m_decreasing     m_decreased : marking_type)
         (class_transs    subclass_fired_pre  : list trans_type),
    spn_class_fire_pre_spec
      places         pre test inhib   m_steady                
      class_transs
                            m_decreasing
      subclass_fired_pre    m_decreased
    ->
    spn_class_fire_pre
      places         pre test inhib   m_steady             
      class_transs
                           m_decreasing
    = (subclass_fired_pre, m_decreased).
Proof.
  intros places pre test inhib m_steady m_decreasing m_decreased
         class_transs  fired_pre_class  H. elim H.
  intros fired_pre_class0  m_decreased0 Haux.
  unfold spn_class_fire_pre. assumption.
Qed.

(********** spn_class_fire_pre ---> spn_fire_pre(_aux) ***********)
(*** ici on gere l'ensemble des classes **************************)

(*** Formal specification : spn_fire_pre_aux ***)
Inductive spn_fire_pre_aux_spec
          (places : list place_type)
          (pre test inhib : weight_type)
          (m_steady  : marking_type)
  : list (list trans_type)   ->  (* classes   *)
    list (list trans_type)   ->  (* fired_pre_classes *)
    marking_type             ->  (* m_decreasing *)
    list (list trans_type)   ->  (* fired_pre_classes *)
    marking_type             ->  (* m_decreasing *)
    Prop :=
| classes_nil :
    forall
      (classes_fired_pre : list (list trans_type))
      (m_decreased : marking_type),
    (spn_fire_pre_aux_spec
       places pre test inhib m_steady []
       classes_fired_pre m_decreased
       classes_fired_pre m_decreased)
      
| classes_cons :
    forall
      (classes_tail fired_pre_classes any_classes : list (list trans_type))
      (class class_fired_pre : list trans_type)
      (m_decreased_class m_decreasing m_any : marking_type),
    (class_fired_pre, m_decreased_class) =
    (spn_class_fire_pre
       places pre test inhib m_steady   
       class
       m_decreasing) ->
    (spn_fire_pre_aux_spec
       places pre test inhib m_steady
       classes_tail
       (class_fired_pre :: fired_pre_classes) m_decreased_class
       any_classes m_any) ->
    (spn_fire_pre_aux_spec
       places pre test inhib m_steady
       (class :: classes_tail)
       fired_pre_classes m_decreasing
       any_classes m_any).

(*
 * Function : Apply spn_class_fire_pre over ALL classes of transitions. 
 *            Begin with initial marking; End with half fired marking.  
 *            "classes_fired_pre" is empty at first 
 *)
Fixpoint spn_fire_pre_aux
         (places : list place_type)
         (pre test inhib : weight_type)
         (m_steady : marking_type)
         (classes classes_fired_pre : list (list trans_type))
         (m_decreasing : marking_type) : (list (list trans_type)) * marking_type :=
  match classes with
  | [] => (classes_fired_pre, m_decreasing)
  | class :: classes_tail => let (class_fired_pre, m_decreased_class) :=
                                 (spn_class_fire_pre
                                    places pre test inhib m_steady
                                    class m_decreasing)
                             in (spn_fire_pre_aux
                                   places pre test inhib m_steady   
                                   classes_tail
                                   (class_fired_pre :: classes_fired_pre)
                                   m_decreased_class)
  end.

Functional Scheme spn_fire_pre_aux_ind :=
  Induction for spn_fire_pre_aux   Sort Prop.

(*** Correctness proof : spn_fire_pre_aux ***)
Theorem spn_fire_pre_aux_correct :
  forall (places : list place_type)
         (pre   test  inhib : weight_type)
         (m_steady  m_decreasing  m_decreased : marking_type)
         (classes_transs   classes_fired_pre_growing
                           classes_fired_pre : list (list trans_type)),
    spn_fire_pre_aux
      places             pre   test  inhib   m_steady
      classes_transs
      classes_fired_pre_growing  m_decreasing
    = (classes_fired_pre, m_decreased)
    ->
    spn_fire_pre_aux_spec
      places             pre   test  inhib   m_steady           
      classes_transs
      classes_fired_pre_growing  m_decreasing
      classes_fired_pre   m_decreased.
Proof.
  do 10 intro.
  functional induction (spn_fire_pre_aux
                          places0     pre0 test0 inhib0  m_steady
                          classes_transs
                          classes_fired_pre_growing   m_decreasing)
             using spn_fire_pre_aux_ind.
  - intro Heq. inversion Heq. apply classes_nil.
  - intro Htail.
    apply classes_cons
      with (class_fired_pre := fst (spn_class_fire_pre
                                      places0 pre0 test0 inhib0 m_steady
                                      class m_decreasing))
           (m_decreased_class := snd (spn_class_fire_pre
                                        places0 pre0 test0 inhib0 m_steady
                                        class  m_decreasing)).
    + rewrite e0. simpl. reflexivity.
    + rewrite e0. simpl. apply (IHp Htail).
Qed.

(*** Completeness proof : spn_fire_pre_aux ***)
Theorem spn_fire_pre_aux_complete :
  forall (places : list place_type)
         (pre   test  inhib : weight_type)
         (m_steady  m_decreasing  m_decreased : marking_type)
         (classes_transs   fired_pre_classes_rec
                           fired_pre_classes : list (list trans_type)),
    spn_fire_pre_aux_spec
      places         pre   test  inhib   m_steady
      classes_transs
      fired_pre_classes_rec    m_decreasing
      fired_pre_classes        m_decreased
    -> 
    spn_fire_pre_aux
      places             pre   test  inhib   m_steady
      classes_transs
      fired_pre_classes_rec    m_decreasing
    = (fired_pre_classes,      m_decreased).
Proof.
  intros places pre test inhib m_steady m_decreasing m_decreased
         classes_transs  fired_pre_classes_rec fired_pre_classes H.
  elim H.
  - intros fired_pre_classes0 m_decreased0. simpl. reflexivity.
  - intros classes_tail fired_pre_classes0 any_classes
           class fired_pre_class  m_decreased_class
           m_decreasing0 m_any Heq Hspectail Htail.
    simpl. rewrite <- Heq. apply Htail.
Qed.

(******* spn_fire_pre_aux   --->  spn_fire_pre ******************)
(***** just apply  ..._aux  with good arguments 
*********  that is an empty list    for fired_pre_classes
*********  and m_steady             for m_decreasing  *) 

(*** Formal specification : spn_fire_pre ***)
Inductive spn_fire_pre_spec
          (places : list place_type)
          (pre test inhib : weight_type)
          (m_steady : marking_type)
          (classes_transs  : list (list trans_type))
  : (list (list trans_type)) -> marking_type -> Prop :=
| spn_fire_pre_mk :
    forall (classes_fired_pre : list (list trans_type))
           (m_inter : marking_type),
      spn_fire_pre_aux
        places           pre    test    inhib   m_steady
        classes_transs
        []                  m_steady
      = (classes_fired_pre, m_inter)
      ->
      spn_fire_pre_spec
        places              pre  test  inhib
        m_steady            classes_transs
        classes_fired_pre   m_inter.

(*
 * Function : Update the marking by consuming
 *            the tokens in pre-condition places.            
 *)
Definition spn_fire_pre
         (places : list place_type)
         (pre test inhib : weight_type)
         (m_steady : marking_type)
         (classes_transs  : list (list trans_type)) :
  (list (list trans_type)) * marking_type :=
  
  (spn_fire_pre_aux
     places pre test inhib m_steady
     classes_transs
     [] m_steady).

Functional Scheme spn_fire_pre_ind :=
  Induction for spn_fire_pre   Sort Prop.

(*** Correctness proof : spn_fire_pre ***)
Theorem spn_fire_pre_correct :
  forall (places : list place_type)
         (pre  test  inhib : weight_type)
         (m_steady   m_inter : marking_type)
         (classes_transs  fired_pre_classes : list (list trans_type)),
    spn_fire_pre
      places           pre   test   inhib    m_steady
      classes_transs  
    = (fired_pre_classes, m_inter)
    ->
    spn_fire_pre_spec
      places           pre   test   inhib    m_steady
      classes_transs
      fired_pre_classes   m_inter.
Proof.
  intros places pre  test  inhib m_steady   m_inter
         classes_transs  fired_pre_classes.
  functional induction (spn_fire_pre
                          places      pre test inhib
                          m_steady     classes_transs)
             using spn_fire_pre_ind.
  apply spn_fire_pre_mk. 
Qed. 

(*** Completeness proof : spn_fire_pre ***)
Theorem spn_fire_pre_complete :
  forall (places : list place_type)
         (pre  test  inhib : weight_type)
         (m_steady   m_inter : marking_type)
         (classes_transs  fired_pre_classes : list (list trans_type)),
    spn_fire_pre_spec
      places           pre test inhib    m_steady
      classes_transs
      fired_pre_classes    m_inter
    ->
    spn_fire_pre
      places           pre test inhib    m_steady
      classes_transs  
    = (fired_pre_classes,  m_inter).
Proof.
  intros places pre  test  inhib m_steady   m_inter
         classes_transs  fired_pre_classes H. elim H.
  intros fired_pre_classes0 m_inter0 Heq.
  unfold spn_fire_pre. assumption.
Qed.

(***********************************************************)
(***********  POST   ***************************************)
(****  not useful to separate in classes ...  but... *******)

(*** Formal specification : class_fire_post ***)
Inductive class_fire_post_spec 
          (places : list place_type)
          (post : weight_type) :
  marking_type ->   (* m_increasing *) 
  list trans_type -> (* class_fired_pre *)
  marking_type -> (* m_increased_class *)
  Prop :=
| class_fire_post_nil :
    forall ( m_increasing  : marking_type),
    (class_fire_post_spec places post m_increasing [] m_increasing)
        
| class_fire_post_cons :
    forall (t : trans_type)
           (tail : list trans_type)
           (m_increasing  m_any  : marking_type),
    (class_fire_post_spec
      places post
      (update_marking_post t post m_increasing places)
      tail m_any) ->
    (class_fire_post_spec
       places      post    m_increasing
       (t :: tail)   m_any).

(*
 * Function : Given a marking "m_intermediate", resulting of the call
 *            of the function spn_fire_pre, and after 
 *            that a given subclass of transs has been pre-fired 
 *            (the "class_fired_pre" list of transitions), 
 *            returns the marking increased by the post-condition edges.  
 *)
Fixpoint class_fire_post
         (places : list place_type)
         (post : weight_type)
         (m_increasing : marking_type)
         (class_fired_pre : list trans_type) : marking_type := 
  match class_fired_pre with
  | []  => m_increasing
  | t :: tail  => (class_fire_post
                     places
                     post
                     (update_marking_post t post m_increasing places)
                     tail)
  end.

Functional Scheme class_fire_post_ind :=
  Induction for class_fire_post   Sort Prop.

(*** Correctness proof : class_fire_post ***)
Theorem class_fire_post_sound :
  forall (places : list place_type)
         (post : weight_type)
         (m_increasing   m_increased : marking_type)
         (class_fired_pre : list trans_type),
    class_fire_post
      places   post     m_increasing
      class_fired_pre   =   m_increased
    ->
    class_fire_post_spec
      places   post     m_increasing        
      class_fired_pre       m_increased.
Proof.
  intros places post  m_increasing  m_increased class_fired_pre.
  functional induction (class_fire_post
                          places   post   m_increasing   
                          class_fired_pre)
             using class_fire_post_ind.
  - intro Heq. rewrite Heq.  apply class_fire_post_nil.
  - intro Hcons. apply class_fire_post_cons. apply (IHm Hcons).
Qed.

(*** Completeness proof : class_fire_post ***)
Theorem class_fire_post_complete :
  forall (places : list place_type)
         (post : weight_type)
         (m_increasing   m_increased : marking_type)
         (class_half_fired  : list trans_type),
    class_fire_post_spec
      places   post    m_increasing        
      class_half_fired      m_increased
    ->
    class_fire_post
      places   post    m_increasing
      class_half_fired    = m_increased.
Proof.
  intros places post  m_increasing  m_increased class_fired_pre H.
  elim H.
  - simpl. reflexivity.
  - simpl. auto. 
Qed.

(**********  Again not useful to separate in classes ... *********)
(***********...  except to print fired transs beautifully ********)

(*** Formal specification : fire_post ***)
Inductive fire_post_spec
          (places : list place_type)
          (post : weight_type) :
  marking_type             -> (* m_increasing *)
  list (list trans_type)   -> (*fired_pre_classes *)
  marking_type             -> (* m_increasing *)
  Prop  := 
| fire_post_nil :
    forall (m_increasing : marking_type),
    fire_post_spec
      places
      post
      m_increasing
      []  m_increasing
      
| fire_post_cons :
    forall (greater_m m any_m : marking_type)
           (tail : list (list trans_type))
           (class : list trans_type), 
    fire_post_spec
      places post greater_m tail any_m
    ->
    greater_m = class_fire_post
                  places post m class
    ->
    fire_post_spec
      places post m (class :: tail) any_m.

(* 
 * Function : Meant to begin with intermediate marking 
 *            computed by "fire_pre", after half (pre arcs) 
 *            firing of ALL the chosen transitions.
 *            Ends with the FINAL marking of the cycle ! 
 *)
Fixpoint fire_post
         (places : list place_type)
         (post : weight_type)
         (m_increasing : marking_type)
         (fired_pre_classes : list (list trans_type)) : marking_type := 
  match fired_pre_classes with
  | []  => m_increasing
  | class :: tail  => let greater_m := (class_fire_post
                                          places post
                                          m_increasing
                                          class)
                      in (fire_post places post greater_m tail)                     
  end. 

Functional Scheme fire_post_ind :=
  Induction for fire_post   Sort Prop.

(*** Correctness proof : fire_post ***)
Theorem fire_post_sound :
  forall (places : list place_type)
         (post : weight_type)
         (m_increasing  m_final : marking_type)
         (classes_firind : list (list trans_type)),
    fire_post
      places   post     m_increasing
      classes_firind   =   m_final
    ->
    fire_post_spec
      places   post     m_increasing        
      classes_firind       m_final.
Proof.
  intros places  post m_increasing  m_final classes_firind.
  functional induction (fire_post
                          places         post
                          m_increasing    classes_firind)
             using fire_post_ind.
  -  intro Heq. rewrite Heq. apply fire_post_nil.
  -  intro Htail.
     apply fire_post_cons
       with (greater_m := class_fire_post
                            places  post  m_increasing class).
     + apply (IHm Htail).
     + reflexivity.
Qed.

(*** Completeness proof : fire_post ***)
Theorem fire_post_complete :
  forall (places : list place_type)
         (post : weight_type)
         (m_increasing  m_final : marking_type)
         (classes_firind : list (list trans_type)),
    fire_post_spec
      places   post     m_increasing        
      classes_firind       m_final
    ->
    fire_post
      places   post     m_increasing
      classes_firind   =   m_final
.
Proof.
  intros places post  m_increasing m_final classes_firind Hspec.
  elim Hspec.
  - simpl. reflexivity.
  - intros greater_m m any_m tail class Hspectail Htail Hgreater.
    simpl. rewrite <- Htail. rewrite Hgreater. reflexivity.
Qed.

(*************************************************)
(****************** SPN FIRE *********************)
(*************************************************)

(*** Formal specification : spn_fire ***)
Inductive spn_fire_spec   
          (places : list place_type)
          (pre test inhib post : weight_type)
          (m_steady : marking_type)
          (classes_transs : list (list trans_type))
  : (list (list trans_type))   ->
    marking_type               ->
    Prop :=
| spn_fire_mk :
    forall (sub_Lol : list (list trans_type))
           (m_inter m : marking_type),
    (sub_Lol, m_inter) = spn_fire_pre
                           places  pre test inhib 
                           m_steady   classes_transs
    ->
    m = fire_post
          places post   m_inter  sub_Lol
    ->
    spn_fire_spec   
      places         pre test inhib post
      m_steady       classes_transs
      sub_Lol    m.

(*  
 * Function : Returns  "transitions fired (Lol)" + "final marking",
 *            branching spn_fire_post with spn_fire_pre   
 *)
Definition spn_fire  
           (places : list place_type)
           (pre test inhib post : weight_type)
           (m_steady : marking_type)
           (classes_transs : list (list trans_type))
  : (list (list trans_type)) * marking_type :=
  let (sub_Lol, m_inter) := (spn_fire_pre places
                                          pre
                                          test
                                          inhib 
                                          m_steady
                                          classes_transs)
  in (sub_Lol, (fire_post places post m_inter sub_Lol)).

Functional Scheme spn_fire_ind :=
  Induction for  spn_fire   Sort Prop.

(*** Correctness proof : spn_fire ***)
Theorem spn_fire_correct :
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
      m_steady   classes_transs      sub_Lol  m_next.
Proof.
  intros places pre test inhib post  m_steady m_next
         classes_transs sub_Lol.
  functional induction (spn_fire
                          places      pre test inhib post
                          m_steady  classes_transs)
             using spn_fire_ind.
  intro Heq. inversion Heq. 
  apply spn_fire_mk with (m_inter := m_inter).
  - rewrite H0 in e. rewrite e. reflexivity.
  - reflexivity.
Qed.

(*** Completeness proof : spn_fire ***)
Theorem spn_fire_complete :
  forall (places : list place_type)
         (pre  test  inhib   post : weight_type)
         (m_steady   m_next : marking_type)
         (classes_transs   sub_Lol : list (list trans_type)),
    spn_fire_spec
      places   pre  test  inhib  post
      m_steady   classes_transs       sub_Lol  m_next
    ->
    spn_fire
      places   pre  test  inhib  post
      m_steady   classes_transs   =  (sub_Lol, m_next).
Proof.
  intros places pre test inhib post  m_steady m_next
         classes_transs sub_Lol H. elim H.
  intros sub_Lol0 m_inter m Heq Hm.
  unfold spn_fire. rewrite <- Heq. rewrite Hm. reflexivity.
Qed.

(*********************************************************)
(************* TO ANIMATE A SPN (AND DEBUG) **************)
(*********************************************************)

(*
 * Function : Returns the list of lists of transitions
 *            fired and a list of pair (place, nboftokens), 
 *            corresponding to the intermediate marking
 *            after pre-condition resolution.
 *   
 *)
Definition spn_print_fire_pre (spn : SPN) :
  (list (list trans_type)) * list (place_type * nat) :=
  match spn with
  | (mk_SPN places transs pre post test inhib m (mk_prior Lol)) =>
    let (sub_Lol, m) := (spn_fire_pre places pre test inhib m Lol)
    in (sub_Lol, (marking2list m places))
  end.

(* (spn_debug1 places pre test inhib m Lol) *)

(************************************************************)
(****************** SPN CYCLE EVOLUTION *********************)
(************************************************************)

(*** Formal specification : spn_cycle ***)
Inductive spn_cycle_spec (spn : SPN) :
  list (list trans_type) -> SPN -> Prop :=
| spn_cycle_mk :
    forall (sub_Lol Lol : list (list trans_type))
           (next_m m : marking_type)
           (next_spn : SPN)
           (places : list place_type)
           (transs : list trans_type)
           (pre post test inhib : weight_type),
    spn = (mk_SPN places transs pre post test inhib m (mk_prior Lol)) ->
    (sub_Lol, next_m) = (spn_fire places pre test inhib post m Lol) ->
    next_spn = (mk_SPN places transs pre post test inhib next_m (mk_prior Lol)) -> 
    (spn_cycle_spec spn sub_Lol next_spn).

(*  
 * Function : Returns the resulting Petri net after all the sensitized
 *            transitions in spn have been fired, and returns
 *            the list of lists containing these transitions.
 *            
 *)
Definition spn_cycle (spn : SPN) : (list (list trans_type)) * SPN :=
  match spn with
  | (mk_SPN places transs pre post test inhib m (mk_prior Lol)) =>
    let (sub_Lol, next_m) := (spn_fire places pre test inhib post m Lol)
    in (sub_Lol, (mk_SPN places transs pre post test inhib next_m (mk_prior Lol)))
  end.

Functional Scheme spn_cycle_ind :=
  Induction for spn_cycle   Sort Prop.

(*** Correctness proof : spn_cycle ***)
Theorem spn_cycle_correct :
  forall (spn  next_spn : SPN)
         (sub_Lol : list (list trans_type)),
    spn_cycle
      spn    =  (sub_Lol, next_spn)
    ->
    spn_cycle_spec
      spn        sub_Lol  next_spn.
Proof.
  intros  spn  next_spn  sub_Lol.
  functional induction (spn_cycle spn)
             using spn_cycle_ind.
  intro Heq.
  apply spn_cycle_mk
    with (Lol:=Lol0) (next_m:=next_m) (m:=m)
         (places:=places0) (transs:=transs0)
         (pre:=pre0) (post:=post0) (test:=test0) (inhib:=inhib0).
  - reflexivity.
  - rewrite e1. inversion Heq. reflexivity.
  - inversion Heq. reflexivity.
Qed.

(*** Completeness proof : spn_cycle ***)
Theorem spn_cycle_complete :
  forall (spn next_spn : SPN)
         (sub_Lol : list (list trans_type)),
  (spn_cycle_spec spn sub_Lol next_spn) ->
  (spn_cycle spn) = (sub_Lol, next_spn).
Proof.
  intros spn next_spn sub_Lol H. elim H.
  intros. unfold spn_cycle. rewrite  H0. rewrite <- H1.
  rewrite H2. reflexivity.
Qed.

(*******************************************)
(******** ANIMATING DURING N CYCLES ********)
(*******************************************)

(*** Formal specification : spn_animate ***)
Inductive spn_animate_spec (spn : SPN) :
  nat -> list (list (list trans_type) * list (place_type * nat)) -> Prop :=
| animate_spn_O : spn_animate_spec spn O [ ([], []) ]
| animate_spn_S :
    forall (next_spn : SPN)
           (Lol_fired : list (list trans_type))
           (visual_marking : list (place_type * nat))
           (n : nat)
           (TAIL : list (list (list trans_type) * list (place_type * nat))),
    (Lol_fired, next_spn) = spn_cycle spn ->
    visual_marking = (marking2list (marking next_spn) (places next_spn)) ->
    (spn_animate_spec next_spn n TAIL) -> 
    (spn_animate_spec spn (S n) ((Lol_fired, visual_marking) :: TAIL)).

(*  
 * Function : Returns the list of (transitions_fired(i), marking(i))
 *            for each cycle i, from 0 to n, representing the evolution
 *            of the Petri net spn.
 *)
Fixpoint spn_animate (spn : SPN) (n : nat) :
  list ((list (list trans_type)) * (list (place_type * nat))) :=
  match n with
  | O => [ ([], []) ]
  | S n' => let (Lol_fired, next_spn) := (spn_cycle spn) 
            in (Lol_fired, (marking2list (marking next_spn) (places next_spn))) ::
               (spn_animate next_spn n')
  end.

Functional Scheme spn_animate_ind :=
  Induction for spn_animate   Sort Prop.

(*** Correctness proof : spn_animate ***)
Theorem spn_animate_correct :
  forall (spn : SPN) (n : nat) (couples : list (list (list trans_type) *
                                                list (place_type * nat))),
  spn_animate spn n = couples -> spn_animate_spec spn n couples.
Proof.
  intros spn n.
  functional induction (spn_animate spn n) using spn_animate_ind.
  - intros couples Heq. rewrite <- Heq. apply animate_spn_O.
  - intros couples Htail. rewrite <- Htail.
    apply animate_spn_S with (next_spn := snd (spn_cycle spn)).
    + rewrite e0. simpl. reflexivity.
    + rewrite e0. simpl. reflexivity.
    + rewrite e0. simpl.
      apply (IHl (spn_animate next_spn n')). reflexivity.
Qed.

(*** Completeness proof : spn_animate ***)
Theorem spn_animate_complete :
  forall (spn : SPN) (n : nat) (couples : list (list (list trans_type)  *
                                                list (place_type * nat))),
  (spn_animate_spec spn n couples) -> spn_animate spn n = couples.
Proof.
  intros spn n couples H. elim H.
  - simpl. reflexivity. 
  - intros. simpl. rewrite <- H0. rewrite <- H1. rewrite <- H3.
    reflexivity.
Qed.

(*****************************************************************)
(*****************************************************************)
(**** HOW TO get the classes of transitions...    from what ? ****)
(*************** sections sorting ********************************)

(*
Require Import Coq.Sorting.Sorted. Search sort.

Section insertion_sort.


  Print prior_type1. Print prior_type2.
  Fixpoint insert (a : trans_type)
                  (l : list trans_type)
                  (prior1 : prior_type1) : list trans_type :=
    match l with
    | nil  => [a]
    | b :: l' => match prior1 with
                 | mk_prior_type1 rel irre assym trans =>
                   if (rel a b)
                   then a :: l
                   else b :: (insert a l' prior1)
               end
    end.
  
  Fixpoint sort (l : list trans_type)
                (prior1 : prior_type1) : list trans_type :=
    match l with
    | [] => []
    | a :: l' => insert a (sort l' prior1) prior1
    end.
  
  (* Fixpoint find_highest (A:Type) (l:list A) : (A * list A) :=
    match l with
    | nil => (a, nil)
    | b::l' => if leb a b
               then find_highest b l'
               else find_highest a l'
    end.*)

  Definition sort_transs (prior1 : prior_type1)
                         (l : list trans_type) : list trans_type := (sort l prior1).
  
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
