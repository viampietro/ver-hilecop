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
      mini_le_maxi : mini <= maxi  ;
      cpt  : nat ;   (* possibly 0   /!\  *)
      (* in_range  : bool      mini <= cpt <= maxi 
sumbool ? ; *)
    }.

Definition time_check (maybe_chrono : option chrono_type) : bool :=
  match maybe_chrono with
  | None => true
  | Some (mk_chrono
            mini
            maxi
            _
            cpt ) =>  ((mini <=? cpt)
                         &&
                         (cpt <=? maxi))
  end.
Inductive time_check_spec
          (maybe_chrono : option chrono_type)
  : Prop :=
| time_check_none : 
    maybe_chrono = None                             -> 
    time_check_spec
      maybe_chrono
| time_check_some : forall
    (mini maxi cpt: nat)
    (mini_le_maxi : mini <= maxi),
    maybe_chrono = Some (mk_chrono
                           mini
                           maxi
                           mini_le_maxi
                           cpt )                    ->
    (mini <=? cpt)
      &&
      (cpt <=? maxi) = true              ->
    time_check_spec
      maybe_chrono.
Functional Scheme time_check_ind :=
  Induction for time_check Sort Prop.
Theorem time_check_correct : forall
    (maybe_chrono : option chrono_type),
    time_check       maybe_chrono = true     ->
    time_check_spec  maybe_chrono.
Proof.
  intros maybe_chrono.
  functional induction (time_check  maybe_chrono)
             using time_check_ind.
  - intro Htrue.
    apply time_check_some with (mini:=mini0) (maxi:=maxi0)
                               (cpt:=cpt0) (mini_le_maxi:=_x).
    + reflexivity.
    + exact Htrue.
  - intro H. apply time_check_none. reflexivity.
Qed.
Theorem time_check_complete : forall
    (maybe_chrono : option chrono_type),
    time_check_spec  maybe_chrono            ->
    time_check       maybe_chrono = true.     
Proof.
  intros maybe_chrono Hspec. elim Hspec.
  - intro Hnone. unfold time_check. rewrite Hnone. reflexivity.
  - intros mini maxi cpt min_leb_max Hsome Htrue.
    unfold time_check. rewrite Hsome. exact Htrue.
Qed.

Structure STPN : Set := mk_STPN
                           { 
                             spn : SPN ;
                             all_chronos :
                               trans_type -> option chrono_type
                           }.



(******* to print *****************************************)
Print chrono_type. Print STPN.

Fixpoint intervals2list
         (all_chronos : trans_type -> option chrono_type)
         (transs : list trans_type)
  : list (trans_type * option (nat * nat * nat) ) :=
  match transs with
  | nil => nil
  | t :: tail => match (all_chronos t) with
                 | None  => (t, None) :: (intervals2list
                                            all_chronos
                                            tail)
                 | Some (mk_chrono
                           mini
                           maxi
                           _
                           cpt) =>
                   (t, Some (mini, cpt, maxi)) :: (intervals2list
                                                     all_chronos
                                                     tail)
                 end
  end.
Inductive intervals2list_spec
          (all_chronos : trans_type -> option chrono_type)
  : list trans_type                            ->   
    list (trans_type *
          option (nat * nat * nat) )           ->
  Prop :=
| intervals2list_nil :  intervals2list_spec
                          all_chronos [] []
| intervals2list_none : forall
    (transs_tail : list trans_type)
    (t : trans_type)
    (couples  : list (trans_type * option (nat * nat * nat))),
    (all_chronos t) = None                  ->
    intervals2list_spec
      all_chronos transs_tail  couples      ->
    intervals2list_spec
      all_chronos (t :: transs_tail) ((t, None) :: couples)
| intervals2list_some : forall
    (transs_tail : list trans_type)
    (t : trans_type)
    (chrono_t : chrono_type)
    (couples  : list (trans_type * option (nat * nat * nat)))
    (mini maxi cpt: nat)
    (mini_le_maxi : mini <= maxi),
    (all_chronos t) = Some chrono_t                ->
    chrono_t = mk_chrono
                 mini    maxi
                 mini_le_maxi      cpt             ->
    intervals2list_spec
      all_chronos transs_tail  couples             ->
    intervals2list_spec
      all_chronos
      (t :: transs_tail)
      ((t, Some (mini, cpt, maxi)) :: couples).
Functional Scheme intervals2list_ind :=
  Induction for intervals2list Sort Prop.
Theorem intervals2list_correct : forall
    (transs : list trans_type)
    (all_chronos : trans_type -> option chrono_type)
    (couples : list (trans_type * option (nat * nat * nat))),
    intervals2list
      all_chronos   transs = couples    ->
    intervals2list_spec
      all_chronos   transs    couples.
Proof.
  intros transs all_chronos.
  functional induction (intervals2list  all_chronos  transs)
             using intervals2list_ind.
  - intros couples  H. rewrite <- H. apply intervals2list_nil.
  - intros couples  H. rewrite <- H.
    apply intervals2list_some
      with (chrono_t := mk_chrono
                          mini0 maxi0 _x cpt0) (mini_le_maxi := _x).
    + assumption. 
    + reflexivity.
    + apply (IHl (intervals2list  all_chronos  tail)). reflexivity.
  - intros couples  H. rewrite <- H. apply intervals2list_none.
    + assumption.
    + apply (IHl (intervals2list  all_chronos  tail)). reflexivity. 
Qed.
Theorem intervals2list_complete : forall
    (transs : list trans_type)
    (all_chronos : trans_type -> option chrono_type)
    (couples : list (trans_type * option (nat * nat * nat))),
    intervals2list_spec
      all_chronos    transs    couples   ->
    intervals2list
      all_chronos    transs =  couples.    
Proof.
  intros transs all_chronos couples H. elim H.
  - simpl. reflexivity.
  - intros. simpl. rewrite H0. rewrite H2. reflexivity.
  - intros. simpl. rewrite H0. rewrite H1. rewrite H3. reflexivity.
Qed.

(**************  end of "to print"  ******************)


(** "enabled" <=> "arcs_classic" + "arcs_test" + "arcs_inhi" OK **)
Definition trans_enabled
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
Functional Scheme trans_enabled_ind :=
  Induction for trans_enabled Sort Prop.
Print trans_enabled_ind. Print nat_ind.
Inductive trans_enabled_spec
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
    trans_enabled_spec
      places   pre   test  inhib   m_steady    t.
Theorem trans_enabled_correct :
  forall (places : list place_type)
          (pre   test  inhib : weight_type)
          (m_steady : marking_type) (t : trans_type),
    trans_enabled
      places      pre   test  inhib
      m_steady    t   = true        ->
    trans_enabled_spec
      places      pre   test  inhib
      m_steady    t.
Proof.
  intros places pre test inhib m_steady t.
  functional induction (trans_enabled
                          places pre test inhib m_steady t)
             using trans_enabled_ind.
  intro Htrue. apply is_enabled_mk. apply Htrue.  
Qed.
Theorem is_enabled_complete :
  forall (places : list place_type)
          (pre   test  inhib : weight_type)
          (m_steady : marking_type) (t : trans_type),
    trans_enabled_spec
      places      pre   test  inhib
      m_steady    t      ->
    trans_enabled
      places      pre   test  inhib
      m_steady    t   = true .
Proof.
  intros places pre   test  inhib m_steady  t Hspec. elim Hspec.
  intros Htrue. unfold trans_enabled. rewrite Htrue. reflexivity.
Qed.
(**   useless fonction for SPN but useful for 

-  _asynchronous_ Petri nets
-   STPN  (and SITPN by extension) 

  needed to list the enabled transitions :

1) to increment time for the right transitions, 
at the beginning of the cycle

2) to reset disabled transitions ?? 
NO !  because   m_steady   &  ! m_decreasing !    **)

Fixpoint list_enabled_aux 
         (places : list place_type)
         (pre    test    inhib : weight_type) 
         (m_steady   : marking_type)
         (enabled_transs : list trans_type)
         (sometranss : list trans_type)  
  : list trans_type :=
  match sometranss with
  | [] => enabled_transs 
  | t :: tail
    =>
    if trans_enabled
         places    pre    test   inhib    m_steady   t
    then list_enabled_aux 
           places   pre   test   inhib    m_steady
           (t::enabled_transs)  tail   
    else list_enabled_aux 
           places   pre   test   inhib    m_steady
           enabled_transs       tail  
  end.
Inductive list_enabled_aux_spec
          (places : list place_type)
          (pre    test    inhib : weight_type) 
          (m_steady   : marking_type)
          (enabled_transs_rec : list trans_type)  (* ? modified *)
  : list trans_type  ->   (* sometranss *)
    
    list trans_type  ->   (* enabled_transs     *)
    Prop :=
| list_enabled_aux_nil :
    list_enabled_aux_spec 
      places   pre   test   inhib  m_steady
      enabled_transs_rec [] enabled_transs_rec
| list_enabled_aux_cons_if :  forall
    (tail  enabled_transs : list trans_type)
    (t : trans_type),
    list_enabled_aux_spec 
      places   pre   test   inhib  m_steady
      (t::enabled_transs_rec)   tail   enabled_transs
    ->
    trans_enabled
      places   pre   test   inhib  m_steady    t
    = true
    ->
    list_enabled_aux_spec 
      places   pre   test   inhib  m_steady
      enabled_transs_rec   (t::tail)   enabled_transs
| list_enabled_aux_cons_else :  forall
    (tail   enabled_transs  : list trans_type)
    (t : trans_type),
    list_enabled_aux_spec 
      places   pre   test   inhib  m_steady
      enabled_transs_rec       tail    enabled_transs
    ->
    trans_enabled
      places   pre   test  inhib   m_steady    t
    = false
    ->
    list_enabled_aux_spec 
      places   pre   test   inhib  m_steady
      enabled_transs_rec   (t::tail)   enabled_transs.

Functional Scheme list_enabled_aux_ind :=
  Induction for list_enabled_aux Sort Prop.

Theorem list_enabled_aux_correct : forall
    (sometranss enabled_transs_rec enabled_transs : list trans_type)
    (places : list place_type)
    (pre   test  inhib : weight_type)
    (m_steady : marking_type),
    list_enabled_aux
      places     pre   test  inhib   m_steady
      enabled_transs_rec    sometranss     = enabled_transs   ->
    list_enabled_aux_spec
      places     pre   test  inhib   m_steady
      enabled_transs_rec    sometranss       enabled_transs.
Proof.
  intros sometranss enabled_transs_rec enabled_transs
         places pre test inhib m_steady.
  functional induction (list_enabled_aux
                          places pre test inhib  m_steady
                          enabled_transs_rec  sometranss)
             using list_enabled_aux_ind.
  - intro Heq. rewrite Heq. apply list_enabled_aux_nil.
  - intro Htail. apply list_enabled_aux_cons_if.
    + apply (IHl Htail).
    + assumption. 
  - intro Htail. apply list_enabled_aux_cons_else.
    + apply (IHl Htail).
    + assumption.
Qed.
Theorem list_enabled_aux_complete : forall
    (sometranss enabled_transs_rec enabled_transs : list trans_type)
    (places : list place_type)
    (pre   test  inhib : weight_type)
    (m_steady : marking_type),
    list_enabled_aux_spec
      places     pre   test  inhib  m_steady
      enabled_transs_rec  sometranss      enabled_transs  ->
    list_enabled_aux
      places     pre   test  inhib  m_steady
      enabled_transs_rec  sometranss    = enabled_transs.
Proof.
  intros sometranss enabled_transs_rec enabled_transs
         places  pre   test  inhib   m_steady Hspec. elim Hspec.
  - simpl.  reflexivity.
  - intros enabled_transs_rec0 tail enabled_transs0 t
           Hspectail Htail Henabled.
    simpl. rewrite Henabled. rewrite Htail. reflexivity.
  - intros enabled_transs_rec0 tail enabled_transs0 t
           Hspectail Htail Hnotenabled.
    simpl. rewrite Hnotenabled. rewrite Htail. reflexivity.
Qed.

(****** list_enabled_aux   ->  list_enabled  *************)
Definition list_enabled 
           (sometranss : list trans_type)
           (places : list place_type)
           (pre    test    inhib : weight_type) 
           (m_steady   : marking_type)
  : list trans_type :=
  list_enabled_aux
    places    pre    test   inhib    m_steady  [] sometranss.
Inductive list_enabled_spec
           (sometranss  : list trans_type)
           (places : list place_type)
           (pre    test    inhib : weight_type) 
           (m_steady   : marking_type)            
  : list trans_type      ->
    Prop  :=
| list_enabled_mk :  forall (enabled_transs : list trans_type),
    list_enabled_aux
      places   pre   test  inhib    m_steady   [] sometranss
    = enabled_transs
    ->
    list_enabled_spec
      sometranss    places    pre    test   inhib    m_steady
      enabled_transs.
Functional Scheme list_enabled_ind :=
  Induction for list_enabled Sort Prop.
Theorem list_enabled_correct :  forall
    (sometranss  enabled : list trans_type)
    (places : list place_type)
    (pre   test  inhib : weight_type)
    (m_steady : marking_type),
    list_enabled
      sometranss  places    pre   test  inhib
      m_steady      =   enabled        ->
    list_enabled_spec
      sometranss  places    pre   test  inhib
      m_steady          enabled.
Proof.
  intros sometranss  enabled places pre test inhib m_steady.
  functional induction (list_enabled
                          sometranss  places pre test inhib
                          m_steady)
             using list_enabled_ind.
  intro H. apply list_enabled_mk. assumption.  
Qed.
Theorem list_enabled_complete : forall
    (sometranss  enabled : list trans_type)
    (places : list place_type)
    (pre   test  inhib : weight_type)
    (m_steady : marking_type),
    list_enabled_spec
      sometranss  places    pre   test  inhib
      m_steady   enabled     ->
    list_enabled
      sometranss  places    pre   test  inhib
      m_steady      =   enabled.
Proof.
  intros  sometranss  enabled places pre test inhib m_steady H.
  elim H. intros enabled_transs H0. simpl. unfold list_enabled.
  rewrite H0. reflexivity. 
Qed.

(********************************** easy spn stpn ... ********)
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
  : list trans_type  ->
    Prop  :=
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

Functional Scheme list_enabled_spn_ind :=
  Induction for list_enabled_spn Sort Prop.

Theorem list_enabled_spn_correct : forall
    (spn : SPN) (enabled : list trans_type),
    list_enabled_spn       spn = enabled        ->
    list_enabled_spn_spec  spn   enabled.
Proof.
  intros spn  enabled.
  functional induction (list_enabled_spn
                          spn)
             using list_enabled_spn_ind.
  intro H. apply list_enabled_spn_mk with
               (Lol := _x0) (m := marking)
               (places := places) (transs := transs)
               (pre:=pre) (post:=_x) (test:=test) (inhib:=inhib).
  + reflexivity.
  + assumption.   
Qed.
Theorem list_enabled_spn_complete : forall
    (spn : SPN) (enabled : list trans_type),
    list_enabled_spn_spec
      spn  enabled                  -> 
    list_enabled_spn
      spn = enabled.
Proof.
  intros spn  enabled Hspec. elim Hspec.
  intros Lol m places transs  pre post test inhib
         enabled_transs Hspn Henabled.
  unfold list_enabled_spn. rewrite Hspn. assumption. 
Qed.

(******************************** useless ******)
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
Functional Scheme list_enabled_stpn_ind :=
  Induction for list_enabled_stpn Sort Prop.
Theorem list_enabled_stpn_correct :  forall
    (stpn : STPN) (enabled : list trans_type),
    list_enabled_stpn
      stpn = enabled        ->
    list_enabled_stpn_spec
      stpn  enabled.
Proof.
  intros stpn  enabled.
  functional induction (list_enabled_stpn
                          stpn)
             using list_enabled_stpn_ind.
  intro H. apply list_enabled_stpn_mk with
               (spn := spn0) (chronos := _x).
  + reflexivity.
  + assumption.   
Qed.
Theorem list_enabled_stpn_complete : forall
    (stpn : STPN) (enabled : list trans_type),
    list_enabled_stpn_spec
      stpn  enabled                  -> 
    list_enabled_stpn
      stpn = enabled.
Proof.
  intros stpn  enabled H. elim H.
  intros. unfold list_enabled_stpn. rewrite H0. rewrite H1.
  reflexivity. 
Qed.
(**************** end of useless ***************)


(********* same as "list_enabled_(aux)"  (so 2 markings) ***********)
Print synchro_check_arcs.
Fixpoint not_synchro_check_list_aux 
         (places : list place_type)
         (pre    test    inhib : weight_type) 
         (m_steady    m_decreasing : marking_type)
         (disabled_transs : list trans_type)
         (sometranss : list trans_type)
  : list trans_type :=
  match sometranss with
  | [] => disabled_transs 
  | t :: tail
    =>
    if synchro_check_arcs
         places  (pre t) (test t) (inhib t) m_steady  m_decreasing
    then not_synchro_check_list_aux 
           places  pre   test  inhib  m_steady  m_decreasing
           disabled_transs       tail 
    else not_synchro_check_list_aux 
           places  pre   test  inhib  m_steady  m_decreasing
           (t::disabled_transs)  tail   
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
      places     pre    test    inhib  m_steady   m_decreasing
      disabled_transs      []         disabled_transs
| not_synchro_check_list_aux_cons_if :  forall
    (tail  any_transs : list trans_type)
    (t : trans_type),
    not_synchro_check_list_aux_spec 
      places     pre   test   inhib     m_steady   m_decreasing
      disabled_transs     tail       any_transs
    ->
     synchro_check_arcs
       places  (pre t) (test t) (inhib t) m_steady  m_decreasing
     = true 
    ->
    not_synchro_check_list_aux_spec  
      places     pre   test   inhib      m_steady   m_decreasing
      disabled_transs   (t::tail)   any_transs
| not_synchro_check_list_aux_cons_else :  forall
    (tail   any_transs  : list trans_type)
    (t : trans_type),
    not_synchro_check_list_aux_spec 
      places     pre   test   inhib  
      m_steady   m_decreasing   (t::disabled_transs)
      tail       any_transs
    ->
     synchro_check_arcs
       places  (pre t) (test t) (inhib t) m_steady  m_decreasing
     = false
    ->
    not_synchro_check_list_aux_spec  
      places     pre   test   inhib  
      m_steady   m_decreasing   disabled_transs
      (t::tail)  any_transs.

Functional Scheme not_synchro_check_list_aux_ind :=
  Induction for not_synchro_check_list_aux Sort Prop.

Theorem not_synchro_check_list_aux_correct :  forall
    (sometranss  disab_rec  disabled_transs: list trans_type)
    (places : list place_type)
    (pre   test  inhib : weight_type)
    (m_steady  m_decreasing : marking_type),
    not_synchro_check_list_aux 
      places   pre   test   inhib  m_steady   m_decreasing
      disab_rec   sometranss    = disabled_transs
    ->
    not_synchro_check_list_aux_spec 
      places    pre   test  inhib  m_steady   m_decreasing
      disab_rec   sometranss      disabled_transs.
Proof.
  intros sometranss  disab_rec disabled_transs
         places   pre   test   inhib  
         m_steady   m_decreasing.
  functional induction (not_synchro_check_list_aux
                          places   pre   test  inhib
                          m_steady   m_decreasing
                          disab_rec  sometranss)
             using not_synchro_check_list_aux_ind.
  - intro Heq. rewrite Heq. apply not_synchro_check_list_aux_nil.
  - intro Htail. apply not_synchro_check_list_aux_cons_if.
    + apply (IHl Htail).
    + assumption.
  - intro Htail. apply not_synchro_check_list_aux_cons_else.
    + apply (IHl Htail).
    + assumption.   
Qed.
Theorem not_synchro_check_list_aux_complete :  forall
    (sometranss  disab_rec  disabled_transs: list trans_type)
    (places : list place_type)
    (pre   test  inhib : weight_type)
    (m_steady  m_decreasing : marking_type),
    not_synchro_check_list_aux_spec 
      places   pre   test   inhib  m_steady   m_decreasing
      disab_rec    sometranss       disabled_transs
    ->
    not_synchro_check_list_aux 
      places   pre   test   inhib  m_steady   m_decreasing
      disab_rec    sometranss     = disabled_transs.  
Proof.
  intros sometranss  disab_rec disabled_transs
         places   pre   test   inhib  
         m_steady   m_decreasing  Hspec. elim Hspec.
  - intro  disab_rec0. simpl. reflexivity.
  - intros disabled_transs0 tail any_transs t
           Hspectail Htail  Hsynchro.
    simpl. rewrite Hsynchro. assumption.
  - intros disabled_transs0 tail any_transs t
           Hspectail Htail  Hnotsynchro.
    simpl. rewrite Hnotsynchro. assumption. 
Qed.

(**************************************************************)

Definition not_synchro_check_list 
         (sometranss : list trans_type)
         (places : list place_type)
         (pre    test    inhib : weight_type) 
         (m_steady    m_decreasing : marking_type)
  : list trans_type :=
  not_synchro_check_list_aux 
    places    pre  test  inhib   m_steady  m_decreasing  []
    sometranss.
Inductive not_synchro_check_list_spec
           (sometranss : list trans_type)
           (places : list place_type)
           (pre    test    inhib : weight_type) 
           (m_steady   m_decreasing : marking_type)
  : list trans_type  ->  Prop  :=
| not_synchro_check_list_mk : forall
    (enabled_transs : list trans_type),
    not_synchro_check_list_aux 
      places   pre  test  inhib  m_steady  m_decreasing  []
      sometranss
    = enabled_transs
    ->
    not_synchro_check_list_spec
      sometranss    places    pre    test   inhib
      m_steady      m_decreasing      enabled_transs.

Functional Scheme not_synchro_check_list_ind :=
  Induction for not_synchro_check_list Sort Prop.

Theorem not_synchro_check_list_correct :  forall
    (places : list place_type)
    (pre   test  inhib : weight_type)
    (m_steady   m_decreasing : marking_type)
    (some_transs  enabled_transs  : list trans_type),
    not_synchro_check_list 
      some_transs    places   pre    test    inhib
      m_steady    m_decreasing  =  enabled_transs
    ->
    not_synchro_check_list_spec
      some_transs   places    pre    test    inhib
      m_steady    m_decreasing     enabled_transs.
Proof.
  intros places  pre    test    inhib
      m_steady    m_decreasing   some_transs  enabled_transs.
  functional induction (not_synchro_check_list
                          some_transs places pre test inhib
                          m_steady m_decreasing)
             using not_synchro_check_list_ind.
  intro H. apply not_synchro_check_list_mk. assumption.   
Qed.
Theorem not_synchro_check_list_complete : forall
    (places : list place_type)
    (pre   test  inhib : weight_type)
    (m_steady   m_decreasing : marking_type)
    (some_transs  enabled_transs  : list trans_type),
    not_synchro_check_list_spec
      some_transs   places    pre    test    inhib
      m_steady    m_decreasing     enabled_transs
    ->
    not_synchro_check_list 
      some_transs   places    pre    test    inhib
      m_steady    m_decreasing  =  enabled_transs.
Proof.
  intros places  pre    test    inhib
         m_steady  m_decreasing   some_transs  enabled_transs H.
  elim H.
  intros enabled_transs0 Hnotsynchro.
  unfold not_synchro_check_list. rewrite Hnotsynchro. reflexivity.
Qed.

(***************************************************************)
(********************* TIME intervals  ---> chronos  ***********)
(********************  complexity problems *********************)

Print STPN. Print all_chronos.
(* increment time, for a given  transitions *)


Definition increment_time_trans0
           (chronos : trans_type -> option chrono_type)
           (t2incr :  trans_type)
  : trans_type -> option chrono_type :=
  match (chronos t2incr) with
  | None => chronos  (* increment nothing ... *)
  | Some (mk_chrono        (* immutable ... *)
            mini     maxi
            min_le_max      cpt)
    => (fun t =>
          if beq_transs
               t t2incr
          then Some (mk_chrono
                       mini     maxi
                       min_le_max    (cpt + 1))
          else (chronos t))                      
  end.

Definition increment_time_trans
           (all_chronos : trans_type -> option chrono_type)
           (t2incr : trans_type)
           (t : trans_type)
  : option chrono_type :=
  match (all_chronos t2incr) with
  | None  => all_chronos t   (* increment  nothing ... *)
  | Some (mk_chrono
            mini maxi min_le_max cpt) =>
    if beq_transs
         t t2incr
    then Some (mk_chrono
                 mini maxi min_le_max (cpt+1))
    else (all_chronos t)
  end.

Inductive increment_time_trans_spec
          (all_chronos : trans_type -> option chrono_type)
          (t2incr  trans : trans_type)
  : option chrono_type  ->  Prop  :=
| increment_time_trans_none : 
    (all_chronos   t2incr) = None
    ->
    increment_time_trans_spec
      all_chronos  t2incr  trans  (all_chronos  trans)
| increment_time_trans_some_if : forall
    (mini maxi cpt : nat)
    (mini_le_maxi : mini <= maxi)
    (chrono_t_incr : option chrono_type),
    (all_chronos    t2incr) = Some (mk_chrono
                                      mini  maxi
                                      mini_le_maxi   cpt)
    ->
    beq_transs    trans  t2incr   = true
    -> 
    Some (mk_chrono
            mini   maxi
            mini_le_maxi  (cpt + 1))  = chrono_t_incr 
    ->
    increment_time_trans_spec
      all_chronos    t2incr  trans  chrono_t_incr
| increment_time_trans_some_else : forall
    (mini maxi cpt : nat)
    (mini_le_maxi : mini <= maxi),
    (all_chronos    t2incr) = Some (mk_chrono
                                      mini  maxi
                                      mini_le_maxi   cpt)
    ->
    beq_transs    trans   t2incr  = false
    ->
    increment_time_trans_spec
      all_chronos     t2incr  trans  (all_chronos trans).

Functional Scheme increment_time_trans_ind :=
  Induction for increment_time_trans Sort Prop. 

Theorem increment_time_trans_correct : forall
    (chronos   : trans_type -> option chrono_type)
    (t2incr     t : trans_type)
    (chronos_incr :  option chrono_type),
    increment_time_trans
      chronos  t2incr  t   =  chronos_incr        ->
    increment_time_trans_spec
      chronos  t2incr  t      chronos_incr.
Proof.
  intros chronos  t2incr  t  chrono_incr.  
  functional induction (increment_time_trans
                          chronos  t2incr  t)
             using  increment_time_trans_ind.
  - intro Hsome. apply increment_time_trans_some_if with
                     (mini := mini0) (maxi := maxi0)
                     (cpt := cpt0) (mini_le_maxi := min_le_max).
    + assumption.
    + assumption.
    + assumption.
  - intro Heq. rewrite <- Heq.
    apply increment_time_trans_some_else with
        (mini := mini0) (maxi := maxi0)
        (cpt := cpt0) (mini_le_maxi := min_le_max).
    + assumption.
    + assumption. 
  - intro Heq. rewrite <- Heq. apply increment_time_trans_none.
    assumption. 
Qed.

Theorem increment_time_trans_complete : forall
    (chronos   : trans_type -> option chrono_type)
    (t2incr   t : trans_type)
    (chrono_incr : option chrono_type),
    increment_time_trans_spec
      chronos  t2incr  t    chrono_incr        ->
    increment_time_trans
      chronos  t2incr  t  = chrono_incr .
Proof.
  intros chronos   t2incr  trans chrono_incr Hspec. elim Hspec.
  - intro H0. unfold increment_time_trans.
    rewrite H0. reflexivity.
  - intros mini0 maxi0 cpt0 mini_le_maxi0 chrono_t_incr
           Hsome Hbeq Hchrono_incr.
    unfold increment_time_trans. rewrite Hsome. rewrite Hbeq.
    assumption.
  - intros mini0 maxi0 cpt0 mini_le_maxi0 Hsome Hnotbeq.
    unfold increment_time_trans. rewrite Hnotbeq. rewrite Hsome.
    reflexivity.
Qed.


Fixpoint increment_time_enabled0
         (chronos : trans_type -> option chrono_type)
         (enabled_transs : list trans_type)
    : trans_type -> option chrono_type  :=
  match enabled_transs with
  | [] => chronos
  | t2incr :: tail
    =>
    increment_time_enabled0
      (increment_time_trans0
         chronos   t2incr)
      tail
  end.

Fixpoint increment_time_enabled
         (chronos : trans_type -> option chrono_type)
         (enabled_transs : list trans_type)
         (t : trans_type)
  : option chrono_type  :=
  match enabled_transs with
  | [] =>   chronos   t
  | t2incr :: tail
    =>
    increment_time_enabled
      (increment_time_trans
         chronos   t2incr)
      (* partial function : trans_type -> option chrono_type *)
      tail
      t
  end.

Inductive increment_time_enabled_spec
          (chronos : trans_type -> option chrono_type)
          (t : trans_type) 
  : list trans_type                  ->   (* enabled_transs *)
    option chrono_type               ->  (* resulting chronos *)
    Prop :=
| increment_time_enabled_nil :
    increment_time_enabled_spec
      chronos  t  [] (chronos t)
| increment_time_enabled_cons : forall
    (tail : list trans_type)
    (t2incr : trans_type)
    (any_chronos : trans_type -> option chrono_type)
    (chronos_t_incr :  trans_type -> option chrono_type),
    chronos_t_incr = increment_time_trans
                       any_chronos   t2incr 
    ->
    increment_time_enabled_spec
      chronos t          tail  (chronos_t_incr t)
    ->
    increment_time_enabled_spec
      chronos t (t2incr::tail)  (any_chronos t).




(* on incremente en debut de cycle. Avec un marquage stable 
donc on se sert d'une liste de transitions enabled, 
facilement calculable *)

Functional Scheme increment_time_enabled_ind :=
  Induction for increment_time_enabled Sort Prop.  

Theorem increment_time_enabled_correct : forall
    (chronos   chronos_incr: trans_type -> option chrono_type)
    (enabled_transs :  list trans_type)
    (t : trans_type),
    increment_time_enabled
      chronos  enabled_transs  t  = (chronos_incr t)
    ->
    increment_time_enabled_spec
      chronos  t  enabled_transs    (chronos_incr t).
Proof.
  intros chronos  chronos_incr  enabled_transs t.  
  functional induction (increment_time_enabled
                          chronos  enabled_transs  t)
             using  increment_time_enabled_ind.
  - intro H. rewrite <- H. apply increment_time_enabled_nil.
  - intro H. rewrite <- H.
    apply increment_time_enabled_cons
      with (chronos_t_incr := increment_time_trans chronos t2incr).
    + unfold increment_time_trans. 
Admitted.
Theorem increment_time_enabled_complete : forall
    (chronos   chronos_incr: trans_type -> option chrono_type)
    (enabled_transs :  list trans_type)
    (t : trans_type),
    increment_time_enabled_spec
      chronos  t  enabled_transs    (chronos_incr t)   ->
    increment_time_enabled
      chronos  enabled_transs  t  = (chronos_incr t).
Proof.
  intros chronos  chronos_incr  enabled_transs  t H.  elim H.
  - simpl. reflexivity.
  - intros tail t2incr any_chronos  chronos_t_incr
           Hincr  Hspectail  Htail. simpl.
Admitted.


(**************************************************************)
(**** on fait la meme chose pour les transitions disabled ... *)


Definition reset_time_trans0
           (chronos : trans_type -> option chrono_type)
           (t2reset : trans_type)
  : trans_type -> option chrono_type :=
  match (chronos t2reset) with
  | None  => chronos   (* reset nothing ... *)
  | Some (mk_chrono
            mini    maxi   min_le_max   cpt )  =>
    (fun t =>
       if beq_transs
            t t2reset
       then Some (mk_chrono
                    mini  maxi   min_le_max   0 )
       else (chronos t))             
  end.

Definition reset_time_trans
           (chronos : trans_type -> option chrono_type)
           (t2reset   t : trans_type)
  : option chrono_type :=
  match (chronos t2reset) with
  | None  => chronos t   (* reset nothing ... *)
  | Some (mk_chrono
            mini maxi   mini_le_maxi cpt) =>
    if beq_transs  t2reset t 
    then Some (mk_chrono
                 mini maxi    mini_le_maxi 0)
    else (chronos t)
  end.

Inductive reset_time_trans_spec
          (chronos : trans_type -> option chrono_type)
          (t2reset  t :  trans_type)
  :  option chrono_type  ->  Prop  :=
| reset_time_trans_none : 
    (chronos t2reset) = None
    ->
    reset_time_trans_spec
      chronos t2reset t  (chronos t)
| reset_time_trans_some_if : forall
    (mini maxi cpt : nat)
    (min_leb_max : mini <= maxi)
    (chrono_t_reset : option chrono_type),
    (chronos t2reset) = Some (mk_chrono
                                mini  maxi
                                min_leb_max   cpt)
    ->
    beq_transs t2reset  t = true
    ->
    Some (mk_chrono
            mini   maxi
            min_leb_max  0) = chrono_t_reset
    ->
    reset_time_trans_spec
      chronos t2reset  t chrono_t_reset
| reset_time_trans_some_else : forall
    (mini maxi cpt : nat)
    (min_leb_max : mini <= maxi),
    (chronos t2reset) = Some (mk_chrono
                                mini  maxi
                                min_leb_max   cpt)
    ->
    beq_transs t2reset  t = false
    ->
    reset_time_trans_spec
      chronos t2reset  t (chronos t).

Functional Scheme reset_time_trans_ind :=
  Induction for reset_time_trans Sort Prop. 

Theorem reset_time_trans_correct :  forall
    (chronos : trans_type -> option chrono_type)
    (t2reset   t : trans_type)
    (chrono_t_reset : option chrono_type),
    reset_time_trans
      chronos    t2reset   t    =  chrono_t_reset       ->
    reset_time_trans_spec
      chronos    t2reset   t       chrono_t_reset.
Proof.
  intros  chronos  t2reset   t  chrono_t_reset.
  functional induction (reset_time_trans
                          chronos  t2reset   t)
             using reset_time_trans_ind.
  - intro H. apply reset_time_trans_some_if
               with (mini:=mini0) (maxi:=maxi0) (cpt:=_x) (min_leb_max:= mini_le_maxi0).
    + assumption.
    + assumption.
    + assumption.
  - intro H. rewrite <- H. apply reset_time_trans_some_else with
                               (mini:=mini0) (maxi:=maxi0)
                               (cpt:=_x) (min_leb_max:=mini_le_maxi0).
    + assumption.
    + assumption.
  - intro H. rewrite <- H. apply reset_time_trans_none.
    assumption. 
Qed.
Theorem reset_time_trans_complete : forall
    (chronos : trans_type -> option chrono_type)
    (t2reset   t : trans_type)
    (chrono_t_reset : option chrono_type),
    reset_time_trans_spec
      chronos    t2reset   t       chrono_t_reset   ->
    reset_time_trans
      chronos    t2reset   t    =  chrono_t_reset.
Proof.
  intros chronos  t2reset  t  chrono_t_reset H. elim H.
  - intro H0. unfold reset_time_trans.
    rewrite H0. reflexivity.
  - intros. unfold reset_time_trans.
    rewrite H0. rewrite H1. assumption.
  - intros. unfold reset_time_trans.
    rewrite H0. rewrite H1. reflexivity.
Qed.

(* 
le reset de compteur est plus subtil : 
 1) quand faut-il le faire ?  
   ----> a la fin du cycle ou plutot dans stpn_sub_fire_pre !
 2) pour quelles transitions faut-il le faire ?
   ----> celles desensibilisees durant le cycle. meme transitoirement
*)
    
(* reset time counters of (a class of ?) some transitions ... *)
Print increment_time_enabled. 
Fixpoint reset_time_disabled0
           (chronos : trans_type -> option chrono_type)
           (disabled_transs : list trans_type)
  : trans_type -> option chrono_type :=
  match disabled_transs with
  | [] => chronos
  | t2reset :: tail =>
    reset_time_disabled0
      (reset_time_trans0
         chronos  t2reset)
      tail
  end.

Fixpoint reset_time_disabled
         (chronos : trans_type -> option chrono_type)
         (disabled_transs : list trans_type)
         (t : trans_type)
  : option chrono_type  :=
  match disabled_transs with
  | [] => chronos  t
  | t2reset :: tail    =>
    reset_time_disabled
      (reset_time_trans   chronos   t2reset)
      tail
      t
  end.

Inductive reset_time_disabled_spec
          (chronos : trans_type -> option chrono_type)
          (t : trans_type)
  : list trans_type             ->   (* disabled_transs *)
    option chrono_type          ->  (* resulting chronos *)
    Prop :=
| reset_time_disabled_nil :
    reset_time_disabled_spec chronos t [] (chronos t)
| reset_time_disabled_cons : forall
    (tail : list trans_type)
    (t2reset : trans_type)
    (any_chronos : trans_type -> option chrono_type)
    (chronos_t_reset : trans_type -> option chrono_type),
    chronos_t_reset = reset_time_disabled 
                        (reset_time_trans
                           any_chronos   t2reset)
                        tail
    ->
    reset_time_disabled_spec
      chronos t tail            (chronos_t_reset t)
    ->
    reset_time_disabled_spec
      chronos t (t2reset::tail) (any_chronos t).

Functional Scheme reset_time_disabled_ind :=
  Induction for reset_time_disabled Sort Prop. 

Theorem reset_time_disabled_correct :  forall
    (chronos : trans_type -> option chrono_type)
    (disabled_transs : list trans_type)
    (t   : trans_type)
    (chrono_t_reset : option chrono_type),
    reset_time_disabled
      chronos    disabled_transs t    =  chrono_t_reset       ->
    reset_time_disabled_spec
      chronos    t  disabled_transs      chrono_t_reset.
Proof.
  intros  chronos    disabled_transs   t   chrono_t_reset.
  functional induction (reset_time_disabled
                          chronos disabled_transs t)
             using reset_time_disabled_ind.
  - intro H. rewrite <- H. apply reset_time_disabled_nil.
  - intro H. rewrite <- H. apply reset_time_disabled_cons with
                               (chronos_t_reset := chronos ).
    +  
Admitted.


 
Theorem reset_time_disabled_complete :  forall
    (chronos : trans_type -> option chrono_type)
    (disabled_transs : list trans_type)
    (t  : trans_type)
    (chrono_t_reset : option chrono_type),
    reset_time_disabled_spec
      chronos  t   disabled_transs      chrono_t_reset       ->
    reset_time_disabled
      chronos  disabled_transs   t  =   chrono_t_reset.
Proof.
  intros chronos  disabled_transs t  chrono_t_reset H. elim H.
  - simpl. reflexivity.
  - intros. simpl. unfold reset_time_disabled.
Admitted.

    

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
         (whole_class : list trans_type)
         (places : list place_type)
         (pre    test    inhib : weight_type) 
         (m_steady    : marking_type)
         (class_transs   fired_pre_class : list trans_type)
         (m_decreasing : marking_type) 
         (chronos : trans_type -> option chrono_type)
  : (list trans_type)      *
    marking_type           *
    (trans_type -> option chrono_type) :=
  match class_transs with
  | t :: tail =>
    if synchro_check_arcs
         places (pre t) (test t) (inhib t)  m_steady  m_decreasing
         (* t is enabled, even w.r.t. to the others *)
         && (time_check (chronos  t))
    then   (* firing  t *)
      let new_decreasing   :=
          (update_marking_pre
             t  pre  m_decreasing  places )
      in   (* reseting the disabled intervals ! *)
      let new_chronos :=
          (reset_time_disabled
             chronos
             (not_synchro_check_list
                whole_class   places     pre    test    inhib
                m_steady       new_decreasing))
      in
      stpn_class_fire_pre_aux
        whole_class  places    pre    test   inhib   m_steady
        tail
        (fired_pre_class ++ [t]) new_decreasing  new_chronos
    else  (* not enabled  w.r.t. the other transs OR not goog time*)
      stpn_class_fire_pre_aux
        whole_class   places    pre    test   inhib   m_steady
        tail
        fired_pre_class          m_decreasing   chronos
  | []  => (fired_pre_class, m_decreasing, chronos)
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
Print spn_class_fire_pre_aux. Print spn_class_fire_pre_aux_spec. 
Inductive stpn_class_fire_pre_aux_spec
          (whole_class : list trans_type)
          (places : list place_type)
          (pre   test   inhib : weight_type)  
          (m_steady     : marking_type)
  : (list trans_type)                   ->     (* class *)
    (list trans_type)                   ->  (* subclass_fired_pre *)
    marking_type                        ->  (* m_decreasing *)
    (trans_type -> option chrono_type)  ->  (* chronos *)
    
      
    (list trans_type)           ->   (* subclass_fired_pre *)
    marking_type                       ->   (* m_decreasing *)
    (trans_type -> option chrono_type)    ->  (* chronos *)
    Prop :=
| class_nil : forall
    (m_decreased : marking_type)
    (subclass_fired_pre : list trans_type)
    (chronos : trans_type -> option chrono_type),
    stpn_class_fire_pre_aux_spec
      whole_class    places   pre  test  inhib  m_steady
      []
      subclass_fired_pre   m_decreased     chronos
      subclass_fired_pre   m_decreased     chronos
| class_cons_if :  forall
    (t : trans_type)
    (tail    subclass_fired_pre  sub : list trans_type)
    (m_decreasing_low  m_decreasing_high  m : marking_type)
    (chronos  new_chronos   chronos_final : trans_type -> option chrono_type),
    synchro_check_arcs
      places    (pre t) (test t) (inhib t)
      m_steady  m_decreasing_high
    = true   /\     time_check (chronos  t) = true
    -> 
    m_decreasing_low = (update_marking_pre
                          t   pre   m_decreasing_high  places)
    ->
     new_chronos =
     (reset_time_disabled
        chronos
        (not_synchro_check_list
           whole_class   places     pre    test    inhib
           m_steady       m_decreasing_low))
    ->    
    stpn_class_fire_pre_aux_spec
      whole_class     places      pre  test  inhib   m_steady
      tail
      (subclass_fired_pre ++ [t])  m_decreasing_low    new_chronos
      sub                          m                  chronos_final
    ->
    stpn_class_fire_pre_aux_spec
      whole_class     places     pre  test  inhib    m_steady
      (t::tail)
      subclass_fired_pre   m_decreasing_high    chronos
      sub                  m                  chronos_final
| class_cons_else :  forall
    (t : trans_type)
    (tail   subclass_half_fired   sub : list trans_type)
    (m_decreasing   m : marking_type)
    (chronos     chronos_final : trans_type -> option chrono_type),
    synchro_check_arcs
      places    (pre t) (test t) (inhib t)
      m_steady  m_decreasing
    = false   \/     time_check (chronos  t) = false
    ->
    stpn_class_fire_pre_aux_spec
      whole_class     places      pre  test  inhib   m_steady
      tail
      subclass_half_fired  m_decreasing          chronos
      sub                   m                 chronos_final
    ->
    stpn_class_fire_pre_aux_spec
      whole_class     places      pre  test  inhib   m_steady
      (t::tail)
      subclass_half_fired  m_decreasing          chronos
      sub                  m   chronos_final.

Functional Scheme stpn_class_fire_pre_aux_ind :=
  Induction for stpn_class_fire_pre_aux   Sort Prop.

Theorem stpn_class_fire_pre_aux_correct : forall
    (whole_class : list trans_type)
    (places : list place_type)
    (pre  test  inhib : weight_type)
    (m_steady      m_decreasing      m_final : marking_type)
    (class_transs  fired_pre_class  sub_final : list trans_type)
    (chronos chronos_final : trans_type -> option chrono_type),
    stpn_class_fire_pre_aux
      whole_class     places    pre   test   inhib  m_steady
      class_transs
      fired_pre_class   m_decreasing    chronos  
    = (sub_final,          m_final,        chronos_final)
    ->
    stpn_class_fire_pre_aux_spec
      whole_class     places     pre   test  inhib  m_steady
      class_transs
      fired_pre_class   m_decreasing    chronos
      sub_final            m_final         chronos_final.
Proof.
  intros whole_class  places  pre test inhib  m_steady
         m_decreasing  m_final
         class_transs   fired_pre_class    sub_final
         chronos  chronos_final.
  functional induction 
             (stpn_class_fire_pre_aux
                whole_class places  pre test inhib  m_steady   
                class_transs
                fired_pre_class  m_decreasing    chronos)
             using stpn_class_fire_pre_aux_ind.
  - intro H. inversion H. apply class_nil.
  - intro H.
    apply class_cons_if
      with (m_decreasing_low := (update_marking_pre
                                   t pre m_decreasing  places ))
           (new_chronos :=
              (reset_time_disabled
                 chronos
                 (not_synchro_check_list
                    whole_class   places     pre    test    inhib
                    m_steady    (update_marking_pre
                                   t pre m_decreasing  places)))).
    + apply andb_prop. assumption. 
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
      whole_class      places     pre test inhib   m_steady
      class_transs
      subclass_fired_pre    m_decreasing        chronos
      sub_final             m_final             chronos_final
    ->
    stpn_class_fire_pre_aux
      whole_class      places     pre test inhib   m_steady
      class_transs
      subclass_fired_pre    m_decreasing    chronos 
    = (sub_final ,          m_final,        chronos_final).
Proof.
  intros whole_class places pre test inhib m_steady
         m_decreasing m_final class_transs fired_pre_class
         sub_final  chronos chronos_final Hspec. elim Hspec.
  - simpl. reflexivity.
  - intros  t tail fired_pre_class0 sub
            m_decreasing_low m_decreasing_high m
            chronos0 new_chronos  chronos_final0
            Hsynchro  Hlow Hnew  Htailspec Htail.
    simpl.
    assert (Hsynchro' : synchro_check_arcs
                          places (pre t) (test t) 
                          (inhib t) m_steady m_decreasing_high &&
                          time_check (chronos0 t) = true).
      { apply andb_true_iff. assumption. }  rewrite Hsynchro'.
      rewrite <- Hlow. rewrite <- Hnew. rewrite Htail.
      reflexivity.
  - intros  t tail fired_pre_class0 sub
            m_decreasing0  m
            chronos0   chronos_final0
            Hsynchro   Htailspec Htail. simpl.
    assert (Hsynchro' : synchro_check_arcs
                          places (pre t) (test t) 
                          (inhib t) m_steady m_decreasing0 &&
                          time_check (chronos0 t) = false).
      { apply andb_false_iff. assumption. } 
    rewrite Hsynchro'. rewrite Htail.  reflexivity. 
Qed.

(* filling subclass_half_fired  ...  *)
Print spn_class_fire_pre_aux.
Definition stpn_class_fire_pre
           (places : list place_type)
           (pre    test    inhib : weight_type) 
           (m_steady   : marking_type)
           (class_transs : list trans_type)
           (m_decreasing : marking_type) 
           (chronos : trans_type -> option chrono_type)
  : (list trans_type) *
    marking_type      *
    (trans_type -> option chrono_type) :=
  stpn_class_fire_pre_aux
    class_transs   places    pre    test    inhib   m_steady
    class_transs   []
    m_decreasing   chronos.

Inductive stpn_class_fire_pre_spec
          (places : list place_type)
          (pre   test   inhib : weight_type)  
          (m_steady    : marking_type)
          (class_transs : list trans_type)
          (m_decreasing    : marking_type)
          (chronos  :  trans_type -> option chrono_type)
  : (list trans_type)                     ->
    marking_type                          ->
    (trans_type -> option chrono_type)    ->
    Prop :=
| stpn_sub_fire_pre_mk :
    forall (fired_pre_class : list trans_type)
           (m_fired_pre_class : marking_type)
           (chronos_final: trans_type -> option chrono_type),
      stpn_class_fire_pre_aux
        class_transs     places    pre    test    inhib m_steady
        class_transs     []
        m_decreasing     chronos
      = (fired_pre_class, m_fired_pre_class, chronos_final)
      ->
      stpn_class_fire_pre_spec
        places          pre  test  inhib        m_steady
        class_transs
        m_decreasing        chronos
        fired_pre_class  m_fired_pre_class  chronos_final
.

Functional Scheme stpn_class_fire_pre_ind :=
  Induction for stpn_class_fire_pre   Sort Prop.
Theorem stpn_class_fire_pre_correct : forall
    (places : list place_type)
    (pre  test  inhib : weight_type)
    (m_steady   m_decreasing     m_decreased : marking_type)
    (class_transs    fired_pre_class  : list trans_type)
    (chronos chronos_final: trans_type -> option chrono_type),
    stpn_class_fire_pre
      places    pre    test    inhib     m_steady
      class_transs
      m_decreasing         chronos     
    = (fired_pre_class, m_decreased, chronos_final)
    ->
    stpn_class_fire_pre_spec
      places          pre  test  inhib    m_steady
      class_transs
      m_decreasing        chronos 
      fired_pre_class  m_decreased  chronos_final.
Proof.
  intros places pre test inhib m_steady m_decreasing m_decreased
         class_transs  fired_pre_class chronos chronos_final H.
  functional induction (stpn_class_fire_pre
                          places    pre test inhib  m_steady
                          class_transs
                          m_decreasing   chronos)
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
      places          pre  test  inhib     m_steady
      class_transs
      m_decreasing        chronos 
      subclass_fired_pre  m_decreased  chronos_final
    -> 
    stpn_class_fire_pre
      places    pre    test    inhib       m_steady
      class_transs
      m_decreasing         chronos
    = (subclass_fired_pre, m_decreased, chronos_final).
Proof.
  intros  places pre test inhib m_steady m_decreasing m_decreased
          class_transs  fired_pre_class chronos chronos_final H.
  elim H.
  intros. unfold stpn_class_fire_pre. assumption.
Qed.

(**************************************************************)
(*********************  stpn_fire_pre 
 apply stpn_class_fire_pre over ALL classes of transitions. 
 Begin with initial marking, 
  end with                          half fired marking.  
 "classes_half_fired" is meant to be empty at first   *)

Print spn_fire_pre_aux.
Fixpoint stpn_fire_pre_aux
         (places : list place_type)
         (pre test inhib : weight_type)
         (m_steady   : marking_type)
         (classes   fired_pre_classes : list (list trans_type))
         (m_decreasing : marking_type)
         (chronos : trans_type -> option chrono_type)
  : (list (list trans_type)) *
    marking_type *
    (trans_type -> option chrono_type)  :=
  match classes with
  | [] => (fired_pre_classes , m_decreasing, chronos)
  | class :: Ltail => let '(sub_l, new_m, new_chronos) :=
                          stpn_class_fire_pre
                            places  pre   test  inhib  m_steady
                            class
                                   m_decreasing  chronos
                      in  stpn_fire_pre_aux
                            places   pre  test  inhib  m_steady
                            Ltail
                            (sub_l::
                                  fired_pre_classes) new_m new_chronos        
  end.

Inductive stpn_fire_pre_aux_spec
          (places : list place_type)
          (pre test inhib : weight_type)
          (m_steady  : marking_type)
  : list (list trans_type)               ->  (* classes   *)
    list (list trans_type)               ->  (* fired_pre_classes *)
    marking_type                         ->  (* m_decreasing *)
    (trans_type -> option chrono_type)     ->     (* chronos *)

    list (list trans_type)          ->  (* fired_pre_classes *)
    marking_type                       ->  (* m_decreasing *)
    (trans_type -> option chrono_type)     ->     (* chronos *)
    Prop :=
| classes_nil : forall (fired_pre_classes : list (list trans_type))
                       (m_decreased : marking_type)
                       (chronos : trans_type -> option chrono_type),
    stpn_fire_pre_aux_spec
      places           pre   test  inhib   m_steady
      []
      fired_pre_classes    m_decreased          chronos 
      fired_pre_classes    m_decreased          chronos
| classes_cons : forall
    (classes_tail classes_fired_pre_tail C : list (list trans_type))
    (class     class_fired_pre : list trans_type)
    (m_decreased   m_decreasing  m_any  : marking_type)
    (chronos   chronos_fin  any_chronos : trans_type ->
                                            option chrono_type),
    stpn_class_fire_pre
      places          pre    test    inhib    m_steady
      class
                        m_decreasing chronos
    = (class_fired_pre, m_decreased, chronos_fin)
    ->
    stpn_fire_pre_aux_spec
      places          pre    test    inhib    m_steady
      classes_tail
      (class_fired_pre::
                      classes_fired_pre_tail) m_decreased chronos_fin
      C     m_any    any_chronos
    ->
    stpn_fire_pre_aux_spec
      places          pre   test   inhib   m_steady
      (class::
            classes_tail)
      classes_fired_pre_tail   m_decreasing    chronos
      C                        m_any          any_chronos.

Functional Scheme stpn_fire_pre_aux_ind :=
  Induction for stpn_fire_pre_aux   Sort Prop.

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

Theorem stpn_fire_pre_aux_correct : forall
    (places : list place_type)
    (pre   test  inhib : weight_type)
    (m_steady  m_decreasing  m_decreased : marking_type)
    (classes_transs   fired_pre_classes_rec
                      fired_pre_classes : list (list trans_type))
    (chronos   chronos_final  : trans_type -> option chrono_type),
    stpn_fire_pre_aux
      places       pre   test  inhib  m_steady
      classes_transs
      fired_pre_classes_rec  m_decreasing  chronos    
    = (fired_pre_classes,    m_decreased,  chronos_final)
    ->
    stpn_fire_pre_aux_spec
      places       pre   test  inhib  m_steady
      classes_transs
      fired_pre_classes_rec  m_decreasing   chronos
      fired_pre_classes      m_decreased    chronos_final.
Proof.
  intros places  pre test inhib m_steady m_decreasing m_decreased
         classes_transs  fired_pre_classes_rec   fired_pre_classes
         chronos chronos_final.
  functional induction
             (stpn_fire_pre_aux
                places pre test inhib m_steady
                classes_transs
                fired_pre_classes_rec  m_decreasing   chronos)
             using stpn_fire_pre_aux_ind.
  - intro Heq. inversion Heq. apply classes_nil.
  - intro H.
    apply classes_cons
      with (class_fired_pre :=
              premz (stpn_class_fire_pre
                       places   pre   test   inhib   m_steady
                       class
                       m_decreasing  chronos))
           (m_decreased :=
              deuz (stpn_class_fire_pre
                      places    pre   test   inhib   m_steady
                      class
                      m_decreasing  chronos))
           (chronos_fin :=
              troiz (stpn_class_fire_pre
                       places pre test inhib  m_steady
                       class
                       m_decreasing  chronos)).
    + rewrite e0. simpl. reflexivity.
    + rewrite e0. simpl.  apply (IHp H).
Qed.

Theorem stpn_fire_pre_aux_complete : forall
    (places : list place_type)
    (pre   test  inhib : weight_type)
    (m_steady  m_decreasing  m_decreased : marking_type)
    (classes_transs   classes_fired_pre_rec
                      classes_fired_pre : list (list trans_type))
    (chronos   chronos_final  : trans_type -> option chrono_type),
    stpn_fire_pre_aux_spec
      places          pre   test   inhib  m_steady
      classes_transs
      classes_fired_pre_rec  m_decreasing   chronos   
      classes_fired_pre      m_decreased    chronos_final
    ->
    stpn_fire_pre_aux
      places          pre   test  inhib   m_steady
      classes_transs
      classes_fired_pre_rec  m_decreasing   chronos
    = (classes_fired_pre,    m_decreased,   chronos_final).    
Proof.
  intros  places pre test inhib  m_steady m_decreasing m_decreased
          classes_transs classes_fired_pre_rec  classes_fired_pre 
          chronos  chronos_final  H. elim H.
  - intros. simpl. reflexivity.
  - intros classes_tail classes_fired_pre_tail
           C  class  class_fired_pre
           m_decreased0   m_decreasing0    m_any
           chronos0     chronos_fin     any_chronos
           Heq   Hspectail   Htail.
    simpl. rewrite Heq. rewrite <- Htail. reflexivity. 
Qed.

Print spn_fire_pre. 
Definition stpn_fire_pre
         (places : list place_type)
         (pre test inhib : weight_type)
         (m_steady : marking_type)
         (classes_transs  : list (list trans_type))
         (chronos : trans_type -> option chrono_type)
  : (list (list trans_type)) *
    marking_type             *
    (trans_type -> option chrono_type)  :=
  stpn_fire_pre_aux
    places    pre test inhib  m_steady
    classes_transs
    []  m_steady   chronos.
Inductive stpn_fire_pre_spec
         (places : list place_type)
         (pre test inhib : weight_type)
         (m_steady : marking_type)
         (classes_transs  : list (list trans_type))
         (chronos : trans_type -> option chrono_type)
  : (list (list trans_type)) ->
    marking_type ->
    (trans_type -> option chrono_type)   ->
    Prop :=
| spn_fire_pre_mk :
    forall (classes_fired_pre : list (list trans_type))
           (m_inter : marking_type)
           (chronos_next  : trans_type ->   option chrono_type),
      stpn_fire_pre_aux
        places      pre    test    inhib  m_steady
        classes_transs
        []                 m_steady   chronos
      = (classes_fired_pre, m_inter,  chronos_next)
      ->
      stpn_fire_pre_spec
        places      pre     test   inhib   m_steady
        classes_transs                 chronos
        classes_fired_pre   m_inter    chronos_next.

Functional Scheme stpn_fire_pre_ind :=
  Induction for stpn_fire_pre   Sort Prop.
Theorem stpn_fire_pre_correct :  forall
    (places : list place_type)
    (pre   test  inhib : weight_type)
    (m_steady  m_decreased : marking_type)
    (classes_transs  classes_fired_pre : list (list trans_type))
    (chronos   chronos_final  : trans_type -> option chrono_type),
    stpn_fire_pre
      places       pre   test  inhib  m_steady            
      classes_transs                   chronos
    = (classes_fired_pre, m_decreased, chronos_final)
    ->
    stpn_fire_pre_spec
      places       pre   test  inhib  m_steady            
      classes_transs                    chronos
      classes_fired_pre    m_decreased   chronos_final.
Proof.
  intros places  pre test inhib m_steady m_decreased
         classes_transs classes_fired_pre
         chronos chronos_final.
  functional induction (stpn_fire_pre
                          places pre test inhib  m_steady
                          classes_transs   chronos)
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
      places       pre   test   inhib  m_steady            
      classes_transs                     chronos
      classes_fired_pre    m_decreased   chronos_final
    ->
    stpn_fire_pre
      places        pre   test  inhib  m_steady            
      classes_transs                   chronos
    = (classes_fired_pre, m_decreased, chronos_final).
Proof.
  intros  places pre test  inhib m_steady
          m_decreased classes_transs classes_fired_pre
          chronos  chronos_final H. elim H.
  intros  classes_fired_pre0 m_inter chronos_next  Heq.
  unfold stpn_fire_pre. assumption.
Qed.

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
  let '(sub_Lol, m_inter, new_chronos ) :=
      (stpn_fire_pre
         places   pre   test  inhib  marking
         classes_transs   chronos)
  in
  (sub_Lol, marking2list
              m_inter   places ,
  intervals2list
    new_chronos   transs).

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
           (m_steady : marking_type)
           (classes_transs : list (list trans_type))
           (chronos : trans_type -> option chrono_type)
  : (list (list trans_type)) *
    marking_type             *
    (trans_type -> option chrono_type)  :=
  let '(sub_Lol, m_inter, new_chronos) :=
      stpn_fire_pre
        places    pre  test  inhib    m_steady
        classes_transs   chronos
  in  (sub_Lol ,
       fire_post
         places     post
         m_inter     sub_Lol ,
       new_chronos ).

Inductive stpn_fire_spec   
          (places : list place_type)
          (pre test inhib post : weight_type)
          (m_steady : marking_type)
          (classes_transs : list (list trans_type))
          (chronos : trans_type -> option chrono_type)
  : (list (list trans_type))   ->
    marking_type               ->
    (trans_type -> option chrono_type)    ->
    Prop :=
| stpn_fire_mk :  forall
    (sub_Lol : list (list trans_type))
    (m_inter   m  : marking_type)
    (new_chronos : trans_type -> option chrono_type),
    (sub_Lol, m_inter, new_chronos) = stpn_fire_pre
                                        places pre test inhib m_steady
                                        classes_transs chronos
    ->
    m = fire_post
          places post   m_inter  sub_Lol
    ->
    stpn_fire_spec   
      places         pre test inhib post      m_steady
      classes_transs   chronos
      sub_Lol    m   new_chronos.

Functional Scheme stpn_fire_ind :=
  Induction for  stpn_fire   Sort Prop.
Theorem stpn_fire_correct : forall
    (places : list place_type)
    (pre test inhib post : weight_type)
    (m_steady  m_next: marking_type)
    (chronos  next_chronos : trans_type -> option chrono_type)
    (classes_transs   sub_Lol: list (list trans_type)),
    stpn_fire
      places   pre  test  inhib  post  m_steady
      classes_transs      chronos  
    =  (sub_Lol, m_next, next_chronos)
    ->
    stpn_fire_spec
      places   pre  test  inhib  post   m_steady
      classes_transs      chronos
      sub_Lol  m_next next_chronos.
Proof.
  intros places  pre  test  inhib  post  m_steady  m_next
         chronos  next_chronos classes_transs sub_Lol.
  functional induction (stpn_fire
                          places pre test inhib post  m_steady
                          classes_transs  chronos)
             using stpn_fire_ind.
  intro Heq. inversion Heq. 
  apply stpn_fire_mk with (m_inter := m_inter).
  - rewrite e. rewrite H0. rewrite H2.  reflexivity.
  - reflexivity.  
Qed.
Theorem stpn_fire_complete : forall
    (places : list place_type)
    (pre test inhib post : weight_type)
    (m_steady  m_next: marking_type)
    (chronos  next_chronos : trans_type -> option chrono_type)
    (classes_transs   sub_Lol: list (list trans_type)),
    stpn_fire_spec
      places   pre  test  inhib  post   m_steady
      classes_transs     chronos  
      sub_Lol  m_next next_chronos
    ->
    stpn_fire
      places   pre  test  inhib  post   m_steady
      classes_transs     chronos
    =  (sub_Lol, m_next, next_chronos).
Proof.
  intros places pre test inhib post  m_steady  m_next chronos
         next_chronos  classes_transs sub_Lol H. elim H.
  intros sub_Lol0  m_inter  m  new_chronos  Hpre   Hpost.
  unfold stpn_fire. rewrite <- Hpre. rewrite Hpost. reflexivity.
Qed.


(* The marking and the chronos are evolving,  
but we want to see also the      fired transitions    *)
(******************************* CYCLE **********************)
Print spn_cycle. Print STPN. Print SPN.
Definition stpn_cycle (stpn : STPN)           
  : (list (list trans_type)) * STPN  :=
  match stpn with
  | mk_STPN
      (mk_SPN
         places  transs
         (* nodup_places  nodup_transitions *)
         pre     post    test          inhib         
         marking         (mk_prior
                            Lol) )
      chronos
    =>
    let enabled := list_enabled_spn
                     (mk_SPN
                        places  transs
                        (* nodup_places  nodup_transitions *)  
                        pre     post    test   inhib   marking
                        (mk_prior
                           Lol) )                         in
    let chronos_incr := increment_time_enabled
                          chronos 
                          enabled                 in
    let '(transs_fired, next_m, next_chronos) :=
        stpn_fire  
          places     pre  test  inhib  post  marking
          Lol    chronos_incr
    in (transs_fired, 
        (mk_STPN
           (mk_SPN
              places  transs  (* nodup_places  nodup_transitions *)
              pre     post     test          inhib    next_m
              (mk_prior
                 Lol) )
           next_chronos))
  end.
About stpn_fire. 
Inductive stpn_cycle_spec
          (stpn : STPN) :
  list (list trans_type)    ->
  STPN                       ->
  Prop :=
| stpn_fired_mk : forall
    (sub_Lol  Lol: list (list trans_type))
    (next_m   m : marking_type)
    (spn : SPN)
    (next_stpn : STPN)
    (places : list place_type)
    (transs  enabled : list trans_type)
    (pre  post test inhib : weight_type)
    (chronos  chronos_incr next_chronos : trans_type
                                          -> option chrono_type),
    spn = mk_SPN
            places  transs  pre  post test inhib    m
            (mk_prior
               Lol)
    ->
    stpn = mk_STPN
                spn
                chronos
    ->
    enabled = list_enabled_spn
                spn
    ->
    chronos_incr = increment_time_enabled
                     chronos      enabled
    -> 
    (sub_Lol, next_m, next_chronos) =
    (stpn_fire
       places  pre  test  inhib  post   m
       Lol   chronos_incr )
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
Theorem stpn_cycle_correct :
  forall (stpn  next_stpn : STPN)
         (sub_Lol : list (list trans_type)),
    stpn_cycle
      stpn    =  (sub_Lol, next_stpn)
    ->
    stpn_cycle_spec
      stpn        sub_Lol  next_stpn.
Proof.
  intros  stpn  next_stpn  sub_Lol.
  functional induction (stpn_cycle stpn)
             using stpn_cycle_ind. 
  intro Heq. apply stpn_fired_mk
               with (Lol:=Lol) (next_m:=next_m) (m:=marking)
                 (places:=places) (transs:=transs)
                 (pre:=pre) (post:=post) (test:=test)
                 (inhib:=inhib) (chronos:=chronos)
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
                                 
                 (enabled := list_enabled_spn
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
                 (chronos_incr := increment_time_enabled
                                    chronos
                                    (list_enabled_spn
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
                    troiz (stpn_fire
                             places  pre  test  inhib  post marking
                             Lol (increment_time_enabled
                                    chronos
                                    (list_enabled_spn
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
                 )).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite e2. inversion Heq. simpl. reflexivity.
  - rewrite e2. simpl. inversion Heq. reflexivity.
Qed.
Theorem stpn_cycle_complete :
 forall (stpn  next_stpn : STPN)
        (sub_Lol : list (list trans_type)),
   stpn_cycle_spec
     stpn         sub_Lol  next_stpn
   ->
   stpn_cycle
      stpn    =  (sub_Lol, next_stpn).
Proof.
  intros  stpn next_stpn sub_Lol  H. elim H.
  intros sub_Lol0  Lol next_m  m  spn0 next_stpn0
         places  transs  enabled  pre post test  inhib 
         chronos    chronos_incr    next_chronos
         H0 H1 H2 H3 H4 H5.
  unfold stpn_cycle.
  rewrite  H1. rewrite H0. simpl.
  unfold list_enabled_spn in H2. rewrite H0 in H2. rewrite <- H2.
  rewrite <- H3. rewrite <- H4. rewrite H5. reflexivity. 
Qed.

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
  | O => [ ( [] , [] , []  ) ]
  | S n' =>  let (Lol_fired, next_stpn) := (stpn_cycle stpn)
             in
             ( Lol_fired ,
               (marking2list
                  (marking (spn  next_stpn))
                  (places (spn   next_stpn))) ,
               (intervals2list
                  (all_chronos   next_stpn)
                  (transs (spn   next_stpn))) ) 
               ::
               (stpn_animate
                  next_stpn
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
                   (marking (spn next_stpn))
                   (places (spn next_stpn))
      ->
      chronos_visuels = (intervals2list
                           (all_chronos   next_stpn)
                           (transs (spn  next_stpn)))
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
Theorem stpn_animate_correct :
  forall (stpn   : STPN)
         (n : nat)
         (triplets : list (list (list trans_type)  *
                           list (place_type * nat) *
                           list (trans_type * option (nat * nat * nat)))),
    stpn_animate
      stpn    n   =  triplets
    ->
    stpn_animate_spec
      stpn    n     triplets.
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
         (triplets : list (list (list trans_type)  *
                           list (place_type * nat) *
                           list (trans_type * option (nat * nat * nat)))),
    stpn_animate_spec
      stpn    n     triplets             ->
    stpn_animate
      stpn    n   =  triplets.
Proof.
  intros. elim H.
  - simpl. reflexivity. 
  - intros. simpl.
    rewrite <- H0. rewrite <- H1. rewrite <- H2. rewrite <- H4.
    reflexivity.
Qed. 