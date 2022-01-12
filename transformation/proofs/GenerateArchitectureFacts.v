(** * Facts about Architecture Generation *)

Require Import String.
Require Import common.CoqLib.
Require Import common.GlobalFacts.
Require Import common.StateAndErrorMonad.
Require Import common.ListLib.
Require Import common.proofs.StateAndErrorMonadTactics.
Require Import common.proofs.ListMonadFacts.
Require Import common.proofs.SetoidListFacts.

Require Import sitpn.SitpnLib.
Require Import sitpn.SitpnFacts.

Require Import hvhdl.Place.
Require Import hvhdl.AbstractSyntax.

Require Import transformation.Sitpn2HVhdl.
Require Import transformation.proofs.GenerateArchitectureInvs.

(** ** Facts about Place Map Generation *)

(* Section GenPMap. *)
  
(*   Lemma map_aux_gen_pmap_entry_P : *)
(*     forall {sitpn mm} {pls : list (P sitpn)} {pmap s pmap' s'}, *)
(*       map_aux (fun p => generate_place_map_entry p mm) pls pmap s = OK pmap' s' -> *)
(*       (forall p, InA P1SigEq p (pls ++ (fs pmap))) -> *)
(*       forall p, InA Peq p (fs pmap'). *)
(*   Proof. *)
(*     induction pls.  *)
(*     (* CASE pls = [] *) *)
(*     intros *; intros e; minv e; intros InA_app p. *)
(*     apply (InA_app p). *)
(*     (* CASE a :: pls *) *)
(*     intros *; intros e; minv e; intros InA_app p. *)
(*     eapply IHpls; eauto. *)
(*     unfold fs; rewrite fst_split_app; cbn. *)
(*     intros p1; specialize (InA_app p1). *)
(*     inversion_clear InA_app as [P1SigEq_ | InA_tl]. *)
(*     do 2 (erewrite InA_app_iff; right); eauto. *)
(*     rewrite app_assoc; erewrite InA_app_iff; left; eauto. *)
(*   Qed. *)

(*   Lemma map_aux_gen_pmap_entry_nodup_plmap : *)
(*     forall {sitpn mm} {pls : list (P sitpn)} {pmap s pmap' s'}, *)
(*       map_aux (fun p => generate_place_map_entry p mm) pls pmap s = OK pmap' s' -> *)
(*       NoDupA Peq (pls ++ (fs pmap)) -> *)
(*       NoDupA Peq (fs pmap'). *)
(*   Proof. *)
(*     induction pls.  *)
(*     (* CASE pls = [] *) *)
(*     intros *; intros e; minv e; auto. *)
(*     (* CASE a :: pls *) *)
(*     intros *; intros e; minv e; intros NoDupA_. *)
(*     eapply IHpls; eauto. *)
(*     unfold fs; rewrite fst_split_app; cbn. *)
(*     rewrite app_assoc; eapply NoDupA_app_comm; auto. *)
(*   Qed. *)
  
(*   Lemma gen_pmap_sil_plmap : *)
(*     forall {sitpn mm s v s'}, *)
(*       @generate_place_map sitpn mm s = OK v s' -> *)
(*       Sig_in_List (lofPs s) -> *)
(*       (forall p, ~InA Peq p (fs (plmap (arch s)))) -> *)
(*       NoDupA Peq (fs (plmap (arch s))) -> *)
(*       Sig_in_List (fs (plmap (arch s'))). *)
(*   Proof. *)
(*     intros *; intros e; minv e. *)
(*     unfold map in EQ1. *)
(*     intros SIL_lofps nIns_plmap NoDupA_plmap; split. *)
(*     eapply map_aux_gen_pmap_entry_P; eauto.     *)
(*     cbn; rewrite app_nil_r; eapply proj1; eapply SIL_lofps. *)
(*     eapply map_aux_gen_pmap_entry_nodup_plmap; eauto. *)
(*     cbn; rewrite app_nil_r; eapply proj2; eapply SIL_lofps. *)
(*   Qed. *)

(*   Lemma gen_pmap_entry_pcomp : *)
(*     forall {sitpn} {p : P sitpn} {mm s v s'}, *)
(*       generate_place_map_entry p mm s = OK v s' -> *)
(*       exists g i o, v = (p, (g, i, o)). *)
(*   Proof. intros *; intros e; minv e; eauto. Qed. *)
  
(*   Lemma map_aux_gen_pmap_entry_pcomp : *)
(*     forall {sitpn mm} {pls : list (P sitpn)} {pmap s pmap' s'}, *)
(*       map_aux (fun p => generate_place_map_entry p mm) pls pmap s = OK pmap' s' -> *)
(*       forall p, InA Peq p pls -> exists g i o, InA Pkeq (p, (g, i, o)) pmap'. *)
(*   Proof. *)
(*     induction pls.  *)
(*     (* BASE CASE *) *)
(*     - inversion 2. *)

(*     (* IND. CASE *) *)
(*     - intros *; intros e p InA_pls; *)
(*         inversion_clear InA_pls as [ e1 e2 Peq_pa | e1 e2 InA_ntl ]; *)
(*         monadInv e. *)
      
(*       (* CASE [Peq p a] *) *)
(*       + edestruct (gen_pmap_entry_pcomp EQ) as (g, (i, (o, eq_x))). *)
(*         rewrite eq_x in EQ0. *)
(*         exists g, i, o; eapply map_aux_inv_acc; eauto with setoidl. *)
(*         rewrite InA_app_iff; right; eauto. *)
        
(*       (* CASE [InA Peq p pls] *) *)
(*       + eapply IHpls; eauto. *)
(*   Qed. *)
    
(*   Lemma gen_pmap_pcomp :  *)
(*     forall {sitpn mm s v s'}, *)
(*       @generate_place_map sitpn mm s = OK v s' -> *)
(*       Sig_in_List (lofPs s) -> *)
(*       forall p, exists g i o, *)
(*           InA Pkeq (p, (g, i, o)) (plmap (arch s')). *)
(*   Proof. *)
(*     intros *; intros e; minv e. *)
(*     unfold map in EQ1; intros SIL_lofps p. *)
(*     eapply map_aux_gen_pmap_entry_pcomp; eauto. *)
(*     eapply ((proj1 SIL_lofps) p). *)
(*   Qed. *)

(*   Lemma gen_pmap_entry_bind_init_marking : *)
(*     forall {sitpn} {p : P sitpn} {mm s g i o s'}, *)
(*       generate_place_map_entry p mm s = OK (p, (g, i, o)) s' -> *)
(*       List.In (initial_marking, inl (e_nat (M0 p))) i. *)
(*   Proof. intros *; intros e; minv e; eauto. Qed. *)
  
(*   Lemma map_aux_gen_pmap_entry_bind_init_marking : *)
(*     forall {sitpn mm} {pls : list (P sitpn)} {pmap s pmap' s'}, *)
(*       map_aux (fun p => generate_place_map_entry p mm) pls pmap s = OK pmap' s' -> *)
(*       IsWellDefined sitpn -> *)
(*       (forall p g i o, InA Pkeq (p, (g, i, o)) pmap -> *)
(*                        List.In (initial_marking, inl (e_nat (M0 p))) i) -> *)
(*       forall p g i o, *)
(*         InA Pkeq (p, (g, i, o)) pmap' -> *)
(*         List.In (initial_marking, inl (e_nat (M0 p))) i. *)
(*   Proof. *)
(*     induction pls.  *)
(*     (* BASE CASE *) *)
(*     - intros *; intros e; minv e; auto. *)

(*     (* IND. CASE *) *)
(*     - intros *; intros e IWD InA_pmap_In; monadInv e. *)
(*       edestruct (gen_pmap_entry_pcomp EQ) as (g, (i, (o, eq_x))). *)
(*       rewrite eq_x in EQ0, EQ; clear eq_x. *)
(*       eapply IHpls; eauto. *)
(*       intros *; rewrite InA_app_iff. *)
(*       inversion_clear 1 as [ InA_pmap | InA_tl]. *)
(*       eapply InA_pmap_In; eauto. *)
(*       inversion_clear InA_tl as [ y l (Peq_, eq_) | y l InA_nil]; *)
(*         [ inject_left eq_; cbn in Peq_; *)
(*           rewrite ((wi_M0 (wi_funs IWD)) p a Peq_); *)
(*           eapply gen_pmap_entry_bind_init_marking; eauto *)
(*           | inversion InA_nil ]. *)
(*   Qed. *)
  
(*   Lemma gen_pmap_bind_init_marking : *)
(*     forall {sitpn mm s v s'}, *)
(*       @generate_place_map sitpn mm s = OK v s' -> *)
(*       IsWellDefined sitpn -> *)
(*       forall p g i o, *)
(*         InA Pkeq (p, (g, i, o)) (plmap (arch s')) -> *)
(*         List.In (initial_marking, inl (e_nat (M0 p))) i. *)
(*   Proof. *)
(*     intros *; intros e; minv e. *)
(*     unfold map in EQ1; intros IWD; intros *. *)
(*     eapply map_aux_gen_pmap_entry_bind_init_marking; eauto. *)
(*     inversion 1. *)
(*   Qed. *)
  
(* End GenPMap. *)

(** ** Facts about Transition Map Generation *)

Section GenTMap.
  
End GenTMap.

(** ** Facts about Interconnection Generation *)

(* Section GenInterconn. *)
  
(*   Lemma interconnect_p_pcomp : *)
(*     forall {sitpn p s v s'}, *)
(*       @interconnect_p sitpn p s = OK v s' -> *)
(*       exists g i o, InA Pkeq (p, (g, i, o)) (plmap (arch s')). *)
(*   Proof. *)
(*     intros until s'; intros e; minv e. *)
(*     destruct x2 as ((g1, i1), o1). *)
(*     exists g1, i1, o1; eauto with setoidl. *)
(*   Qed. *)
  
(*   Lemma iter_interconnect_p_pcomp : *)
(*     forall {sitpn pls s v s'}, *)
(*       iter (@interconnect_p sitpn) pls s = OK v s' -> *)
(*       NoDupA Peq pls -> *)
(*       forall p, *)
(*         InA Peq p pls -> *)
(*         exists g i o, InA Pkeq (p, (g, i, o)) (plmap (arch s')). *)
(*   Proof. *)
(*     intros until pls; *)
(*       functional induction (iter (@interconnect_p sitpn) pls) using iter_ind. *)

(*     (* BASE CASE *) *)
(*     - inversion 3. *)

(*     (* IND. CASE *) *)
(*     - intros *; intros e NoDupA_pls p InA_pls; *)
(*         inversion_clear InA_pls as [ e1 e2 Peq_pb | e1 e2 InA_ntl ]; *)
(*         monadInv e. *)

(*       (* CASE a = n *) *)
(*       + edestruct (interconnect_p_pcomp EQ0) as (g, (i, (o, InA_plmap))). *)
(*         exists g, i, o; symmetry in Peq_pb; eauto with setoidl. *)

(*       (* CASE n ∈ tl *) *)
(*       + eapply interconnect_p_inv_pcomp; eauto. *)
(*         eapply IHm; eauto. *)
(*         lazymatch goal with *)
(*         | [ H: NoDupA _ _ |- _ ] => inversion_clear H; auto *)
(*         end. *)
(*   Qed. *)
  
(*   Lemma gen_interconnections_pcomp :  *)
(*     forall {sitpn s v s'}, *)
(*       @generate_interconnections sitpn s = OK v s' -> *)
(*       Sig_in_List (lofPs s) -> *)
(*       forall p, exists g i o, *)
(*           InA Pkeq (p, (g, i, o)) (plmap (arch s')). *)
(*   Proof. *)
(*     intros *; intros e; minv e. *)
(*     inversion 1; intros; eapply iter_interconnect_p_pcomp; eauto.     *)
(*   Qed. *)
  
(* End GenInterconn. *)

(** ** Facts about Architecture Generation Function *)

(* Lemma gen_arch_pcomp :  *)
(*   forall {sitpn mm s v s'}, *)
(*     @generate_architecture sitpn mm s = OK v s' -> *)
(*     Sig_in_List (lofPs s) -> *)
(*     forall p, exists g i o, *)
(*         InA Pkeq (p, (g, i, o)) (plmap (arch s')). *)
(* Proof. *)
(*   intros until s'; intros e; monadInv e. *)
(*   erewrite gen_pmap_inv_lofPs; eauto. *)
(*   erewrite gen_tmap_inv_lofPs; eauto. *)
(*   eapply gen_interconnections_pcomp; eauto. *)
(* Qed. *)

(* Lemma gen_arch_sil_plmap :  *)
(*   forall {sitpn mm s v s'}, *)
(*     @generate_architecture sitpn mm s = OK v s' -> *)
(*     Sig_in_List (lofPs s) -> *)
(*     (forall p, ~InA Peq p (fs (plmap (arch s)))) -> *)
(*     NoDupA Peq (fs (plmap (arch s))) -> *)
(*     Sig_in_List (fs (plmap (arch s'))). *)
(* Proof. *)
(*   intros *; intros e; monadInv e. *)
(*   intros SIL_lofps nInA_plmap NoDupA_plmap. *)
(*   eapply gen_interconnections_inv_sil_plmap; eauto. *)
(*   erewrite <- gen_tmap_inv_plmap; eauto. *)
(*   eapply gen_pmap_sil_plmap; eauto. *)
(* Qed. *)

(* Lemma gen_arch_bind_init_marking :  *)
(*   forall {sitpn mm s v s'}, *)
(*     @generate_architecture sitpn mm s = OK v s' -> *)
(*     Sig_in_List (lofPs s) -> *)
(*     (forall p, ~InA Peq p (fs (plmap (arch s)))) -> *)
(*     IsWellDefined sitpn -> *)
(*     forall p g i o, *)
(*       InA Pkeq (p, (g, i, o)) (plmap (arch s')) -> *)
(*       List.In (initial_marking, inl (e_nat (M0 p))) i. *)
(* Proof. *)
(*   intros *; intros e; monadInv e. *)
(*   intros SIL_lofps nInA_plmap IWD; intros *; intros InA_plmap'. *)
(*   edestruct (@gen_pmap_pcomp sitpn) with (p := p) as (g1, (i1, (o1, InA_plmap0))); eauto. *)
(*   assert (In_initm_i1 : List.In (initial_marking, inl (e_nat (M0 p))) i1) *)
(*     by (eapply gen_pmap_bind_init_marking; eauto). *)
(*   rewrite (gen_tmap_inv_plmap EQ1) in InA_plmap0. *)
(*   eapply gen_interconnections_inv_pcomp_imap; eauto; *)
(*     ((rewrite <- (gen_tmap_inv_lofPs EQ1), <- (gen_pmap_inv_lofPs EQ); assumption) *)
(*      || (cbv; lia) || auto). *)
(* Admitted. *)

Lemma gen_tcis_p_comp_ex :
  forall (sitpn : Sitpn) (s : Sitpn2HVhdlState sitpn) v s' p,
    generate_tcis s = OK v s' ->
    (exists id__p g__p i__p o__p,
        InA Pkeq (p, id__p) (p2pcomp (γ s))
        /\ InCs (cs_comp id__p Petri.place_entid g__p i__p o__p) (beh s)) -> 
    (exists id__p g__p i__p o__p,
        InA Pkeq (p, id__p) (p2pcomp (γ s'))
        /\ InCs (cs_comp id__p Petri.place_entid g__p i__p o__p) (beh s')).
Admitted.

Remark iter_prop_A_state :
  forall {state A : Type} {f : A -> Mon unit} {l} (eqA : A -> A -> Prop) {s : state} {v s'}
         {Q : A -> state -> Prop},
    iter f l s = OK v s' ->
    (forall a b s, eqA a b -> Q a s <-> Q b s) ->
    (forall a s1 x s2, f a s1 = OK x s2 -> Q a s2) ->
    (forall a s1 x s2, f a s1 = OK x s2 -> forall b, Q b s1 -> Q b s2) ->
    forall a, InA eqA a l -> Q a s'.
Proof.
  intros until l; functional induction (iter f l) using iter_ind;
    intros eqA s v s' Q e; monadFullInv e; intros Qequiv Qprop Qinv.
  - inversion 1.
  - inversion_clear 1; [ erewrite Qequiv; eauto | (eapply Qinv; eauto; eapply IHm; eauto) ].
Qed.

Lemma SIL_forall_A :
  forall A P (l : list { x : A | P x }),
    Sig_in_List l -> forall a, InA P1SigEq a l.
Admitted.

Lemma gen_pci_p_comp_ex :
  forall sitpn (n : nat) (a : P sitpn) (s1 : Sitpn2HVhdlState sitpn) (x : unit) (s2 : Sitpn2HVhdlState sitpn),
    generate_pci a n s1 = OK x s2 ->
    exists id__p g__p i__p o__p,
      InA Pkeq (a, id__p) (p2pcomp (γ s2)) /\ InCs (cs_comp id__p Petri.place_entid g__p i__p o__p) (beh s2).
Proof.
  intros *; intros e; minv e.
  all: do 4 eexists; split; [ eauto with setoidl | left; eauto ].
Qed.  

Lemma p_comp_ex_Peq_equiv :
  forall sitpn (x y : P sitpn) s,
    Peq x y ->
    ((exists id__p g__p i__p o__p,
         InA Pkeq (x, id__p) (p2pcomp (γ s)) /\ InCs (cs_comp id__p Petri.place_entid g__p i__p o__p) (beh s))
     <-> (exists id__p g__p i__p o__p,
             InA Pkeq (y, id__p) (p2pcomp (γ s)) /\ InCs (cs_comp id__p Petri.place_entid g__p i__p o__p) (beh s))).
Proof.
  intros; split;
    (edestruct 1 as (id__p, (g__p, (i__p, (o__p, (InA_a, InCs_)))));
     exists id__p, g__p, i__p, o__p; split; [ eauto with setoidl | assumption ]).
Qed.

Lemma gen_pci_p_comp_ex_inv :
  forall sitpn (n : nat) (a : P sitpn) (s1 : Sitpn2HVhdlState sitpn) (x : unit) (s2 : Sitpn2HVhdlState sitpn),
    generate_pci a n s1 = OK x s2 ->
    forall b,
      (exists id__p g__p i__p o__p,
          InA Pkeq (b, id__p) (p2pcomp (γ s1)) /\ InCs (cs_comp id__p Petri.place_entid g__p i__p o__p) (beh s1)) ->
      exists id__p g__p i__p o__p,
        InA Pkeq (b, id__p) (p2pcomp (γ s2)) /\ InCs (cs_comp id__p Petri.place_entid g__p i__p o__p) (beh s2).
Proof.
  intros *; intros e b; destruct (Peqdec a b) as [Peq_ab | nPeq_ab]. 

  (* CASE [Peq a b], implies [Q a s' <-> Q b s']. *)
  - rewrite <- (p_comp_ex_Peq_equiv sitpn a b s1 Peq_ab).
    rewrite <- (p_comp_ex_Peq_equiv sitpn a b s2 Peq_ab).
    intro; eapply gen_pci_p_comp_ex; eauto.

  (* CASE [~Peq a b], then nevermind the new entry [(a, id__p)] and new
     PCI in [(beh s2)]. *)
  - minv e.
    all: try (edestruct 1 as (id__p, (g__p, (i__p, (o__p, (InA_a, InCs_)))));
              exists id__p, g__p, i__p, o__p; split; [
                 (erewrite <- (getv_inv_state EQ1); eauto 1 with setoidl)
               | (right; erewrite <- (getv_inv_state EQ1); assumption) ]).
Admitted.

Lemma gen_pcis_p_comp_ex :
  forall (sitpn : Sitpn) (b : P sitpn -> nat) (s : Sitpn2HVhdlState sitpn) v s' p,
    generate_pcis b s = OK v s' ->
    Sig_in_List (lofPs s) ->
    (exists id__p g__p i__p o__p,
        InA Pkeq (p, id__p) (p2pcomp (γ s'))
        /\ InCs (cs_comp id__p Petri.place_entid g__p i__p o__p) (beh s')).
Proof.
  intros *; intros e; minv e. intros SIL_lofPs.
  pattern p, s'.
  eapply iter_prop_A_state with (eqA := Peq); eauto.

  (* Proves that [Peq a b] implies [Q a s' <-> Q b s']. *)
  - eapply p_comp_ex_Peq_equiv.
    
  (* Proves that [∀ a, f a s = OK v s' -> Q a s'] where [f] 
     is [generate_pci] here. *)
  - cbn; intros x; eapply gen_pci_p_comp_ex.
    
  (* Proves that property [Q] is invariant. *)
  - simpl; intros x; eapply gen_pci_p_comp_ex_inv with (n := b x).

  (* Proves that *)
  - eapply SIL_forall_A; eauto.
Qed.

Lemma gen_archi_p_comp_ex :
  forall (sitpn : Sitpn) (b : P sitpn -> nat) (s : Sitpn2HVhdlState sitpn) v s' p,
    generate_architecture b s = OK v s' ->
    Sig_in_List (lofPs s) ->
    (exists id__p g__p i__p o__p,
        InA Pkeq (p, id__p) (p2pcomp (γ s'))
        /\ InCs (cs_comp id__p Petri.place_entid g__p i__p o__p) (beh s')).
Proof.
  intros *; intros e; monadInv e; intros SIL_lofPs.
  eapply gen_tcis_p_comp_ex; eauto.
  eapply gen_pcis_p_comp_ex; eauto.
Qed.
