(** * Lemmas about Sitpn *)

Require Import Coqlib.
Require Import InAndNoDup.
Require Import Sitpn.
Require Import SitpnSemanticsDefs.
Require Import Fired.

(* All transitions of the top-priority list belong
   to the main list [lofT] or to the acc. list [tp]. *)

Lemma istplist_in_tp_or_T :
  forall (sitpn : Sitpn) lofT tp tp',
    @IsTopPriorityListAux sitpn lofT tp tp' ->
    forall t, List.In t tp' -> List.In t lofT \/ List.In t tp.
Proof.
  induction 1; intros t' Hin_tp'.

  (* BASE CASE, lofT = [] *)
  - firstorder.

  (* CASE, lofT = (_ :: _), and transitions are top-priority or not. *)
    
  - specialize (IHIsTopPriorityListAux t' Hin_tp');
      inversion_clear IHIsTopPriorityListAux;
      [ auto | destruct_in_app_or; [ auto | firstorder ] ].
  - specialize (IHIsTopPriorityListAux t' Hin_tp'); firstorder. 
Qed.

(* Transitions that are elected to be fired either come from
   the [tp] list or the acc. list [fired]. *)

Lemma electfired_in_fired_or_tp :
  forall sitpn s m fired tp m' fired',
    
    @ElectFired sitpn s m fired tp (m', fired') ->

    forall t, List.In t fired' -> List.In t fired \/ List.In t tp.
Proof.
  intros sitpn s m fired tp m' fired' Helect;
    dependent induction Helect;

    (* BASE CASE,  *)
    auto;

    (* 2 IND. CASES *)
    intros t' Hin_t'_fired';
    specialize (IHHelect m' fired' eq_refl t' Hin_t'_fired');
    inversion IHHelect;
    
    [
      (* CASE tp = (_ :: _) + election succeed *)
      destruct_in_app_or;
      [
        left; assumption |
        inversion IHHelect; [
          destruct_in_app_or; [ auto | firstorder ] |
          auto
        ]
      ] |
      auto |
      (* CASE tp = (_ :: _) + election does not succeed *)
      left; assumption |
      auto
    ].      
Qed.

(* Transitions in fset either come from the list [lofT] or
   from the acc. list [fired]. *)

Lemma isfiredlistaux_in_fired_or_T :
  forall sitpn s m fired lofT fset,
    
    @IsFiredListAux sitpn s m fired lofT fset ->

    forall t, List.In t fset -> List.In t fired \/ List.In t lofT.
Proof.
  intros sitpn s m fired lofT fset Hfired;
    dependent induction Hfired.

  (* BASE CASE, lofT = [] *)
  - auto.

  (* IND. CASE, lofT <> [] *)
  - intros t Hin_fired''.
    
    specialize (IHHfired t Hin_fired'') as Hw_in_fired'_inlofT'.
    lazymatch goal with
    | [ H: ElectFired _ _ _ _ _ |- _ ] =>
      specialize (electfired_in_fired_or_tp sitpn _ _ _ _ _ _ H t) as Hw_infired_intp
    end.

    (* 2 CASES: t ∈ fired' or t ∈ lofT' *)
    inversion_clear Hw_in_fired'_inlofT' as [Hin_t_fired' | Hin_t_lofT'].

    (* t ∈ fired' *)
    + specialize (Hw_infired_intp Hin_t_fired').

      (* t ∈ fired or t ∈ tp *)
      inversion_clear Hw_infired_intp as [Hin_t_fired | Hin_t_tp].
      
      (* t ∈ fired *)
      -- firstorder.

      (* t ∈ tp *)
      -- specialize (istplist_in_tp_or_T sitpn lofT [] tp H t Hin_t_tp) as Hw_inT_innil.
         inversion Hw_inT_innil; [ auto | contradiction ].

    (* t ∈ lofT' *)
    + firstorder.
Qed.

(* All transitions elected to be fired at state [s] are firable at
   state [s] *)

Lemma electfired_is_firable : 
  forall sitpn s m fired tp m' fired',

    (forall t, List.In t fired -> Firable s t) ->
    @ElectFired sitpn s m fired tp (m', fired') ->

    forall t, List.In t fired' -> Firable s t.
Proof.
  intros sitpn s m fired tp m' fired' Hfirable Helect;
    dependent induction Helect;

    (* BASE CASE *)
    auto;

    (* IND. CASES *)
    apply IHHelect with (m'0 := m') (fired'0 := fired'); intros;
      [
        (* CASE firable *)
        destruct_in_app_or;
        [ auto |
          lazymatch goal with
          | [ H: List.In ?a [?b] |- _ ] =>
            inversion H as [ Heq | ];
            [rewrite <- Heq; assumption | contradiction]
          end ] |
        reflexivity |

        (* CASE not firable *)
        auto |
        reflexivity
      ].  
Qed.
  
(* All transitions fired at state [s] are firable at state [s] *)

Lemma fired_aux_is_firable :
  forall sitpn s m fired lofT fset,

    (* All transitions of the acc. list fired are firable *)
    (forall t, List.In t fired -> Firable s t) ->
    
    (* t ∈ fired(s) *)
    @IsFiredListAux sitpn s m fired lofT fset ->

    forall t, List.In t fset -> Firable s t.
Proof.
  intros sitpn s m fired lofT fset Hfirable.
  induction 1.

  (* BASE CASE lofT = [] *)
  - auto.

  (* IND. CASE *)
  - lazymatch goal with
    | [ H: ElectFired _ _ _ _ _ |- _ ] =>
      apply (IHIsFiredListAux (electfired_is_firable sitpn s m fired tp m' fired' Hfirable H))
    end.
Qed.

Hint Resolve fired_aux_is_firable : core.

(* All transitions fired at state [s] are firable at state [s] *)

Lemma fired_is_firable :
  forall sitpn s fset,

    (* t ∈ fired(s) *)
    @IsFiredList sitpn s fset ->

    forall t, List.In t fset -> Firable s t.
Proof.
  intros sitpn s fset.
  inversion 1 as (lofT, Hfired_aux).
  assert (Hinnil : forall t, List.In t [] -> Firable s t) by contradiction.
  eauto.  
Qed.
