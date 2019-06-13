(* Import Sitpn material. *)

Require Import Hilecop.Sitpn.Sitpn.
Require Import Hilecop.Sitpn.SitpnTokenPlayer.
Require Import Hilecop.Sitpn.SitpnSemantics.

(* Import Sitpn tactics, and misc. lemmas. *)

Require Import Hilecop.Sitpn.SitpnTactics.
Require Import Hilecop.Utils.HilecopLemmas.


(** * Falling Edge Lemmas about Time-Related Semantics Rules. *)

Section SitpnFallingEdgeSameStructDItvals.

  (** [update_time_intervals] preserves the structure of
      [new_d_itvals ++ d_itvals] in the returned [d_itvals']. *)
  
  Lemma update_time_intervals_same_struct_ditvals :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (d_itvals : list (Trans * DynamicTimeInterval))
           (new_d_itvals : list (Trans * DynamicTimeInterval))
           (d_itvals' : list (Trans * DynamicTimeInterval)),
      update_time_intervals sitpn s d_itvals new_d_itvals = Some d_itvals' ->
      (fst (split (new_d_itvals ++ d_itvals))) = (fst (split d_itvals')).
  Proof.
    intros sitpn s d_itvals new_d_itvals;
      functional induction (update_time_intervals sitpn s d_itvals new_d_itvals)
                 using update_time_intervals_ind;
      intros d_itvals' Hfun;
      
      (* BASE CASE. *)
      ((injection Hfun as Heq_itvals; simpl; rewrite Heq_itvals; rewrite app_nil_r; reflexivity)
         
       (* GENERAL CASE *)
       || (specialize (IHo d_itvals' Hfun) as Heq_ditvals;
           rewrite fst_split_app in Heq_ditvals;
           rewrite fst_split_app in Heq_ditvals;
           simpl in Heq_ditvals;
           rewrite fst_split_app;
           rewrite fst_split_cons_app;
           simpl;
           rewrite <- app_assoc in Heq_ditvals;
           assumption)

       (* ERROR CASE *)
       || inversion Hfun).
  Qed.
  
  (** [sitpn_falling_edge] preserves the structure of the
      [d_intervals] in the returned state. *)
  
  Lemma sitpn_falling_edge_same_struct_ditvals :
    forall (sitpn : Sitpn)
           (s s' : SitpnState)
           (time_value : nat)
           (env : Condition -> nat -> bool),
      sitpn_falling_edge sitpn s time_value env = Some s' ->
      (fst (split (d_intervals s))) = (fst (split (d_intervals s'))).
  Proof.
    intros sitpn s s' time_value env Hfun.
    functional induction (sitpn_falling_edge sitpn s time_value env)
               using sitpn_falling_edge_ind.

    (* GENERAL CASE, all went well. *)
    - simpl in Hfun; injection Hfun as Heq_s'; rewrite <- Heq_s'.
      simpl.
      specialize (update_time_intervals_same_struct_ditvals
                    sitpn s (d_intervals s) [] d_intervals' e)
        as Hsame_struct_ditvals.
      assumption.

    (* ERROR CASE. *)
    - inversion Hfun.

    (* ERROR CASE. *)
    - inversion Hfun.

  Qed.
      
End SitpnFallingEdgeSameStructDItvals.

