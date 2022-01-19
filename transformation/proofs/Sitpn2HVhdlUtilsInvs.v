(** * State invariance properties over HILECOP's transformation utilitary functions *)

Require Import common.CoqLib.
Require Import common.GlobalTypes.
Require Import common.ListPlus.
Require Import common.ListDep.
Require Import common.StateAndErrorMonad.

Require Import String.
Require Import common.proofs.StateAndErrorMonadTactics.

Require Import sitpn.Sitpn.

Require Import hvhdl.HVhdlCoreLib.
Require Import hvhdl.HVhdlHilecopLib.

Require Import transformation.Sitpn2HVhdlTypes.
Require Import transformation.Sitpn2HVhdlUtils.

(** ** State invariance properties about [get_comp] *)

Section GetCompInvs.

  (* Can not use [solve_sinv_pattern] to decide [get_comp_inv_state]
     because it is used in [solve_sinv_pattern].  *)
  
  Lemma get_comp_aux_inv_state :
    forall {cstmt} {sitpn : Sitpn} {id__c : ident} {s : Sitpn2HVhdlState sitpn} {v s'} ,
      get_comp_aux sitpn id__c cstmt s = OK v s' -> s = s'.
  Proof.
    intro; induction cstmt; intros*; cbn; try (solve [inversion 1; subst; reflexivity]).
    destruct (id__c0 =? id__c); intros e; monadInv e; reflexivity.
    intros e; monadInv e.
    transitivity s0; eauto.
    transitivity s1; eauto.
    destruct x in EQ2; (destruct x0 in EQ2; monadInv EQ2; try (reflexivity)).
  Qed.
  
  Lemma get_comp_inv_state :
    forall {sitpn : Sitpn} {id__c} {s : Sitpn2HVhdlState sitpn} {v s'},
      get_comp id__c s = OK v s' -> s = s'.
  Proof. intros *; intros e; monadFullInv e. 
         rewrite (get_comp_aux_inv_state EQ1).
         destruct x0; (monadInv EQ2; try (reflexivity)).
  Qed.
  
End GetCompInvs.

