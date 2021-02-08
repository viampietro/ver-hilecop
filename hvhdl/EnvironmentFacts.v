(** * Facts about H-VHDL Environment *)

Require Import common.Coqlib.
Require Import common.NatSet.

Require Import common.NatMap.
Require Import common.NatMapTactics.

Require Import hvhdl.HVhdlTypes.
Require Import hvhdl.Environment.
Require Import hvhdl.SemanticalDomains.

(** ** Facts about the [IsMergedDState] relation *)

Lemma IsMergedDState_comm :
  forall {σ__o σ σ' σ__m},
    IsMergedDState σ__o σ σ' σ__m <->
    IsMergedDState σ__o σ' σ σ__m.
Proof.
  split; intros;
    match goal with
    | [ H: IsMergedDState _ _ _ _ |- _ ] =>
      unfold IsMergedDState in H; decompose [and] H; clear H
    end;
    let rec solve_imds :=
        match goal with
        | |- IsMergedDState _ _ _ _ => split; solve_imds
        | |- _ /\ _ => split; [solve_imds | solve_imds]
        | |- forall (_ : _) (_ : _), ~NatSet.In _ (_ U _) -> _ <-> _ =>
          intros;
            match goal with
            | [ H: forall (_ : _) (_ : _), ~NatSet.In _ _ -> _ <-> MapsTo _ _ (?f _), H': ~NatSet.In _ _ |- _ <-> MapsTo _ _ (?f _) ] =>
              apply H; auto; do 1 intro; apply H';
                match goal with
                | [ H'': NatSet.In _ (_ U _) |- _ ] =>
                  rewrite union_spec in H''; inversion H''; rewrite union_spec; [right; assumption | left; assumption]
                end
            end
        | |- Equal _ (events ?σ U events ?σ') =>
          transitivity (events σ' U events σ); auto with set
        | _ => firstorder
        end in solve_imds.
Qed.

Lemma IsMergedDState_ex :
  forall {σ__o σ σ'}, exists σ__m, IsMergedDState σ__o σ σ' σ__m.
Proof.
  unfold IsMergedDState.
Admitted.

Ltac decompose_IMDS :=
  match goal with
  | [ H: IsMergedDState _ _ _ _ |- _ ] =>
    unfold IsMergedDState in H; decompose [and] H; clear H
  end.

Lemma IsMergedDState_assoc_1 :
  forall {σ σ0 σ1 σ2 σ12 σ01 σ012},
    IsMergedDState σ σ1 σ2 σ12 ->
    IsMergedDState σ σ0 σ12 σ012 ->
    IsMergedDState σ σ0 σ1 σ01 ->
    IsMergedDState σ σ01 σ2 σ012.
Proof.
  intros;
    do 3 decompose_IMDS;
    let rec solve_imds :=
        match goal with
        | |- IsMergedDState _ _ _ _ => split; solve_imds
        | |- _ /\ _ => split; [solve_imds | solve_imds]
        | |- Equal _ (events ?σ U events ?σ') => 
          match goal with
          | [ H: Equal ?ev012 (_ U ?ev12), H': Equal ?ev01 _, H'': Equal ?ev12 _
              |- Equal ?ev012 (?ev01 U _) ] =>
            rewrite H; rewrite H'; rewrite H''; auto with set
          end
        | _ => auto
        end in solve_imds.

        (* [∀ id ∈ (events σ01) -> (sigstore σ01) (id) = (sigstore σ012) (id)] *)
        - intros;
            match goal with
            | [ H: Equal (events ?σ) (_ U _), H': NatSet.In _ (_ ?σ) |- MapsTo _ _ (_ ?σ) <-> _ ] =>
              rewrite H, union_spec in H'; inversion H'
            end.

          (* CASE [id ∈ (events σ0)] *)
          transitivity (MapsTo id v (sigstore σ0)); rw_mapsto.
          
          (* CASE [id ∈ (events σ1) ] *)
          transitivity (MapsTo id v (sigstore σ1)); [rw_mapsto | auto].
          transitivity (MapsTo id v (sigstore σ12)); rw_mapsto;
            match goal with
            | [ H: Equal (events ?σ12) _ |- NatSet.In _ (events ?σ12) ] =>
              rewrite H; auto with set
            end.

        (* [∀ id ∈ (events σ2) -> (sigstore σ2) (id) = (sigstore σ012) (id)] *)
        - intros;
            transitivity (MapsTo id v (sigstore σ12)); rw_mapsto;
              match goal with
              | [ H: Equal (events ?σ12) _ |- NatSet.In _ (events ?σ12) ] =>
                rewrite H; auto with set
              end.

        (* [∀ id ∉ (events σ01) U (events σ2) -> (sigstore σ) (id) = (sigstore σ012) (id)] *)
        - intros id v; intros; rw_mapsto.
          match goal with
          | [ H: Equal (events ?σ12) _, H': Equal (events ?σ01) _, H'': ~NatSet.In _ (events ?σ01 U _)
              |- ~NatSet.In _ (_ U events ?σ12) ] =>
            rewrite H' in H''; rewrite H; erewrite <- union_assoc; eauto
          end.

        (* [∀ id ∈ (events σ01) -> (compstore σ01) (id) = (compstore σ012) (id)] *)
        - intros id v; intros;
            match goal with
            | [ H: Equal (events ?σ) (_ U _), H': NatSet.In _ (_ ?σ) |- MapsTo _ _ (_ ?σ) <-> _ ] =>
              rewrite H, union_spec in H'; inversion H'
            end.

          (* CASE [id ∈ (events σ0)] *)
          transitivity (MapsTo id v (compstore σ0)); rw_mapsto.
          
          (* CASE [id ∈ (events σ1) ] *)
          transitivity (MapsTo id v (compstore σ1)); [rw_mapsto | auto].
          transitivity (MapsTo id v (compstore σ12)); rw_mapsto;
            match goal with
            | [ H: Equal (events ?σ12) _ |- NatSet.In _ (events ?σ12) ] =>
              rewrite H; auto with set
            end.

        (* [∀ id ∈ (events σ2) -> (compstore σ2) (id) = (compstore σ012) (id)] *)
        - intros id v; intros;
            transitivity (MapsTo id v (compstore σ12)); rw_mapsto;
              match goal with
              | [ H: Equal (events ?σ12) _ |- NatSet.In _ (events ?σ12) ] =>
                rewrite H; auto with set
              end.

        (* [∀ id ∉ (events σ01) U (events σ2) -> (compstore σ) (id) = (compstore σ012) (id)] *)
        - intros id v; intros; rw_mapsto.
          match goal with
          | [ H: Equal (events ?σ12) _, H': Equal (events ?σ01) _, H'': ~NatSet.In _ (events ?σ01 U _)
              |- ~NatSet.In _ (_ U events ?σ12) ] =>
            rewrite H' in H''; rewrite H; erewrite <- union_assoc; eauto
          end.
Qed.

Lemma IsMergedDState_assoc_2 :
  forall {σ σ0 σ1 σ2 σ12 σ01 σ012},
    IsMergedDState σ σ0 σ1 σ01 ->
    IsMergedDState σ σ01 σ2 σ012 ->
    IsMergedDState σ σ1 σ2 σ12 ->
    IsMergedDState σ σ0 σ12 σ012.
Proof.
  intros;
    do 3 decompose_IMDS;
    let rec solve_imds :=
        match goal with
        | |- IsMergedDState _ _ _ _ => split; solve_imds
        | |- _ /\ _ => split; [solve_imds | solve_imds]
        | |- Equal _ (events ?σ U events ?σ') =>
          match goal with
          | [ H: Equal ?ev012 (?ev01 U _), H': Equal ?ev01 _, H'': Equal ?ev12 _
              |- Equal ?ev012 (_ U ?ev12) ] =>
            rewrite H; rewrite H'; rewrite H''; auto with set
          end
        | _ => auto
        end in solve_imds.

        (* [∀ id ∈ (events σ0) -> (sigstore σ0) (id) = (sigstore σ012) (id)] *)
        - intros;
            transitivity (MapsTo id v (sigstore σ01)); rw_mapsto;
              match goal with
              | [ H: Equal (events ?σ01) _ |- NatSet.In _ (events ?σ01) ] =>
                rewrite H; auto with set
              end.
        
        (* [∀ id ∈ (events σ12) -> (sigstore σ12) (id) = (sigstore σ012) (id)] *)
        - intros;
          match goal with
          | [ H: Equal (events ?σ) (_ U _), H': NatSet.In _ (_ ?σ) |- MapsTo _ _ (_ ?σ) <-> _ ] =>
            rewrite H, union_spec in H'; inversion H'
          end.

          (* CASE [id ∈ (events σ1)] *)
          transitivity (MapsTo id v (sigstore σ1)); [ rw_mapsto | auto].
          transitivity (MapsTo id v (sigstore σ01)); rw_mapsto;
            match goal with
            | [ H: Equal (events ?σ12) _ |- NatSet.In _ (events ?σ12) ] =>
              rewrite H; auto with set
            end.
          
          (* CASE [id ∈ (events σ2) ] *)
          transitivity (MapsTo id v (sigstore σ2)); rw_mapsto.
          
        (* [∀ id ∉ (events σ0) U (events σ12) -> (sigstore σ) (id) = (sigstore σ012) (id)] *)
        - intros id v; intros; rw_mapsto.
          match goal with
          | [ H: Equal (events ?σ01) _, H': Equal (events ?σ12) _, H'': ~NatSet.In _ (_ U events ?σ12)
              |- ~NatSet.In _ (events ?σ01 U _) ] =>
            rewrite H' in H''; rewrite H; erewrite union_assoc; eauto
          end.

        (* [∀ id ∈ (events σ0) -> (compstore σ0) (id) = (compstore σ012) (id)] *)
        - intros id v; intros;
            transitivity (MapsTo id v (compstore σ01)); rw_mapsto;
              match goal with
              | [ H: Equal (events ?σ01) _ |- NatSet.In _ (events ?σ01) ] =>
                rewrite H; auto with set
              end.
          
        (* [∀ id ∈ (events σ12) -> (compstore σ12) (id) = (compstore σ012) (id)] *)
        - intros id v; intros;
            match goal with
            | [ H: Equal (events ?σ) (_ U _), H': NatSet.In _ (_ ?σ) |- MapsTo _ _ (_ ?σ) <-> _ ] =>
              rewrite H, union_spec in H'; inversion H'
            end.

          (* CASE [id ∈ (events σ1)] *)
          transitivity (MapsTo id v (compstore σ1)); [ rw_mapsto | auto].
          transitivity (MapsTo id v (compstore σ01)); rw_mapsto;
            match goal with
            | [ H: Equal (events ?σ12) _ |- NatSet.In _ (events ?σ12) ] =>
              rewrite H; auto with set
            end.
          
          (* CASE [id ∈ (events σ2) ] *)
          transitivity (MapsTo id v (compstore σ2)); rw_mapsto.
          
        (* [∀ id ∉ (events σ0) U (events σ12) -> (compstore σ) (id) = (compstore σ012) (id)] *)
        - intros id v; intros; rw_mapsto.
          match goal with
          | [ H: Equal (events ?σ01) _, H': Equal (events ?σ12) _, H'': ~NatSet.In _ (_ U events ?σ12)
              |- ~NatSet.In _ (events ?σ01 U _) ] =>
            rewrite H' in H''; rewrite H; erewrite union_assoc; eauto
          end.
Qed.
