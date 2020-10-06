(** * Stabilization relation. *)

(** Defines the relation that evaluates the behavioral
    part of a design until there are no more events
    on signals or component instances generated;
    then the design is said to be stabilized.
 *)

Require Import Coqlib.
Require Import NatMap.
Require Import NatSet.
Require Import Environment.
Require Import AbstractSyntax.
Require Import CombinationalEvaluation.
Require Import ListsPlus.

(** Defines the stabilization relation. *)

Inductive stabilize (Δ : ElDesign) (σ : DState) (behavior : cs) : list DState -> DState -> Prop :=

(** Case when the design state [σ] registered no event; it has
    stabilized.  The stabilization trace is empty (4th argument). *)

| StabilizeEnd :
    (* * Side conditions * *)
    events σ = NatSet.empty ->
    
    (* * Conclusion * *)
    stabilize Δ σ behavior [] σ 
  
(** Case when the design state [σ] registered some events;
    therefore it has not stabilized.

    Evaluates [behavior] with the [vcomb] relation and sees if the
    newly generated state has stabilized. *)

| StabilizeLoop :
    forall σ' σ'' θ,
      
      (* * Premises * *)
      vcomb Δ σ behavior σ' ->
      stabilize Δ σ' behavior θ σ'' ->

      (* * Side conditions * *)
      
      (* Some events are registered in σ. *)
      events σ <> NatSet.empty ->

      (* σ'' is a quiet state (i.e, no events) *)
      events σ'' = NatSet.empty ->
      
      (* * Conclusion * *)
      stabilize Δ σ behavior (σ' :: θ) σ''.

(** ** Facts about [stabilize] *)

Lemma is_last_of_trace :
  forall Δ σ behavior θ σ',
    stabilize Δ σ behavior θ σ' ->
    (Last θ σ' \/ σ = σ').
Proof.
  induction 1.

  (* BASE CASE. *)
  - right; reflexivity. 

  (* IND. CASE. *)
  - destruct θ.
    + lazymatch goal with
      | [ H: stabilize _ _ _ [] _ |- _ ] =>
        inversion H; left; apply Last_singleton
      end.
    + inversion_clear IHstabilize as [Hlast | Heq].
      -- left; apply Last_cons; assumption.
      -- rewrite Heq in H0; inversion H0; contradiction.
Qed.

Lemma last_no_event :
  forall Δ σ behavior θ σ',
    stabilize Δ σ behavior θ σ' ->
    Last θ σ' ->
    events σ' = {[]}.
Proof.
  induction 1.
  - inversion 1.
  - intros Hlast.
    destruct θ.
    assumption.
    assert (Hconsl : d :: θ <> nil) by inversion 1.
    apply (IHstabilize (last_cons_inv Hconsl Hlast)).
Qed.

(* All signals get a stable value at a certain point of the
   stabilization trace. *)

Lemma stable_value_signal :
  forall θ Δ σ behavior σ',
    stabilize Δ σ behavior θ σ' ->
    (forall s,
      (exists v, MapsTo s v (sigstore σ)) ->
      (exists θ', θ' <> []
                    /\ LeListCons θ' θ
                    /\ exists v, forall σ__j, List.In σ__j θ' -> MapsTo s v (sigstore σ__j)))
    \/ σ = σ'.
Proof.
  
  induction 1.

  (* BASE CASE *)
  - right; reflexivity.

  (* IND. CASE 
     In that case, the left part of the disj. is true.
   *)
  - left; intros.
    
    lazymatch goal with
    | [ Hvcomb: vcomb _ _ _ _, H: (exists v, MapsTo s v (sigstore σ)) |- _ ] =>

      (* s has a value at σ' *)
      inversion_clear H as (v, Hmaps);
        specialize (comb_maps_sigid Δ σ behavior σ' s v Hvcomb Hmaps) as Hex_v'
    end.

    (* 2 CASES: θ' <> [] or σ' = σ'' *)
    inversion_clear IHstabilize as [Hnotnil | Heq_σ'].

    (* CASE θ' <> [] 
       Instantiates θ' and v with the values coming from the IH, then trivial
     *)
    
    + specialize (Hnotnil s Hex_v'); inversion_clear Hnotnil as (θ', Hw).
      decompose [and] Hw.
      exists θ'; split;
        [ assumption |
          split; [ apply LeListCons_cons; assumption | assumption]
        ].

    (* CASE σ' = σ''

       Means that θ = [], otherwise contradicts the fact that σ' has
       an empty event set. *)
      
    + lazymatch goal with
      | [ H: stabilize _ _ _ _ _ |- _ ] =>
        inversion H
      end.

      (* CASE θ = [] 
         Then, there is but one non-empty trace θ' verifying
         θ' <= [σ''], that is θ' = [σ'']
       *)
      -- exists [σ'']; inversion_clear Hex_v' as (v', Hmaps').
         
         (* Solves [σ''] <> [] *)
         split; [ inversion 1 | auto].

         (* Solves LeListCons [σ''] [σ''] *)
         split; [ apply LeListCons_refl | auto].

         (* Solves ∀ σj, σj ∈ [σ''] -> σj(s) = v' 
            There's only one σj verifying σj ∈ [σ''].
          *)
         exists v'; intros σ__j Hin; inversion_clear Hin as [Heq_σ'' | ];
           [rewrite <- Heq_σ''; rewrite <- Heq_σ'; assumption |
            contradiction].

      (* CASE θ non-empty, then contradiction *)
      -- lazymatch goal with
         | [ H: events σ' <> _ |- _ ] =>
           rewrite Heq_σ' in H; contradiction
         end.
Qed.
