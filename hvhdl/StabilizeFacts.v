(** * Facts about Stabilization *)

Require Import common.Coqlib.
Require Import common.NatMap.
Require Import common.NatSet.
Require Import common.ListPlus.

Require Import hvhdl.Environment.
Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.CombinationalEvaluation.
Require Import hvhdl.HVhdlTypes.
Require Import hvhdl.Stabilize.
Require Import hvhdl.Place.
Require Import hvhdl.HilecopDesignStore.

Lemma is_last_of_trace :
  forall D__s Δ σ behavior θ σ',
    stabilize D__s Δ σ behavior θ σ' ->
    (Last θ σ' \/ σ = σ').
Proof.
  induction 1.

  (* BASE CASE. *)
  - right; reflexivity. 

  (* IND. CASE. *)
  - destruct θ.
    + lazymatch goal with
      | [ H: stabilize _ _ _ _ [] _ |- _ ] =>
        inversion H; left; apply Last_singleton
      end.
    + inversion_clear IHstabilize as [Hlast | Heq].
      -- left; apply Last_cons; assumption.
      -- rewrite Heq in H0; inversion H0; contradiction.
Qed.

Lemma last_no_event :
  forall D__s Δ σ behavior θ σ',
    stabilize D__s Δ σ behavior θ σ' ->
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
  forall D__s θ Δ σ behavior σ',
    stabilize D__s Δ σ behavior θ σ' ->
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
    | [ Hvcomb: vcomb _ _ _ _ _, H: (exists v, MapsTo s v (sigstore σ)) |- _ ] =>

      (* s has a value at σ' *)
      inversion_clear H as (v, Hmaps);
        specialize (comb_maps_sigid D__s Δ σ behavior σ' s v Hvcomb Hmaps) as Hex_v'
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
      | [ H: stabilize _ _ _ _ _ _ |- _ ] =>
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

Lemma stab_inv_s_marking :
  forall Δ σ behavior θ σ',
    stabilize hdstore Δ σ behavior θ σ' ->
    forall id__p gm ipm opm σ__p σ__p' v,
      InCs (cs_comp id__p Petri.place_entid gm ipm opm) behavior ->
      MapsTo id__p σ__p (compstore σ) ->
      MapsTo s_marking v (sigstore σ__p) ->
      MapsTo id__p σ__p' (compstore σ') ->
      MapsTo s_marking v (sigstore σ__p').
Admitted.
