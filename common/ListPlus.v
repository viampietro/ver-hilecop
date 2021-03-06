(** Exports all modules pertaining to lists and defines new lists
    predicates.  The predicates are useful in the formalization 
    and the proofs.
 *)

Require Import CoqLib.
Require Import common.GlobalFacts.
Require Import SetoidList.
Require Import GlobalTypes.
Require Export FstSplit.
Require Export InAndNoDup.

Set Implicit Arguments.

(** ** Miscellaneous list functions. *)

Section ListPlusMisc.

  Variable A : Type.
  
  Definition is_empty (l : list A) : bool := if l then true else false.

  (* Given that the equality between elements of type A is
         decidable, computes the intersection between two lists of
         As. *)

  Definition inter (eq : A -> A -> Prop)
    (Aeqdec : forall x y : A, {eq x y} + {~eq x y}) (l m : list A) :=
    filter (fun a => if InA_dec Aeqdec a m then true else false) l. 

  (** States that a finite set is implemented by a list. *)

  Definition Set_in_List (A : Type) (P : A -> Prop) (l : list A) : Prop :=
    (forall a : A, P a <-> In a l) /\ NoDup l.

  Definition Set_in_ListA {A : Type} (eqA : A -> A -> Prop) (P : A -> Prop) (l : list A) : Prop :=
    (forall a : A, P a <-> InA eqA a l) /\ NoDupA eqA l.
  
  Definition Sig_in_List {A : Type} {P : A -> Prop} (l : list {x : A | P x}) : Prop :=
    (forall a : {x : A | P x}, InA GlobalFacts.P1SigEq a l) /\ NoDupA GlobalFacts.P1SigEq l.

  (** States that a given list enumerates all the elements of a given
      type [A], and thus that the number of elements in [A] is
      finite. Inspired from [Coq.Logic.FinFun]. *)
  
  Definition Full (eqA : A -> A -> Prop) (l : list A) :=
    forall a : A, InA eqA a l.

  Definition FullP (eqA : A -> A -> Prop) (P : A -> Prop) (l : list A) :=
    forall a : A, P a <-> InA eqA a l.

  Definition Listing (eqA : A -> A -> Prop) (l : list A) :=
    NoDupA eqA l /\ Full eqA l.

  Definition ListingP (eqA : A -> A -> Prop) (P : A -> Prop) (l : list A) :=
    NoDupA eqA l /\ FullP eqA P l.
  
End ListPlusMisc.

(** ** Operations and predicates on functions implemented as lists of couples *)

Section FunAsListOfCouples.

  Variable A B : Type.
  Variable eqA : A -> A -> Prop.
  Variable eqA_dec : forall x y : A, {eqA x y} + {~eqA x y}.
  Variable eqB : B -> B -> Prop.
  Variable eqB_dec : forall x y : B, {eqB x y} + {~eqB x y}.
  
  (** States that a given list of couples [A * B] implements a
      function from [A] to [B]. *)
  
  Definition IsFun (l : list (A * B)) := NoDupA eqA (fs l).

  (** States that a given list of couples [A * B] implements a
      application from [A] to [B]. *)
  
  Definition IsApp (l : list (A * B)) := Listing eqA (fs l).
  
  (** Equality between two couples [A * B] *)
  
  Definition ProdEq (c1 c2 : A * B) :=
    eqA (fst c1) (fst c2) /\ eqB (snd c1) (snd c2).
  
  (** States that a given list of couples [l] implements an injective
      application from [A] to [B]. *)

  Definition IsInjective (l : list (A * B)) :=
    IsApp l /\ forall y x1 x2, InA ProdEq (x1, y) l -> InA ProdEq (x2, y) l -> eqA x1 x2.

  (** States that a given list of couples [l] implements a surjective
      application from [A] to [B]; i.e. all the elements of type [B]
      are in the second elements of [l]. *)

  Definition IsSurjective (l : list (A * B)) :=
    IsApp l /\ forall y, InA eqB y (snd (split l)).

  (** Variant: all the elements of type [B] and that verify property
      [P] are in the second elements of [l]. *)
  
  Definition IsSurjectiveP (P : B -> Prop) (l : list (A * B)) :=
    IsApp l /\ forall y, InA eqB y (snd (split l)).

  (** States that a given list of couples [l] implements a bijective
      application. *)

  Definition IsBijective (l : list (A * B)) :=
    IsInjective l /\ IsSurjective l.

  Definition IsBijectiveP (P : B -> Prop) (l : list (A * B)) :=
    IsInjective l /\ IsSurjectiveP P l.
  
  (** Returns [Some a] if it is asscoiated with [k] in list [l].  
      Returns None, if k is not in the first elements of [l].
   *)

  Fixpoint getv (k : A) (l : list (A * B)) {struct l} : option B :=
    match l with
    | nil => None
    | cons (a, b) tl => if eqA_dec k a then Some b else getv k tl
    end.

  (** Sets the couple [(k, v)] in list [l]. If [k] is in the first
      elements of [l], then the old binding of [k] to value in [l] is
      replaced by the binding of [k] to [v].  Puts the couple [(k,v)]
      at the end of list [l] otherwise. *)

  Fixpoint setv (k : A) (v : B) (l : list (A * B)) {struct l} : list (A * B) :=
    match l with
    | nil => [(k, v)]
    | cons (a, b) tl => if eqA_dec k a then cons (k, v) tl else cons (a, b) (setv k v tl)
    end.

  Functional Scheme setv_ind := Induction for setv Sort Prop.

  (** Returns the domain of function implemented by the list of
      couples [l]. *)

  Definition dom (l : list (A * B)) := fst (split l).

  (** Returns the codomain of the function implemented by the list of
      couples [l]. *)

  Definition codom (l : list (A * B)) := snd (split l).

  (** Creates a new list that implements the function from [A ??? B] to
      [C] by merging the domains of the two functions implemented by
      [l] and [m]. *)
  
  Variable C : Type.
  
  Definition merge_dom (l : list (A * C)) (m : list (B * C)) :
    list ((A + B) * C) :=
    (map (fun '(a, c) => (inl a, c)) l) ++ (map (fun '(b, c) => (inr b, c)) m).
    
  
End FunAsListOfCouples.

Arguments getv {A B eqA}.
Arguments setv {A B eqA}.

(** ** Map function with possible errors (Option Map). *)

Section OMap.

  Variable A B : Type.
  
  Variable fopt_map : A -> option B.
  
  (** Maps all elements of [lofAs] to a term [b] of [B] and returns
      the resulting list or return an error. *)

  Fixpoint omap_aux (lofAs : list A) (lofBs : list B) {struct lofAs} :
    option (list B) :=
    match lofAs with
    | nil => Some lofBs
    | a :: tl =>
      (* Continues the mapping or returns an error. *)
      match fopt_map a with
      | Some b => omap_aux tl (lofBs ++ [b])
      | None => None
      end
    end.

  (** Wrapper around the [omap_aux] function. *)

  Definition omap (lofAs : list A) : option (list B) :=
    omap_aux lofAs nil.

  (** Version with optionE used instead of option. *)

  Variable fopte_map : A -> optionE B.
  
  (** Maps all elements of [lofAs] to a term [b] of [B] and returns
      the resulting list or return an error. *)

  Fixpoint oemap_aux (lofAs : list A) (lofBs : list B) {struct lofAs} :
    optionE (list B) :=
    match lofAs with
    | nil => Success lofBs
    | a :: tl =>
      (* Continues the mapping or returns an error. *)
      match fopte_map a with
      | Success b => oemap_aux tl (lofBs ++ [b])
      | Err msg => Err msg
      end
    end.

  (** Wrapper around the [omap_aux] function. *)

  Definition oemap (lofAs : list A) : optionE (list B) :=
    oemap_aux lofAs nil.
  
End OMap.

Arguments omap_aux {A B}.
Arguments omap {A B}.
Arguments oemap_aux {A B}.
Arguments oemap {A B}.

(** Fold left function with possible errors (Option Fold left). *)

Section OFold_left.

  Variable A B : Type.
  
  Variable f : A -> B -> option A.

  Fixpoint ofold_left (l:list B) (a0 : A) : option A :=
    match l with
    | nil => Some a0
    | cons b t => match f a0 b with
                  | None => None
                  | Some a => ofold_left t a
                  end
    end.

  (** Version with optionE used instead of option. *)
  
  Variable fe : A -> B -> optionE A.

  Fixpoint oefold_left (l:list B) (a0 : A) : optionE A :=
    match l with
    | nil => Success a0
    | cons b t => match fe a0 b with
                  | Err msg => Err msg
                  | Success a => oefold_left t a
                  end
    end.
  
End OFold_left.

Arguments ofold_left {A B}.
Arguments oefold_left {A B}.

(** ** Predicates IsDecListCons, IsDecListApp and facts. *)

Section DecreasedList.

  (** List l is a decreased or equal version of list l'. 
      l' is built from l by adding elements in the front (cons).
       
      Useful for proof involving recursion on lists.  *)
  
  Inductive IsDecListCons {A: Type} : list A -> list A -> Prop :=
  | IsDecListCons_refl : forall l : list A, IsDecListCons l l
  | IsDecListCons_eq : forall (a : A) (l : list A), IsDecListCons l (a :: l)
  | IsDecListCons_cons :
      forall (a : A) (l l' : list A),
      IsDecListCons l l' ->      
      IsDecListCons l (a :: l').

  Hint Constructors IsDecListCons : core.
  
  (** *** Facts about IsDecListCons. *)
  
  Lemma is_dec_list_cons_nil {A : Type} :
    forall (l : list A), IsDecListCons [] l.
  Proof.
    induction l.
    - apply IsDecListCons_refl.
    - apply IsDecListCons_cons; assumption.
  Qed.

  Lemma is_dec_list_cons_app_eq {A : Type} :
    forall (l l' : list A),
      IsDecListCons l (l' ++ l).
  Proof.
    induction l'.

    (* BASE CASE *)
    - simpl; apply IsDecListCons_refl.

    (* INDUCTION CASE *)
    - rewrite <- app_comm_cons; apply IsDecListCons_cons; assumption.
  Qed.
  
  Lemma is_dec_list_cons_incl {A : Type} :
    forall l' l : list A, IsDecListCons l l' -> incl l l'.
  Proof.
    intros l l'; induction 1.
    - firstorder.
    - firstorder.
    - apply incl_tl; assumption.      
  Qed.

  Lemma is_dec_list_cons_cons {A : Type} :
    forall (a : A) (l' l : list A), IsDecListCons (a :: l) l' -> IsDecListCons l l'.
  Proof.
    intros a l'.
    induction l'; intros l His_dec.
    
    - inversion His_dec. 
    - inversion His_dec; auto.
  Qed.

  (** If l' has no duplicates and l is a decreased version of l' then
      l has no duplicates. *)
  
  Lemma nodup_is_dec_list_cons {A : Type} :
    forall (l' l : list A),
      NoDup l' ->
      IsDecListCons l l' ->
      NoDup l.
  Proof.
    induction l'; intros l Hnodup_l' His_dec.
    
    (* BASE CASE *)
    - inversion His_dec; apply NoDup_nil.

    (* INDUCTION CASE *)
    - inversion His_dec.
      
      (* Case IsDecListCons_refl *)
      + assumption.

      (* Case IsDecListCons_eq *)
      + rewrite NoDup_cons_iff in Hnodup_l';
          apply proj2 in Hnodup_l';
          assumption.

      (* Case IsDecListCons_cons *)
      + rewrite NoDup_cons_iff in Hnodup_l';
          apply proj2 in Hnodup_l';
          apply (IHl' l Hnodup_l' H1).
  Qed.

  (** If IsDecListCons l l' then it's possible to
      decompose l' in (m ++ l). *)
  
  Lemma is_dec_list_cons_exists_app {A : Type} :
    forall (l' l : list A),
      IsDecListCons l l' -> exists l'' : list A, l' = l'' ++ l.
  Proof.
    induction l'; intros l His_dec.

    (* BASE CASE *)
    - inversion His_dec.
      exists []; rewrite app_nil_r; auto.

    (* INDUCTION CASE *)
    - inversion His_dec.
      + exists []. simpl. reflexivity.
      + exists [a]. simpl. reflexivity.
      + specialize (IHl' l H1) as Hex.
        inversion_clear Hex as (m & Heq_l'_ml).
        rewrite Heq_l'_ml.
        exists (a :: m).
        auto.
  Qed.

  (** concat is a morphism for IsDecListCons. *)
  
  Lemma is_dec_list_cons_concat {A : Type} :
    forall (ll ll' : list (list A)),
      IsDecListCons ll ll' -> IsDecListCons (concat ll) (concat ll').
  Proof.
    intros ll ll' His_dec.
    specialize (is_dec_list_cons_exists_app His_dec) as Hex_l''.
    inversion_clear Hex_l'' as (l'' & Heq_l'_ll'').
    rewrite Heq_l'_ll''.
    rewrite concat_app.
    apply is_dec_list_cons_app_eq.
  Qed.

  (** Simpler definition of IsDecListCons. *)
  
  Inductive LeListCons {A: Type} : list A -> list A -> Prop :=
  | LeListCons_refl : forall l : list A, LeListCons l l
  | LeListCons_cons :
      forall (a : A) (l l' : list A),
        LeListCons l l' ->      
        LeListCons l (a :: l').

  Hint Constructors LeListCons : core.

  Lemma lelistcons_nil {A : Type} :
    forall (l : list A), LeListCons [] l.
  Proof.
    induction l.
    - apply LeListCons_refl.
    - apply LeListCons_cons; assumption.
  Qed.
  
  (** List l is a decreased or equal version of list l'. 
      l' is built from l by adding elements in the front (cons).
       
      Useful for proof involving recursion on lists.  *)

  Inductive IsDecListApp {A : Type} : list A -> list A -> Prop :=
  | IsDecListApp_refl : forall l : list A, IsDecListApp l l
  | IsDecListApp_cons :
      forall (a : A) (l l' : list A),
        IsDecListApp l l' ->
        IsDecListApp l (l' ++ [a]).
  
End DecreasedList.

(** ** Predicate IsPredInList and facts. *)

Section PredInList.

  Variable A : Type.
    
  (** Tells if x is a predecessor of y in list l. 
      x and y are possibly equal and list l
      possibly contains duplicates. *)
  
  Inductive IsPredInList (x y : A) : list A -> Prop :=
  | IsPredInList_eq :
      forall l : list A, IsPredInList x y (x :: y :: l)
  | IsPredInList_rm_snd :
      forall (a : A) (l : list A), IsPredInList x y (x :: l) ->
                                   IsPredInList x y (x :: a :: l)
  | IsPredInList_rm_fst : 
      forall (a : A) (l : list A), IsPredInList x y l ->
                                   IsPredInList x y (a :: l).

  (** IsPredInList with no duplicates in list l, x and y different. *)
  
  Definition IsPredInNoDupList (x y : A) (l : list A) :=
    x <> y /\ NoDup l /\ IsPredInList x y l.

  (** *** Facts about IsPredInList and IsPredInNoDuplist. *)
  
  Lemma not_is_pred_in_list_nil :
    forall (x y : A), ~IsPredInList x y [].
  Proof.
    intros x y His_pred.
    inversion His_pred.
  Qed.

  Lemma is_pred_in_list_in_tail :
    forall (x y : A) (l : list A), In y l -> IsPredInList x y (x :: l).
  Proof.
    induction l.
    - intro Hnot_in; inversion Hnot_in.
    - intro Hin_y_l; inversion Hin_y_l.
      + rewrite H; apply IsPredInList_eq.
      + apply IsPredInList_rm_snd; apply (IHl H).
  Qed.
  
  Theorem is_pred_in_dec_list :
    forall (l l' : list A) (x y : A),
      IsPredInList x y l -> IsDecListCons l l' -> NoDup l' -> IsPredInList x y l'.
  Proof.
    induction l'.
    - intros x y His_pred His_dec Hnodup.
      induction l.
      + inversion His_pred.
      + inversion His_dec.
    - intros x y His_pred His_dec Hnodup.
      inversion His_dec.
      + rewrite <- H0; assumption.
      + rewrite <- H2; apply IsPredInList_rm_fst; assumption. 
      + apply IsPredInList_rm_fst.
        -- apply NoDup_cons_iff in Hnodup; apply proj2 in Hnodup.
           apply (IHl' x y His_pred H1 Hnodup).
  Qed.

  Lemma is_pred_cons_diff :
    forall (l : list A) (x y a : A) , IsPredInList x y (a :: l) ->
                                      x <> a ->
                                      IsPredInList x y l.
  Proof.
    induction l; intros x y a' His_pred Hdiff.
    - inversion His_pred; inversion H0.
    - inversion His_pred.
      + contradiction.
      + contradiction.
      + assumption.
  Qed.

  Lemma is_pred_in_tail :
    forall (l : list A) (x y : A) , IsPredInNoDupList x y (x :: l) -> In y l.
  Proof.
    induction l; intros x y His_pred;
      unfold IsPredInNoDupList in His_pred; decompose [and] His_pred.
    - inversion H2; inversion H3.
    - inversion H2.
      + apply in_eq.
      + apply NoDup_remove with (l := [x]) in H1.
        apply proj1 in H1.
        unfold IsPredInNoDupList in IHl.
        specialize (IHl x y (conj H (conj H1 H3))) as Hin_y_l.
        apply in_cons.
        assumption.
      + inversion H1.
        apply not_in_cons in H7.
        apply proj1 in H7.
        specialize (is_pred_cons_diff H3 H7) as His_pred_in_l.
        apply IsPredInList_rm_fst with (a := x) in His_pred_in_l.
        apply in_cons.
        apply NoDup_remove with (l := [x]) in H1.
        apply proj1 in H1.
        unfold IsPredInNoDupList in IHl.
        specialize (IHl x y (conj H (conj H1 His_pred_in_l))) as Hin_y_l.
        assumption.
  Qed.

  Theorem not_is_pred_in_list_if_hd :
    forall (l : list A) (x y : A) (eqA_dec : forall x y : A, {x = y} + {x <> y}),
      ~IsPredInNoDupList x y (y :: l).
  Proof.
    induction l; intros x y eqA_dec His_pred.
    - unfold IsPredInNoDupList in His_pred.
      decompose [and] His_pred.
      repeat (match goal with
              | H : IsPredInList _ _ _ |- _ => inversion H
              end).
      
    - unfold IsPredInNoDupList in His_pred.
      decompose [and] His_pred.
      match goal with
      | H : IsPredInList _ _ _ |- _ => inversion H
      end.
      + contradiction.
      + contradiction.
      + specialize (eqA_dec x a) as eqA_dec_xa.
        elim eqA_dec_xa.
        -- intro Heq_xa.
           rewrite Heq_xa in H3.
           rewrite Heq_xa in H.
           apply NoDup_cons_iff in H1.
           elim H1; intros Hnot_in_y Hnodup.
           specialize (is_pred_in_tail (conj H (conj Hnodup H3))) as Hin_y_l.
           apply in_cons with (a := a) in Hin_y_l.
           contradiction.
        -- intro Hneq_xa.
           specialize (is_pred_cons_diff H3 Hneq_xa) as His_pred_in_l.
           apply IsPredInList_rm_fst with (a := y) in His_pred_in_l.
           apply NoDup_remove with (l := [y]) in H1.
           apply proj1 in H1.
           unfold IsPredInNoDupList in IHl.
           apply (IHl x y eqA_dec); auto.
  Qed.

  Theorem not_is_pred_in_dec_list :
    forall (l' l : list A) (x y : A)
           (eqA_dec : forall x y : A, {x = y} + {x <> y}),
      IsDecListCons (y :: l) l' ->
      In x l ->
      ~IsPredInNoDupList x y l'.
  Proof.
    induction l'; intros l x y eqA_dec His_dec Hin_x_l.
    - inversion His_dec.
    - intro His_pred.
      unfold IsPredInNoDupList in His_pred; decompose [and] His_pred.
      rename H into Hneq_xy; rename H1 into Hnodup; clear His_pred; rename H2 into His_pred.
      inversion His_pred.
      + inversion His_dec.
        -- rewrite <- H3 in H0; contradiction.
        -- rewrite <- H4 in Hnodup.
           rewrite <- H0 in Hnodup.
           apply in_cons with (a := y) in Hin_x_l.
           apply NoDup_cons_iff in Hnodup.
           apply proj1 in Hnodup; contradiction.
        -- apply is_dec_list_cons_cons in H3.
           apply is_dec_list_cons_incl in H3.
           apply H3 in Hin_x_l.
           rewrite <- H0 in Hnodup.
           apply NoDup_cons_iff in Hnodup.
           apply proj1 in Hnodup; contradiction.
      + inversion His_dec.
        -- rewrite <- H4 in H; contradiction.
        -- rewrite <- H5 in Hnodup.
           rewrite <- H in Hnodup.
           apply in_cons with (a := y) in Hin_x_l.
           apply NoDup_cons_iff in Hnodup.
           apply proj1 in Hnodup; contradiction.
        -- apply is_dec_list_cons_cons in H4.
           apply is_dec_list_cons_incl in H4.
           apply H4 in Hin_x_l.
           rewrite <- H in Hnodup.
           apply NoDup_cons_iff in Hnodup.
           apply proj1 in Hnodup; contradiction.
      + inversion His_dec.
        -- assert (Hnot_is_pred : ~IsPredInNoDupList x y (y :: l)) by
             (apply not_is_pred_in_list_if_hd; assumption).
           rewrite <- H4 in His_pred; rewrite <- H4 in Hnodup.
           rewrite <- H5 in His_pred; rewrite <- H5 in Hnodup.
           specialize (conj Hneq_xy (conj Hnodup His_pred)) as His_pred'.
           contradiction.
        -- assert (Hnot_is_pred : ~IsPredInNoDupList x y (y :: l))
            by (apply not_is_pred_in_list_if_hd; assumption).
           rewrite <- H5 in Hnodup; rewrite <- H5 in H0.
           apply NoDup_cons_iff in Hnodup.
           apply proj2 in Hnodup.
           specialize (conj Hneq_xy (conj Hnodup H0)) as His_pred'.
           contradiction.
        -- apply NoDup_cons_iff in Hnodup.
           apply proj2 in Hnodup.
           eapply IHl'; eauto.
           unfold IsPredInNoDupList; auto.
  Qed.

  (** *** Predecessor or same element in list *)

  (** Same as [IsPredInList]; addition of the rule [LeInlist_refl]. *)
  
  Inductive LeInList {A} (x : A) : A -> list A -> Prop :=
  | LeInList_refl :
      forall l, LeInList x x (x :: l)
  | LeInList_hd :
      forall y l, LeInList x y (x :: y :: l)
  | LeInlist_rm_snd :
      forall y l a, LeInList x y (x :: l) ->
                    LeInList x y (x :: a :: l)
  | LeInList_rm_fst : 
      forall y l a, (x = y \/ a <> y) ->
                    LeInList x y l ->
                    LeInList x y (a :: l).

  (** *** Facts about [LeInList] *)
  
  Lemma leinlist_in_refl :
    forall l (x : A), List.In x l -> LeInList x x l.
  Proof.
    intros l; induction l.
    - contradiction.
    - inversion 1; [
        lazymatch goal with
        | [ H: a = ?x |- _ ] => rewrite H; apply LeInList_refl
        end |
        apply LeInList_rm_fst; auto].
  Qed.

  Lemma leinlist_cons :
    forall l (x y a : A), LeInList x y  (a :: l) -> x <> a -> List.In x l -> LeInList x y l.
  Proof.
    intros l x y a Hle_cons; dependent induction Hle_cons; intros; (contradiction || assumption).    
  Qed.
  
End PredInList.

(** ** Last element of a list *)

Section LastElt.

  (** States that some elt is at the last position of an non-empty
      list. *)
  
  Inductive Last {A} : list A -> A -> Prop :=
  | Last_singleton : forall a, Last (cons a nil) a
  | Last_cons : forall l a b, Last l a -> Last (b :: l) a.

  (** *** Facts about [Last] *)
  
  Lemma last_cons_inv :
    forall {A l a b}, l <> nil -> @Last A (b :: l) a -> @Last A l a.
  Proof.
    intros;
      lazymatch goal with
      | [ H: Last (_ :: _) _ |- _ ] =>
        dependent induction H; [contradiction | assumption]
      end.
  Qed.
  
End LastElt.

(** ** Propositional version of Fold left *)

Section Fold_left_prop.
  Variables (A : Type) (B : Type).
  Variable f : A -> B -> A.
  
  Inductive FoldL : list B -> A -> A -> Prop :=
  | FoldL_nil : forall acc, FoldL nil acc acc
  | FoldL_cons :
      forall l b acc acc',
        FoldL l (f acc b) acc' ->
        FoldL (b :: l) acc acc'.

  (** *** Facts about FoldL *)

  Lemma FoldL_xres :
    forall (l : list B) (acc : A),
    exists res, FoldL l acc res.
  Proof.
    intros l; induction l; intros.

    - exists acc; apply FoldL_nil.
    - specialize (IHl (f acc a)).
      inversion_clear IHl as (res, IH); exists res.
      apply FoldL_cons; assumption.
  Qed.
  
End Fold_left_prop.

Arguments FoldL {A B}.

(** ** Boolean and lists. *)

Section BoolAndLists.

  Variable A : Type.
  Variable f : A -> bool.

  (* States that the boolean [sum] is the sum of the application of
     function [f] to the elements of list [l]. *)
  
  Definition BSum (l : list A) (sum : bool) : Prop :=
    FoldL (fun sum a => sum || f a) l false sum.

  Definition bsum (l : list A) : bool :=
    fold_left (fun sum a => sum || f a) l false.
  
  (* States that the boolean [prod] is the product of the application
     of function [f] to the elements of list [l]. *)

  Definition BProd (l : list A) (prod : bool) : Prop :=
    FoldL (fun prod a => prod && f a) l true prod.

  Definition bprod (l : list A) : bool :=
    fold_left (fun prod a => prod && f a) l true.
  
End BoolAndLists.

(** ** Nat and lists. *)

Section NatAndLists.

  Variable A : Type.
  Variable f : A -> nat.

  (* States that the nat [sum] is the sum of the application of
     function [f] to the elements of list [l]. *)
  
  Definition NatSum (l : list A) (sum : nat) : Prop :=
    FoldL (fun sum a => sum + f a) l 0 sum.

  Definition natsum (l : list A) : nat :=
    fold_left (fun sum a => sum + f a) l 0.
  
  (* States that the nat [prod] is the product of the application
     of function [f] to the elements of list [l]. *)

  Definition NatProd (l : list A) (prod : nat) : Prop :=
    FoldL (fun prod a => prod * f a) l 1 prod.

  Definition natprod (l : list A) : nat :=
    fold_left (fun prod a => prod * f a) l 1.
  
End NatAndLists.

(** ** Propositional version of Map *)

Section Map_prop.

  Inductive Map {A B : Type} (f : A -> B) : list A -> list B -> Prop :=
  | Map_nil : Map f [] []
  | Map_cons : forall l m a, Map f l m -> Map f (a :: l) (f a :: m).
  
End Map_prop.

(** ** Sequence of natural numbers *)

Section Seq.

  (** *** Dependently-typed natural number sequence *)
  
  Lemma S_add_comm : forall n m, n + S m = S n + m. do 2 intro; lia. Qed.
  Lemma S_mone_inv : forall n, 0 < n -> n = S (n - 1). intro; lia. Qed.
  
  Fixpoint seqd (start len : nat) {struct len} : 0 < start + len -> list { n : nat | n < start + len }.
    refine (match len with
            | 0 => fun _ => nil
            | S len' => fun _ => _
            end).
    refine ((exist _ start (Nat.lt_add_pos_r (S len') start (Nat.lt_0_succ len'))) :: _).
    rewrite (S_add_comm start len').
    rewrite (S_add_comm start len') in l.
    exact (seqd (S start) len' l).
  Defined.

  
End Seq.
