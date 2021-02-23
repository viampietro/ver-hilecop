(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Finite map library *)

(** This file proposes an implementation of the non-dependent interface
 [FMapInterface.WS] using lists of pairs, unordered but without redundancy. *)

Require Import FunInd FMapInterface.

Require Export Bool DecidableType OrderedType.
Set Implicit Arguments.
Unset Strict Implicit.

Import Coq.Structures.Equalities.
Require Import GlobalFacts.

Module Subset (X : UsualDecidableType).
  
  Definition st (Q : X.t -> Prop) := {e | Q e}.

  Section Elt.
    Variable Q : X.t -> Prop.
    Definition eq := @seq X.t Q.
    Definition eq_refl := @seq_refl X.t Q.
    Definition eq_sym := @seq_sym X.t Q.
    Definition eq_trans := @seq_trans X.t Q.
    Definition eq_dec := @seqdec X.t Q X.eq_dec.

    Hint Immediate eq_sym : core.
    Hint Resolve eq_refl eq_trans : core.
  End Elt.

  Hint Unfold eq : core.
  Hint Resolve eq_trans eq_refl : core.
  Hint Immediate eq_sym : core.
End Subset.

Module KeyQDecidableType (Import X:UsualDecidableType).
  
  Module Import SubsetX := Subset X.

  Section Elt.

    Variable Q : t -> Prop.
    Variable elt : Type.
    Notation key := (st Q).

    Definition eqk (p p':key*elt) := eq (fst p) (fst p').
    Definition eqke (p p':key*elt) :=
      eq (fst p) (fst p') /\ (snd p) = (snd p').

    Hint Unfold eqk eqke : core.
    Hint Extern 2 (eqke ?a ?b) => split : core.

    (* eqke is stricter than eqk *)

    Lemma eqke_eqk : forall x x', eqke x x' -> eqk x x'.
    Proof.
      unfold eqk, eqke; intuition.
    Qed.

    (* eqk, eqke are equalities *)

    Lemma eqk_refl : forall e, eqk e e.
    Proof. auto. Qed.

    Lemma eqke_refl : forall e, eqke e e.
    Proof. auto. Qed.

    Lemma eqk_sym : forall e e', eqk e e' -> eqk e' e.
    Proof. auto. Qed.

    Lemma eqke_sym : forall e e', eqke e e' -> eqke e' e.
    Proof. unfold eqke; intuition. Qed.

    Lemma eqk_trans : forall e e' e'', eqk e e' -> eqk e' e'' -> eqk e e''.
    Proof. eauto. Qed.

    Lemma eqke_trans : forall e e' e'', eqke e e' -> eqke e' e'' -> eqke e e''.
    Proof.
      unfold eqke; intuition; [ eauto | congruence ].
    Qed.

    Hint Resolve eqk_trans eqke_trans eqk_refl eqke_refl : core.
    Hint Immediate eqk_sym eqke_sym : core.

    Global Instance eqk_equiv : Equivalence eqk.
    Proof. split; eauto. Qed.

    Global Instance eqke_equiv : Equivalence eqke.
    Proof. split; eauto. Qed.

    Lemma InA_eqke_eqk :
      forall x m, InA eqke x m -> InA eqk x m.
    Proof.
      unfold eqke; induction 1; intuition. 
    Qed.
    Hint Resolve InA_eqke_eqk : core.

    Lemma InA_eqk : forall p q m, eqk p q -> InA eqk p m -> InA eqk q m.
    Proof.
      intros; apply InA_eqA with p; auto using eqk_equiv.
    Qed.

    Definition MapsTo (k:key)(e:elt):= InA eqke (k,e).
    Definition In k m := exists e:elt, MapsTo k e m.

    Hint Unfold MapsTo In : core.

    (* An alternative formulation for [In k l] is [exists e, InA eqk (k,e) l] *)

    Lemma In_alt : forall k l, In k l <-> exists e, InA eqk (k,e) l.
    Proof.
      firstorder.
      exists x; auto.
      induction H.
      destruct y.
      exists e; auto.
      destruct IHInA as [e H0].
      exists e; auto.
    Qed.

    Lemma MapsTo_eq : forall l x y e, eq x y -> MapsTo x e l -> MapsTo y e l.
    Proof.
      intros; unfold MapsTo in *; apply InA_eqA with (x,e); auto using eqke_equiv.
    Qed.

    Lemma In_eq : forall l x y, eq x y -> In x l -> In y l.
    Proof.
      destruct 2 as (e,E); exists e; eapply MapsTo_eq; eauto.
    Qed.

    Lemma In_inv : forall k k' e l, In k ((k',e) :: l) -> eq k k' \/ In k l.
    Proof.
      inversion 1.
      inversion_clear H0; eauto.
      destruct H1; simpl in *; intuition.
    Qed.

    Lemma In_inv_2 : forall k k' e e' l,
        InA eqk (k, e) ((k', e') :: l) -> ~ eq k k' -> InA eqk (k, e) l.
    Proof.
      inversion_clear 1; compute in H0; intuition.
    Qed.

    Lemma In_inv_3 : forall x x' l,
        InA eqke x (x' :: l) -> ~ eqk x x' -> InA eqke x l.
    Proof.
      inversion_clear 1; compute in H0; intuition.
    Qed.

  End Elt.

  Hint Unfold eqk eqke : core.
  Hint Extern 2 (eqke ?a ?b) => split : core.
  Hint Resolve eqk_trans eqke_trans eqk_refl eqke_refl : core.
  Hint Immediate eqk_sym eqke_sym : core.
  Hint Resolve InA_eqke_eqk : core.
  Hint Unfold MapsTo In : core.
  Hint Resolve In_inv_2 In_inv_3 : core.

End KeyQDecidableType.

(** When compared with Ocaml Map, this signature has been split in
    several parts :

   - The first parts [WSfun] and [WS] propose signatures for weak
     maps, which are maps with no ordering on the key type nor the
     data type.  [WSfun] and [WS] are almost identical, apart from the
     fact that [WSfun] is expressed in a functorial way whereas [WS]
     is self-contained. For obtaining an instance of such signatures,
     a decidable equality on keys in enough (see for example
     [FMapWeakList]). These signatures contain the usual operators
     (add, find, ...). The only function that asks for more is
     [equal], whose first argument should be a comparison on data.

   - Then comes [Sfun] and [S], that extend [WSfun] and [WS] to the
     case where the key type is ordered. The main novelty is that
     [elements] is required to produce sorted lists.

   - Finally, [Sord] extends [S] with a complete comparison function. For
     that, the data type should have a decidable total ordering as well.

   If unsure, what you're looking for is probably [S]: apart from [Sord],
   all other signatures are subsets of [S].

   Some additional differences with Ocaml:

    - no [iter] function, useless since Coq is purely functional
    - [option] types are used instead of [Not_found] exceptions
    - more functions are provided: [elements] and [cardinal] and [map2]

*)


Definition Cmp (elt:Type)(cmp:elt->elt->bool) e1 e2 := cmp e1 e2 = true.

(** ** Weak signature for maps

    No requirements for an ordering on keys nor elements, only decidability
    of equality on keys. First, a functorial signature: *)

Module Type WSfun (E : UsualDecidableType).

  Module Import SubsetE := Subset E.
  
  Definition key := st.
  Hint Transparent key : core.

  Parameter t : (E.t -> Prop) -> Type -> Type.
  (** the abstract type of maps *)

  Section Types.

    Variable Q : E.t -> Prop.
    Variable elt:Type.

    Parameter empty : t Q elt.
    (** The empty map. *)

    Parameter is_empty : t Q elt -> bool.
    (** Test whether a map is empty or not. *)

    Parameter add : key Q -> elt -> t Q elt -> t Q elt.
    (** [add x y m] returns a map containing the same bindings as [m],
	plus a binding of [x] to [y]. If [x] was already bound in [m],
	its previous binding disappears. *)

    Parameter find : key Q -> t Q elt -> option elt.
    (** [find x m] returns the current binding of [x] in [m],
	or [None] if no such binding exists. *)

    Parameter remove : key Q -> t Q elt -> t Q elt.
    (** [remove x m] returns a map containing the same bindings as [m],
	except for [x] which is unbound in the returned map. *)

    Parameter mem : key Q -> t Q elt -> bool.
    (** [mem x m] returns [true] if [m] contains a binding for [x],
	and [false] otherwise. *)

    Variable elt' elt'' : Type.

    Parameter map : (elt -> elt') -> t Q elt -> t Q elt'.
    (** [map f m] returns a map with same domain as [m], where the associated
	value a of all bindings of [m] has been replaced by the result of the
	application of [f] to [a]. Since Coq is purely functional, the order
        in which the bindings are passed to [f] is irrelevant. *)

    Parameter mapi : (key Q -> elt -> elt') -> t Q elt -> t Q elt'.
    (** Same as [map], but the function receives as arguments both the
	key and the associated value for each binding of the map. *)

    Parameter map2 :
     (option elt -> option elt' -> option elt'') -> t Q elt -> t Q elt' ->  t Q elt''.
    (** [map2 f m m'] creates a new map whose bindings belong to the ones
        of either [m] or [m']. The presence and value for a key [k] is
        determined by [f e e'] where [e] and [e'] are the (optional) bindings
        of [k] in [m] and [m']. *)

    Parameter elements : t Q elt -> list (key Q * elt).
    (** [elements m] returns an assoc list corresponding to the bindings
        of [m], in any order. *)

    Parameter cardinal : t Q elt -> nat.
    (** [cardinal m] returns the number of bindings in [m]. *)

    Parameter fold : forall A: Type, (key Q -> elt -> A -> A) -> t Q elt -> A -> A.
    (** [fold f m a] computes [(f kN dN ... (f k1 d1 a)...)],
	where [k1] ... [kN] are the keys of all bindings in [m]
	(in any order), and [d1] ... [dN] are the associated data. *)

    Parameter equal : (elt -> elt -> bool) -> t Q elt -> t Q elt -> bool.
    (** [equal cmp m1 m2] tests whether the maps [m1] and [m2] are equal,
      that is, contain equal keys and associate them with equal data.
      [cmp] is the equality predicate used to compare the data associated
      with the keys. *)

    Section Spec.

      Variable m m' m'' : t Q elt.
      Variable x y z : key Q.
      Variable e e' : elt.

      Parameter MapsTo : key Q -> elt -> t Q elt -> Prop.

      Definition In (k:key Q)(m: t Q elt) : Prop := exists e:elt, MapsTo k e m.

      Definition Empty m := forall (a : key Q)(e:elt) , ~ MapsTo a e m.

      Definition eq_key (p p':key Q*elt) := E.eq (proj1_sig (fst p)) (proj1_sig (fst p')).

      Definition eq_key_elt (p p' : key Q * elt) :=
          E.eq (proj1_sig (fst p)) (proj1_sig (fst p')) /\ (snd p) = (snd p').

    (** Specification of [MapsTo] *)
      Parameter MapsTo_1 : E.eq (proj1_sig x) (proj1_sig y) -> MapsTo x e m -> MapsTo y e m.

    (** Specification of [mem] *)
      Parameter mem_1 : In x m -> mem x m = true.
      Parameter mem_2 : mem x m = true -> In x m.

    (** Specification of [empty] *)
      Parameter empty_1 : Empty empty.

    (** Specification of [is_empty] *)
      Parameter is_empty_1 : Empty m -> is_empty m = true.
      Parameter is_empty_2 : is_empty m = true -> Empty m.

    (** Specification of [add] *)
      Parameter add_1 : E.eq (proj1_sig x) (proj1_sig y) -> MapsTo y e (add x e m).
      Parameter add_2 : ~ E.eq (proj1_sig x) (proj1_sig y) -> MapsTo y e m -> MapsTo y e (add x e' m).
      Parameter add_3 : ~ E.eq (proj1_sig x) (proj1_sig y) -> MapsTo y e (add x e' m) -> MapsTo y e m.

    (** Specification of [remove] *)
      Parameter remove_1 : E.eq (proj1_sig x) (proj1_sig y) -> ~ In y (remove x m).
      Parameter remove_2 : ~ E.eq (proj1_sig x) (proj1_sig y) -> MapsTo y e m -> MapsTo y e (remove x m).
      Parameter remove_3 : MapsTo y e (remove x m) -> MapsTo y e m.

    (** Specification of [find] *)
      Parameter find_1 : MapsTo x e m -> find x m = Some e.
      Parameter find_2 : find x m = Some e -> MapsTo x e m.

    (** Specification of [elements] *)
      Parameter elements_1 :
        MapsTo x e m -> InA eq_key_elt (x,e) (elements m).
      Parameter elements_2 :
        InA eq_key_elt (x,e) (elements m) -> MapsTo x e m.
      (** When compared with ordered maps, here comes the only
         property that is really weaker: *)
      Parameter elements_3w : NoDupA eq_key (elements m).

    (** Specification of [cardinal] *)
      Parameter cardinal_1 : cardinal m = length (elements m).

    (** Specification of [fold] *)
      Parameter fold_1 :
	forall (A : Type) (i : A) (f : key Q -> elt -> A -> A),
        fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (elements m) i.

    (** Equality of maps *)

    (** Caveat: there are at least three distinct equality predicates on maps.
      - The simplest (and maybe most natural) way is to consider keys up to
        their equivalence [E.eq], but elements up to Leibniz equality, in
        the spirit of [eq_key_elt] above. This leads to predicate [Equal].
      - Unfortunately, this [Equal] predicate can't be used to describe
        the [equal] function, since this function (for compatibility with
        ocaml) expects a boolean comparison [cmp] that may identify more
        elements than Leibniz. So logical specification of [equal] is done
        via another predicate [Equivb]
      - This predicate [Equivb] is quite ad-hoc with its boolean [cmp],
        it can be generalized in a [Equiv] expecting a more general
        (possibly non-decidable) equality predicate on elements *)

     Definition Equal m m' := forall y, find y m = find y m'.
     Definition Equiv (eq_elt:elt->elt->Prop) m m' :=
         (forall k, In k m <-> In k m') /\
         (forall k e e', MapsTo k e m -> MapsTo k e' m' -> eq_elt e e').
     Definition Equivb (cmp: elt->elt->bool) := Equiv (Cmp cmp).

     (** Specification of [equal] *)

     Variable cmp : elt -> elt -> bool.

     Parameter equal_1 : Equivb cmp m m' -> equal cmp m m' = true.
     Parameter equal_2 : equal cmp m m' = true -> Equivb cmp m m'.

    End Spec.
   End Types.

  (** Specification of [map] *)
  Parameter map_1 : forall (Q:E.t->Prop)(elt elt':Type)(m: t Q elt)(x:key Q)(e:elt)(f:elt->elt'),
      MapsTo x e m -> MapsTo x (f e) (map f m).
  Parameter map_2 : forall (Q:E.t->Prop)(elt elt':Type)(m: t Q elt)(x:key Q)(f:elt->elt'),
      In x (map f m) -> In x m.

  (** Specification of [mapi] *)
  Parameter mapi_1 : forall (Q:E.t->Prop)(elt elt':Type)(m: t Q elt)(x:key Q)(e:elt)
                            (f:key Q->elt->elt'), MapsTo x e m ->
                                                exists y, E.eq (proj1_sig y) (proj1_sig x) /\ MapsTo x (f y e) (mapi f m).
  Parameter mapi_2 : forall (Q:E.t->Prop)(elt elt':Type)(m: t Q elt)(x:key Q)
                            (f:key Q->elt->elt'), In x (mapi f m) -> In x m.
  
  (** Specification of [map2] *)
  Parameter map2_1 : forall (Q:E.t->Prop)(elt elt' elt'':Type)(m: t Q elt)(m': t Q elt')
	                    (x:key Q)(f:option elt->option elt'->option elt''),
      In x m \/ In x m' ->
      find x (map2 f m m') = f (find x m) (find x m').

  Parameter map2_2 : forall (Q:E.t->Prop)(elt elt' elt'':Type)(m: t Q elt)(m': t Q elt')
	                    (x:key Q)(f:option elt->option elt'->option elt''),
      In x (map2 f m m') -> In x m \/ In x m'.

  Hint Immediate MapsTo_1 mem_2 is_empty_2
       map_2 mapi_2 add_3 remove_3 find_2
    : map.
  Hint Resolve mem_1 is_empty_1 is_empty_2 add_1 add_2 remove_1
       remove_2 find_1 fold_1 map_1 mapi_1 mapi_2
    : map.

End WSfun.

(** ** Static signature for Weak Maps

    Similar to [WSfun] but expressed in a self-contained way. *)

Module Type WS.
  Declare Module E : UsualDecidableType.
  Include WSfun E.
End WS.

Module Raw (X:UsualDecidableType).

  Module Import PX := KeyQDecidableType X.
  
  Definition key (Q : X.t -> Prop) := SubsetX.st Q.
  Definition t (Q : X.t -> Prop) (elt:Type) := list (key Q * elt).

  Section Elt.

    Variable Q : X.t -> Prop.  
    Variable elt : Type.

    Notation eqk := (eqk (Q := Q) (elt:=elt)).
    Notation eqke := (eqke (Q := Q) (elt:=elt)).
    Notation MapsTo := (MapsTo (Q := Q) (elt:=elt)).
    Notation In := (In (Q := Q) (elt:=elt)).
    Notation NoDupA := (NoDupA eqk).

    (** * [empty] *)

    Definition empty : t Q elt := nil.

    Definition Empty (m : t Q elt) := forall (a : key Q)(e:elt), ~ MapsTo a e m.

    Lemma empty_1 : Empty empty.
    Proof.
      unfold Empty,empty.
      intros a e.
      intro abs.
      inversion abs.
    Qed.

    Hint Resolve empty_1 : core.

    Lemma empty_NoDup : NoDupA empty.
    Proof.
      unfold empty; auto.
    Qed.

    (** * [is_empty] *)

    Definition is_empty (l : t Q elt) : bool := if l then true else false.

    Lemma is_empty_1 :forall m, Empty m -> is_empty m = true.
    Proof.
      unfold Empty, PX.MapsTo.
      intros m.
      case m;auto.
      intros p l inlist.
      destruct p.
      absurd (InA eqke (k, e) ((k, e) :: l));auto.
    Qed.

    Lemma is_empty_2 : forall m, is_empty m = true -> Empty m.
    Proof.
      intros m.
      case m;auto.
      intros p l abs.
      inversion abs.
    Qed.

    (** * [mem] *)

    Function mem (k : key Q) (s : t Q elt) {struct s} : bool :=
      match s with
      | nil => false
      | (k',_) :: l => if SubsetX.eq_dec k k' then true else mem k l
      end.

    Lemma mem_1 : forall m (Hm:NoDupA m) x, In x m -> mem x m = true.
    Proof.
      intros m Hm x; generalize Hm; clear Hm.
      functional induction (mem x m);intros NoDup belong1;trivial.
      inversion belong1. inversion H.
      inversion_clear NoDup.
      inversion_clear belong1.
      inversion_clear H1.
      compute in H2; destruct H2.
      contradiction.
      apply IHb; auto.
      exists x0; auto.
    Qed.

    Lemma mem_2 : forall m (Hm:NoDupA m) x, mem x m = true -> In x m.
    Proof.
      intros m Hm x; generalize Hm; clear Hm; unfold PX.In,PX.MapsTo.
      functional induction (mem x m); intros NoDup hyp; try discriminate.
      exists _x; auto.
      inversion_clear NoDup.
      destruct IHb; auto.
      exists x0; auto.
    Qed.

    (** * [find] *)

    Function find (k:key Q) (s: t Q elt) {struct s} : option elt :=
      match s with
      | nil => None
      | (k',x)::s' => if SubsetX.eq_dec k k' then Some x else find k s'
      end.

    Lemma find_2 : forall m x e, find x m = Some e -> MapsTo x e m.
    Proof.
      intros m x. unfold PX.MapsTo.
      functional induction (find x m);simpl;intros e' eqfind; inversion eqfind; auto.
    Qed.

    Lemma find_1 : forall m (Hm:NoDupA m) x e,
        MapsTo x e m -> find x m = Some e.
    Proof.
      intros m Hm x e; generalize Hm; clear Hm; unfold PX.MapsTo.
      functional induction (find x m);simpl; subst; try clear H_eq_1.

      inversion 2.

      do 2 inversion_clear 1.
      compute in H2; destruct H2; subst; trivial.
      elim H; apply InA_eqk with (x,e); auto.

      do 2 inversion_clear 1; auto.
      compute in H2; destruct H2; elim _x; auto.
    Qed.

    (* Not part of the exported specifications, used later for [combine]. *)

    Lemma find_eq : forall m (Hm:NoDupA m) x x',
        SubsetX.eq x x' -> find x m = find x' m.
    Proof.
      induction m; simpl; auto; destruct a; intros.
      inversion_clear Hm.
      rewrite (IHm H1 x x'); auto.
      destruct (SubsetX.eq_dec x s) as [|Hneq]; destruct (SubsetX.eq_dec x' s) as [|?Hneq'];
        trivial.
      elim Hneq'; apply SubsetX.eq_trans with x; auto.
      elim Hneq; apply SubsetX.eq_trans with x'; auto.
    Qed.

    (** * [add] *)

    Function add (k : key Q) (x : elt) (s : t Q elt) {struct s} : t Q elt :=
      match s with
      | nil => (k,x) :: nil
      | (k',y) :: l => if SubsetX.eq_dec k k' then (k,x)::l else (k',y)::add k x l
      end.

    Lemma add_1 : forall m x y e, X.eq (proj1_sig x) (proj1_sig y) -> MapsTo y e (add x e m).
    Proof.
      intros m x y e; generalize y; clear y; unfold PX.MapsTo.
      functional induction (add x e m);simpl;auto.
    Qed.

    Lemma add_2 : forall m x y e e',
        ~SubsetX.eq x y -> MapsTo y e m -> MapsTo y e (add x e' m).
    Proof.
      intros m x  y e e'; generalize y e; clear y e; unfold PX.MapsTo.
      functional induction (add x e' m);simpl;auto.
      intros y' e'' eqky';  inversion_clear 1.
      destruct H0; simpl in *.
      elim eqky'; apply SubsetX.eq_trans with k'; auto.
      auto.
      intros y' e'' eqky'; inversion_clear 1; intuition.
    Qed.

    Lemma add_3 : forall m x y e e',
        ~ SubsetX.eq x y -> MapsTo y e (add x e' m) -> MapsTo y e m.
    Proof.
      intros m x y e e'. generalize y e; clear y e; unfold PX.MapsTo.
      functional induction (add x e' m);simpl;auto.
      intros; apply (In_inv_3 H0); auto.
      constructor 2; apply (In_inv_3 H0); auto.
      inversion_clear 2; auto.
    Qed.

    Lemma add_3' : forall m x y e e',
        ~ SubsetX.eq x y -> InA eqk (y,e) (add x e' m) -> InA eqk (y,e) m.
    Proof.
      intros m x y e e'. generalize y e; clear y e.
      functional induction (add x e' m);simpl;auto.
      inversion_clear 2.
      compute in H1; elim H; auto.
      inversion H1.
      constructor 2; inversion_clear H0; auto.
      compute in H1; elim H; auto.
      inversion_clear 2; auto.
    Qed.

    Lemma add_NoDup : forall m (Hm:NoDupA m) x e, NoDupA (add x e m).
    Proof.
      induction m.
      simpl; constructor; auto; red; inversion 1.
      intros.
      destruct a as (x',e').
      simpl; case (SubsetX.eq_dec x x'); inversion_clear Hm; auto.
      constructor; auto.
      contradict H.
      apply InA_eqk with (x,e); auto.
      constructor; auto.
      contradict H; apply add_3' with x e; auto.
    Qed.

    (* Not part of the exported specifications, used later for [combine]. *)

    Lemma add_eq : forall m (Hm:NoDupA m) x a e,
        SubsetX.eq x a -> find x (add a e m) = Some e.
    Proof.
      intros.
      apply find_1; auto.
      apply add_NoDup; auto.
      apply add_1; symmetry; auto.
    Qed.

    Lemma add_not_eq : forall m (Hm:NoDupA m) x a e,
        ~SubsetX.eq x a -> find x (add a e m) = find x m.
    Proof.
      intros.
      case_eq (find x m); intros.
      apply find_1; auto.
      apply add_NoDup; auto.
      apply add_2; auto.
      apply find_2; auto.
      case_eq (find x (add a e m)); intros; auto.
      rewrite <- H0; symmetry.
      apply find_1; auto.
      apply add_3 with a e; auto.
      apply find_2; auto.
    Qed.


    (** * [remove] *)

    Function remove (k : key Q) (s : t Q elt) {struct s} : t Q elt :=
      match s with
      | nil => nil
      | (k',x) :: l => if SubsetX.eq_dec k k' then l else (k',x) :: remove k l
      end.

    Lemma remove_1 : forall m (Hm:NoDupA m) x y, SubsetX.eq x y -> ~ In y (remove x m).
    Proof.
      intros m Hm x y; generalize Hm; clear Hm.
      functional induction (remove x m);simpl;intros;auto.

      red; inversion 1; inversion H1.

      inversion_clear Hm.
      subst.
      contradict H0.
      destruct H0 as (e,H2); unfold PX.MapsTo in H2.
      apply InA_eqk with (y,e); auto.
      compute; apply SubsetX.eq_trans with x; auto.

      intro H2.
      destruct H2 as (e,H2); inversion_clear H2.
      compute in H0; destruct H0.
      elim _x; apply SubsetX.eq_trans with y; auto.
      inversion_clear Hm.
      elim (IHt0 H2 H).
      exists e; auto.
    Qed.

    Lemma remove_2 : forall m (Hm:NoDupA m) x y e,
        ~ SubsetX.eq x y -> MapsTo y e m -> MapsTo y e (remove x m).
    Proof.
      intros m Hm x y e; generalize Hm; clear Hm; unfold PX.MapsTo.
      functional induction (remove x m);auto.
      inversion_clear 3; auto.
      compute in H1; destruct H1.
      elim H; apply SubsetX.eq_trans with k'; auto.

      inversion_clear 1; inversion_clear 2; auto.
    Qed.

    Lemma remove_3 : forall m (Hm:NoDupA m) x y e,
        MapsTo y e (remove x m) -> MapsTo y e m.
    Proof.
      intros m Hm x y e; generalize Hm; clear Hm; unfold PX.MapsTo.
      functional induction (remove x m);auto.
      do 2 inversion_clear 1; auto.
    Qed.

    Lemma remove_3' : forall m (Hm:NoDupA m) x y e,
        InA eqk (y,e) (remove x m) -> InA eqk (y,e) m.
    Proof.
      intros m Hm x y e; generalize Hm; clear Hm; unfold PX.MapsTo.
      functional induction (remove x m);auto.
      do 2 inversion_clear 1; auto.
    Qed.

    Lemma remove_NoDup : forall m (Hm:NoDupA m) x, NoDupA (remove x m).
    Proof.
      induction m.
      simpl; intuition.
      intros.
      inversion_clear Hm.
      destruct a as (x',e').
      simpl; case (SubsetX.eq_dec x x'); auto.
      constructor; auto.
      contradict H; apply remove_3' with x; auto.
    Qed.

    (** * [elements] *)

    Definition elements (m: t Q elt) := m.

    Lemma elements_1 : forall m x e, MapsTo x e m -> InA eqke (x,e) (elements m).
    Proof.
      auto.
    Qed.

    Lemma elements_2 : forall m x e, InA eqke (x,e) (elements m) -> MapsTo x e m.
    Proof.
      auto.
    Qed.

    Lemma elements_3w : forall m (Hm:NoDupA m), NoDupA (elements m).
    Proof.
      auto.
    Qed.

    (** * [fold] *)

    Function fold (A:Type)(f:key Q->elt->A->A)(m:t Q elt) (acc : A) {struct m} :  A :=
      match m with
      | nil => acc
      | (k,e)::m' => fold f m' (f k e acc)
      end.

    Lemma fold_1 : forall m (A:Type)(i:A)(f:key Q->elt->A->A),
        fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (elements m) i.
    Proof.
      intros; functional induction (@fold A f m i); auto.
    Qed.

    (** * [equal] *)

    Definition check (cmp : elt -> elt -> bool)(k:key Q)(e:elt)(m': t Q elt) :=
      match find k m' with
      | None => false
      | Some e' => cmp e e'
      end.

    Definition submap (cmp : elt -> elt -> bool)(m m' : t Q elt) : bool :=
      fold (fun k e b => andb (check cmp k e m') b) m true.

    Definition equal (cmp : elt -> elt -> bool)(m m' : t Q elt) : bool :=
      andb (submap cmp m m') (submap (fun e' e => cmp e e') m' m).

    Definition Submap cmp m m' :=
      (forall k, In k m -> In k m') /\
      (forall k e e', MapsTo k e m -> MapsTo k e' m' -> cmp e e' = true).

    Definition Equivb cmp m m' :=
      (forall k, In k m <-> In k m') /\
      (forall k e e', MapsTo k e m -> MapsTo k e' m' -> cmp e e' = true).

    Lemma submap_1 : forall m (Hm:NoDupA m) m' (Hm': NoDupA m') cmp,
        Submap cmp m m' -> submap cmp m m' = true.
    Proof.
      unfold Submap, submap.
      induction m.
      simpl; auto.
      destruct a; simpl; intros.
      destruct H.
      inversion_clear Hm.
      assert (H3 : In s m').
      apply H; exists e; auto.
      destruct H3 as (e', H3).
      unfold check at 2; rewrite (find_1 Hm' H3).
      rewrite (H0 s); simpl; auto.
      eapply IHm; auto.
      split; intuition.
      apply H.
      destruct H5 as (e'',H5); exists e''; auto.
      apply H0 with k; auto.
    Qed.

    Lemma submap_2 : forall m (Hm:NoDupA m) m' (Hm': NoDupA m') cmp,
        submap cmp m m' = true -> Submap cmp m m'.
    Proof.
      unfold Submap, submap.
      induction m.
      simpl; auto.
      intuition.
      destruct H0; inversion H0.
      inversion H0.

      destruct a; simpl; intros.
      inversion_clear Hm.
      rewrite andb_b_true in H.
      assert (check cmp s e m' = true).
      clear H1 H0 Hm' IHm.
      set (b:=check cmp s e m') in *.
      generalize H; clear H; generalize b; clear b.
      induction m; simpl; auto; intros.
      destruct a; simpl in *.
      destruct (andb_prop _ _ (IHm _ H)); auto.
      rewrite H2 in H.
      destruct (IHm H1 m' Hm' cmp H); auto.
      unfold check in H2.
      case_eq (find s m'); [intros e' H5 | intros H5];
        rewrite H5 in H2; try discriminate.
      split; intros.
      destruct H6 as (e0,H6); inversion_clear H6.
      compute in H7; destruct H7; subst.
      exists e'.
      apply PX.MapsTo_eq with s; auto.
      apply find_2; auto.
      apply H3.
      exists e0; auto.
      inversion_clear H6.
      compute in H8; destruct H8; subst.
      rewrite (find_1 Hm' (PX.MapsTo_eq H6 H7)) in H5; congruence.
      apply H4 with k; auto.
    Qed.

    (** Specification of [equal] *)

    Lemma equal_1 : forall m (Hm:NoDupA m) m' (Hm': NoDupA m') cmp,
        Equivb cmp m m' -> equal cmp m m' = true.
    Proof.
      unfold Equivb, equal.
      intuition.
      apply andb_true_intro; split; apply submap_1; unfold Submap; firstorder.
    Qed.

    Lemma equal_2 : forall m (Hm:NoDupA m) m' (Hm':NoDupA m') cmp,
        equal cmp m m' = true -> Equivb cmp m m'.
    Proof.
      unfold Equivb, equal.
      intros.
      destruct (andb_prop _ _ H); clear H.
      generalize (submap_2 Hm Hm' H0).
      generalize (submap_2 Hm' Hm H1).
      firstorder.
    Qed.

    Variable elt':Type.

    (** * [map] and [mapi] *)

    Fixpoint map (f:elt -> elt') (m:t Q elt) : t Q elt' :=
      match m with
      | nil => nil
      | (k,e)::m' => (k,f e) :: map f m'
      end.

    Fixpoint mapi (f: key Q -> elt -> elt') (m:t Q elt) : t Q elt' :=
      match m with
      | nil => nil
      | (k,e)::m' => (k,f k e) :: mapi f m'
      end.

  End Elt.
  Section Elt2.

    Variable Q : X.t -> Prop.
    
    (* A new section is necessary for previous definitions to work
   with different [elt], especially [MapsTo]... *)

    Variable elt elt' : Type.

    (** Specification of [map] *)

    Lemma map_1 : forall (m:t Q elt)(x:key Q)(e:elt)(f:elt->elt'),
        MapsTo x e m -> MapsTo x (f e) (map f m).
    Proof.
      intros m x e f.
      (* functional induction map elt elt' f m.  *) (* Marche pas ??? *)
      induction m.
      inversion 1.

      destruct a as (x',e').
      simpl.
      inversion_clear 1.
      constructor 1.
      unfold eqke in *; simpl in *; intuition congruence.
      constructor 2.
      unfold MapsTo in *; auto.
    Qed.

    Lemma map_2 : forall (m:t Q elt)(x:key Q)(f:elt->elt'),
        In x (map f m) -> In x m.
    Proof.
      intros m x f.
      (* functional induction map elt elt' f m. *) (* Marche pas ??? *)
      induction m; simpl.
      intros (e,abs).
      inversion abs.

      destruct a as (x',e).
      intros hyp.
      inversion hyp. clear hyp.
      inversion H; subst; rename x0 into e'.
      exists e; constructor.
      unfold eqke in *; simpl in *; intuition.
      destruct IHm as (e'',hyp).
      exists e'; auto.
      exists e''.
      constructor 2; auto.
    Qed.

    Lemma map_NoDup : forall m (Hm : NoDupA (@eqk Q elt) m)(f:elt->elt'),
        NoDupA (@eqk Q elt') (map f m).
    Proof.
      induction m; simpl; auto.
      intros.
      destruct a as (x',e').
      inversion_clear Hm.
      constructor; auto.
      contradict H.
      (* il faut un map_1 avec eqk au lieu de eqke *)
      clear IHm H0.
      induction m; simpl in *; auto.
      inversion H.
      destruct a; inversion H; auto.
    Qed.

    (** Specification of [mapi] *)

    Lemma mapi_1 : forall (m:t Q elt)(x:key Q)(e:elt)(f:key Q->elt->elt'),
        MapsTo x e m ->
        exists y, SubsetX.eq y x /\ MapsTo x (f y e) (mapi f m).
    Proof.
      intros m x e f.
      (* functional induction mapi elt elt' f m. *) (* Marche pas ??? *)
      induction m.
      inversion 1.

      destruct a as (x',e').
      simpl.
      inversion_clear 1.
      exists x'.
      destruct H0; simpl in *.
      split; auto.
      constructor 1.
      unfold eqke in *; simpl in *; intuition congruence.
      destruct IHm as (y, hyp); auto.
      exists y; intuition.
    Qed.

    Lemma mapi_2 : forall (m:t Q elt)(x:key Q)(f:key Q->elt->elt'),
        In x (mapi f m) -> In x m.
    Proof.
      intros m x f.
      (* functional induction mapi elt elt' f m. *) (* Marche pas ??? *)
      induction m; simpl.
      intros (e,abs).
      inversion abs.

      destruct a as (x',e).
      intros hyp.
      inversion hyp. clear hyp.
      inversion H; subst; rename x0 into e'.
      exists e; constructor.
      unfold eqke in *; simpl in *; intuition.
      destruct IHm as (e'',hyp).
      exists e'; auto.
      exists e''.
      constructor 2; auto.
    Qed.

    Lemma mapi_NoDup : forall m (Hm : NoDupA (@eqk Q elt) m)(f: key Q->elt->elt'),
        NoDupA (@eqk Q elt') (mapi f m).
    Proof.
      induction m; simpl; auto.
      intros.
      destruct a as (x',e').
      inversion_clear Hm; auto.
      constructor; auto.
      contradict H.
      clear IHm H0.
      induction m; simpl in *; auto.
      inversion_clear H.
      destruct a; inversion_clear H; auto.
    Qed.

  End Elt2.
  Section Elt3.
    Variable Q : X.t -> Prop.
    Variable elt elt' elt'' : Type.

    Notation oee' := (option elt * option elt')%type.

    Definition combine_l (m:t Q elt)(m':t Q elt') : t Q oee' :=
      mapi (fun k e => (Some e, find k m')) m.

    Definition combine_r (m:t Q elt)(m':t Q elt') : t Q oee' :=
      mapi (fun k e' => (find k m, Some e')) m'.

    Definition fold_right_pair (A B C:Type)(f:A->B->C->C) :=
      List.fold_right (fun p => f (fst p) (snd p)).

    Definition combine (m:t Q elt)(m':t Q elt') : t Q oee' :=
      let l := combine_l m m' in
      let r := combine_r m m' in
      fold_right_pair (add (elt:=oee')) r l.

    Lemma fold_right_pair_NoDup :
      forall l r (Hl: NoDupA (eqk (elt:=oee')) l)
             (Hl: NoDupA (eqk (elt:=oee')) r),
        NoDupA (eqk (Q := Q) (elt:=oee')) (fold_right_pair (add (elt:=oee')) r l).
    Proof.
      induction l; simpl; auto.
      destruct a; simpl; auto.
      inversion_clear 1.
      intros; apply add_NoDup; auto.
    Qed.
    Hint Resolve fold_right_pair_NoDup : core.

    Lemma combine_NoDup :
      forall m (Hm:NoDupA (@eqk Q elt) m) m' (Hm':NoDupA (@eqk Q elt') m'),
        NoDupA (@eqk Q oee') (combine m m').
    Proof.
      unfold combine, combine_r, combine_l.
      intros.
      set (f1 := fun (k : key Q) (e : elt) => (Some e, find k m')).
      set (f2 := fun (k : key Q) (e' : elt') => (find k m, Some e')).
      generalize (mapi_NoDup Hm f1).
      generalize (mapi_NoDup Hm' f2).
      set (l := mapi f1 m); clearbody l.
      set (r := mapi f2 m'); clearbody r.
      auto.
    Qed.

    Definition at_least_left (o:option elt)(o':option elt') :=
      match o with
      | None => None
      | _  => Some (o,o')
      end.

    Definition at_least_right (o:option elt)(o':option elt') :=
      match o' with
      | None => None
      | _  => Some (o,o')
      end.

    Lemma combine_l_1 :
      forall m (Hm:NoDupA (@eqk Q elt) m) m' (Hm':NoDupA (@eqk Q elt') m')(x:key Q),
        find x (combine_l m m') = at_least_left (find x m) (find x m').
    Proof.
      unfold combine_l.
      intros.
      case_eq (find x m); intros.
      simpl.
      apply find_1.
      apply mapi_NoDup; auto.
      destruct (mapi_1 (fun k e => (Some e, find k m')) (find_2 H)) as (y,(H0,H1)).
      rewrite (find_eq Hm' (SubsetX.eq_sym H0)); auto.
      simpl.
      case_eq (find x (mapi (fun k e => (Some e, find k m')) m)); intros; auto.
      destruct (@mapi_2 _ _ _ m x (fun k e => (Some e, find k m'))).
      exists p; apply find_2; auto.
      rewrite (find_1 Hm H1) in H; discriminate.
    Qed.

    Lemma combine_r_1 :
      forall m (Hm:NoDupA (@eqk Q elt) m) m' (Hm':NoDupA (@eqk Q elt') m')(x:key Q),
        find x (combine_r m m') = at_least_right (find x m) (find x m').
    Proof.
      unfold combine_r.
      intros.
      case_eq (find x m'); intros.
      simpl.
      apply find_1.
      apply mapi_NoDup; auto.
      destruct (mapi_1 (fun k e => (find k m, Some e)) (find_2 H)) as (y,(H0,H1)).
      rewrite (find_eq Hm (SubsetX.eq_sym H0)); auto.
      simpl.
      case_eq (find x (mapi (fun k e' => (find k m, Some e')) m')); intros; auto.
      destruct (@mapi_2 _ _ _ m' x (fun k e' => (find k m, Some e'))).
      exists p; apply find_2; auto.
      rewrite (find_1 Hm' H1) in H; discriminate.
    Qed.

    Definition at_least_one (o:option elt)(o':option elt') :=
      match o, o' with
      | None, None => None
      | _, _  => Some (o,o')
      end.

    Lemma combine_1 :
      forall m (Hm:NoDupA (@eqk Q elt) m) m' (Hm':NoDupA (@eqk Q elt') m')(x:key Q),
        find x (combine m m') = at_least_one (find x m) (find x m').
    Proof.
      unfold combine.
      intros.
      generalize (combine_r_1 Hm Hm' x).
      generalize (combine_l_1 Hm Hm' x).
      assert (NoDupA (eqk (elt:=oee')) (combine_l m m')).
      unfold combine_l; apply mapi_NoDup; auto.
      assert (NoDupA (eqk (elt:=oee')) (combine_r m m')).
      unfold combine_r; apply mapi_NoDup; auto.
      set (l := combine_l m m') in *; clearbody l.
      set (r := combine_r m m') in *; clearbody r.
      set (o := find x m); clearbody o.
      set (o' := find x m'); clearbody o'.
      clear Hm' Hm m m'.
      induction l.
      destruct o; destruct o'; simpl; intros; discriminate || auto.
      destruct a; simpl in *; intros.
      destruct (SubsetX.eq_dec x k); simpl in *.
      unfold at_least_left in H1.
      destruct o; simpl in *; try discriminate.
      inversion H1; subst.
      apply add_eq; auto.
      inversion_clear H; auto.
      inversion_clear H.
      rewrite <- IHl; auto.
      apply add_not_eq; auto.
    Qed.

    Variable f : option elt -> option elt' -> option elt''.

    Definition option_cons (A:Type)(k:key Q)(o:option A)(l:list (key Q*A)) :=
      match o with
      | Some e => (k,e)::l
      | None => l
      end.

    Definition map2 m m' :=
      let m0 : t Q oee' := combine m m' in
      let m1 : t Q (option elt'') := map (fun p => f (fst p) (snd p)) m0 in
      fold_right_pair (option_cons (A:=elt'')) nil m1.

    Lemma map2_NoDup :
      forall m (Hm:NoDupA (@eqk Q elt) m) m' (Hm':NoDupA (@eqk Q elt') m'),
        NoDupA (@eqk Q elt'') (map2 m m').
    Proof.
      intros.
      unfold map2.
      assert (H0:=combine_NoDup Hm Hm').
      set (l0:=combine m m') in *; clearbody l0.
      set (f':= fun p : oee' => f (fst p) (snd p)).
      assert (H1:=map_NoDup (elt' := option elt'') H0 f').
      set (l1:=map f' l0) in *; clearbody l1.
      clear f' f H0 l0 Hm Hm' m m'.
      induction l1.
      simpl; auto.
      inversion_clear H1.
      destruct a; destruct o; simpl; auto.
      constructor; auto.
      contradict H.
      clear IHl1.
      induction l1.
      inversion H.
      inversion_clear H0.
      destruct a; destruct o; simpl in *; auto.
      inversion_clear H; auto.
    Qed.

    Definition at_least_one_then_f (o:option elt)(o':option elt') :=
      match o, o' with
      | None, None => None
      | _, _  => f o o'
      end.

    Lemma map2_0 :
      forall m (Hm:NoDupA (@eqk Q elt) m) m' (Hm':NoDupA (@eqk Q elt') m')(x:key Q),
        find x (map2 m m') = at_least_one_then_f (find x m) (find x m').
    Proof.
      intros.
      unfold map2.
      assert (H:=combine_1 Hm Hm' x).
      assert (H2:=combine_NoDup Hm Hm').
      set (f':= fun p : oee' => f (fst p) (snd p)).
      set (m0 := combine m m') in *; clearbody m0.
      set (o:=find x m) in *; clearbody o.
      set (o':=find x m') in *; clearbody o'.
      clear Hm Hm' m m'.
      generalize H; clear H.
      match goal with |- ?m=?n -> ?p=?q =>
                      assert ((m=n->p=q)/\(m=None -> p=None)); [|intuition] end.
      induction m0; simpl in *; intuition.
      destruct o; destruct o'; simpl in *; try discriminate; auto.
      destruct a as (k,(oo,oo')); simpl in *.
      inversion_clear H2.
      destruct (SubsetX.eq_dec x k) as [|Hneq]; simpl in *.
      (* x = k *)
      assert (at_least_one_then_f o o' = f oo oo').
      destruct o; destruct o'; simpl in *; inversion_clear H; auto.
      rewrite H2.
      unfold f'; simpl.
      destruct (f oo oo'); simpl.
      destruct (SubsetX.eq_dec x k) as [|Hneq]; try contradict Hneq; auto.
      destruct (IHm0 H1) as (_,H4); apply H4; auto.
      case_eq (find x m0); intros; auto.
      elim H0.
      apply InA_eqk with (x,p); auto.
      apply InA_eqke_eqk.
      exact (find_2 H3).
      (* k < x *)
      unfold f'; simpl.
      destruct (f oo oo'); simpl.
      destruct (SubsetX.eq_dec x k); [ contradict Hneq; auto | auto].
      destruct (IHm0 H1) as (H3,_); apply H3; auto.
      destruct (IHm0 H1) as (H3,_); apply H3; auto.

      (* None -> None *)
      destruct a as (k,(oo,oo')).
      simpl.
      inversion_clear H2.
      destruct (SubsetX.eq_dec x k) as [|Hneq].
      (* x = k *)
      discriminate.
      (* k < x *)
      unfold f'; simpl.
      destruct (f oo oo'); simpl.
      destruct (SubsetX.eq_dec x k); [ contradict Hneq; auto | auto].
      destruct (IHm0 H1) as (_,H4); apply H4; auto.
      destruct (IHm0 H1) as (_,H4); apply H4; auto.
    Qed.

    (** Specification of [map2] *)
    Lemma map2_1 :
      forall m (Hm:NoDupA (@eqk Q elt) m) m' (Hm':NoDupA (@eqk Q elt') m')(x:key Q),
        In x m \/ In x m' ->
        find x (map2 m m') = f (find x m) (find x m').
    Proof.
      intros.
      rewrite map2_0; auto.
      destruct H as [(e,H)|(e,H)].
      rewrite (find_1 Hm H).
      destruct (find x m'); simpl; auto.
      rewrite (find_1 Hm' H).
      destruct (find x m); simpl; auto.
    Qed.

    Lemma map2_2 :
      forall m (Hm:NoDupA (@eqk Q elt) m) m' (Hm':NoDupA (@eqk Q elt') m')(x:key Q ),
        In x (map2 m m') -> In x m \/ In x m'.
    Proof.
      intros.
      destruct H as (e,H).
      generalize (map2_0 Hm Hm' x).
      rewrite (find_1 (map2_NoDup Hm Hm') H).
      generalize (@find_2 _ _ m x).
      generalize (@find_2 _ _ m' x).
      destruct (find x m);
        destruct (find x m'); simpl; intros.
      left; exists e0; auto.
      left; exists e0; auto.
      right; exists e0; auto.
      discriminate.
    Qed.

  End Elt3.
End Raw.


Module Make (X: UsualDecidableType) <: WS with Module E:=X.
  Module Raw := Raw X.
  Module E := X.
  Module PX := Raw.PX.
  Module SubsetE := PX.SubsetX.
  
  Definition key (Q : X.t -> Prop) := PX.SubsetX.st Q.
  Record slist (Q : X.t -> Prop) (elt:Type) :=
    {this :> Raw.t Q elt; NoDup : NoDupA (@Raw.PX.eqk Q elt) this}.
  Definition t (Q : X.t -> Prop) (elt:Type) := slist Q elt.

  Section Elt.
    Variable Q : X.t -> Prop.
    Variable elt elt' elt'':Type.

    Implicit Types m : t Q elt.
    Implicit Types x y : key Q.
    Implicit Types e : elt.

    Definition empty : t Q elt := Build_slist (Raw.empty_NoDup Q elt).
    Definition is_empty m : bool := Raw.is_empty (this m).
    Definition add x e m : t Q elt := Build_slist (Raw.add_NoDup (NoDup m) x e).
    Definition find x m : option elt := Raw.find x (this m).
    Definition remove x m : t Q elt := Build_slist (Raw.remove_NoDup (NoDup m) x).
    Definition mem x m : bool := Raw.mem x (this m).
    Definition map f m : t Q elt' := Build_slist (Raw.map_NoDup (NoDup m) f).
    Definition mapi (f:key Q->elt->elt') m : t Q elt' := Build_slist (Raw.mapi_NoDup (NoDup m) f).
    Definition map2 f m (m':t Q elt') : t Q elt'' :=
      Build_slist (Raw.map2_NoDup f (NoDup m) (NoDup m')).
    Definition elements m : list (key Q*elt) := @Raw.elements Q elt (this m).
    Definition cardinal m := length (this m).
    Definition fold (A:Type)(f:key Q->elt->A->A) m (i:A) : A := @Raw.fold Q elt A f (this m) i.
    Definition equal cmp m m' : bool := @Raw.equal Q elt cmp (this m) (this m').
    Definition MapsTo x e m : Prop := Raw.PX.MapsTo x e (this m).
    Definition In x m : Prop := Raw.PX.In x (this m).
    Definition Empty m : Prop := Raw.Empty (this m).

    Definition Equal m m' := forall y, find y m = find y m'.
    Definition Equiv (eq_elt:elt->elt->Prop) m m' :=
      (forall k, In k m <-> In k m') /\
      (forall k e e', MapsTo k e m -> MapsTo k e' m' -> eq_elt e e').
    Definition Equivb cmp m m' : Prop := @Raw.Equivb Q elt cmp (this m) (this m').

    Definition eq_key : (key Q*elt) -> (key Q*elt) -> Prop := @Raw.PX.eqk Q elt.
    Definition eq_key_elt : (key Q*elt) -> (key Q*elt) -> Prop:= @Raw.PX.eqke Q elt.

    Lemma MapsTo_1 : forall m x y e, PX.SubsetX.eq x y -> MapsTo x e m -> MapsTo y e m.
    Proof. intros m; exact (@Raw.PX.MapsTo_eq Q elt (this m)). Qed.

    Lemma mem_1 : forall m x, In x m -> mem x m = true.
    Proof. intros m; exact (@Raw.mem_1 Q elt (this m) (NoDup m)). Qed.
    Lemma mem_2 : forall m x, mem x m = true -> In x m.
    Proof. intros m; exact (@Raw.mem_2 Q elt (this m) (NoDup m)). Qed.

    Lemma empty_1 : Empty empty.
    Proof. exact (@Raw.empty_1 Q elt). Qed.

    Lemma is_empty_1 : forall m, Empty m -> is_empty m = true.
    Proof. intros m; exact (@Raw.is_empty_1 Q elt (this m)). Qed.
    Lemma is_empty_2 :  forall m, is_empty m = true -> Empty m.
    Proof. intros m; exact (@Raw.is_empty_2 Q elt (this m)). Qed.

    Lemma add_1 : forall m x y e, PX.SubsetX.eq x y -> MapsTo y e (add x e m).
    Proof. intros m; exact (@Raw.add_1 Q elt (this m)). Qed.
    Lemma add_2 : forall m x y e e', ~ PX.SubsetX.eq x y -> MapsTo y e m -> MapsTo y e (add x e' m).
    Proof. intros m; exact (@Raw.add_2 Q elt (this m)). Qed.
    Lemma add_3 : forall m x y e e', ~ PX.SubsetX.eq x y -> MapsTo y e (add x e' m) -> MapsTo y e m.
    Proof. intros m; exact (@Raw.add_3 Q elt (this m)). Qed.

    Lemma remove_1 : forall m x y, PX.SubsetX.eq x y -> ~ In y (remove x m).
    Proof. intros m; exact (@Raw.remove_1 Q elt (this m) (NoDup m)). Qed.
    Lemma remove_2 : forall m x y e, ~ PX.SubsetX.eq x y -> MapsTo y e m -> MapsTo y e (remove x m).
    Proof. intros m; exact (@Raw.remove_2 Q elt (this m) (NoDup m)). Qed.
    Lemma remove_3 : forall m x y e, MapsTo y e (remove x m) -> MapsTo y e m.
    Proof. intros m; exact (@Raw.remove_3 Q elt (this m) (NoDup m)). Qed.

    Lemma find_1 : forall m x e, MapsTo x e m -> find x m = Some e.
    Proof. intros m; exact (@Raw.find_1 Q elt (this m) (NoDup m)). Qed.
    Lemma find_2 : forall m x e, find x m = Some e -> MapsTo x e m.
    Proof. intros m; exact (@Raw.find_2 Q elt (this m)). Qed.

    Lemma elements_1 : forall m x e, MapsTo x e m -> InA eq_key_elt (x,e) (elements m).
    Proof. intros m; exact (@Raw.elements_1 Q elt (this m)). Qed.
    Lemma elements_2 : forall m x e, InA eq_key_elt (x,e) (elements m) -> MapsTo x e m.
    Proof. intros m; exact (@Raw.elements_2 Q elt (this m)). Qed.
    Lemma elements_3w : forall m, NoDupA eq_key (elements m).
    Proof. intros m; exact (@Raw.elements_3w Q elt (this m) (NoDup m)). Qed.

    Lemma cardinal_1 : forall m, cardinal m = length (elements m).
    Proof. intros; reflexivity. Qed.

    Lemma fold_1 : forall m (A : Type) (i : A) (f : key Q -> elt -> A -> A),
        fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (elements m) i.
    Proof. intros m; exact (@Raw.fold_1 Q elt (this m)). Qed.

    Lemma equal_1 : forall m m' cmp, Equivb cmp m m' -> equal cmp m m' = true.
    Proof. intros m m'; exact (@Raw.equal_1 Q elt (this m) (NoDup m) (this m') (NoDup m')). Qed.
    Lemma equal_2 : forall m m' cmp, equal cmp m m' = true -> Equivb cmp m m'.
    Proof. intros m m'; exact (@Raw.equal_2 Q elt (this m) (NoDup m) (this m') (NoDup m')). Qed.

  End Elt.

  Lemma map_1 : forall (Q : X.t -> Prop) (elt elt':Type)(m: t Q elt)(x:key Q)(e:elt)(f:elt->elt'),
      MapsTo x e m -> MapsTo x (f e) (map f m).
  Proof. intros Q elt elt' m; exact (@Raw.map_1 Q elt elt' (this m)). Qed.
  Lemma map_2 : forall (Q : X.t -> Prop)  (elt elt':Type)(m: t Q elt)(x:key Q)(f:elt->elt'),
      In x (map f m) -> In x m.
  Proof. intros Q elt elt' m; exact (@Raw.map_2 Q elt elt' (this m)). Qed.

  Lemma mapi_1 : forall (Q : X.t -> Prop) (elt elt':Type)(m: t Q elt)(x:key Q)(e:elt)
                        (f:key Q->elt->elt'), MapsTo x e m ->
                                            exists y, PX.SubsetX.eq y x /\ MapsTo x (f y e) (mapi f m).
  Proof. intros Q elt elt' m; exact (@Raw.mapi_1 Q elt elt' (this m)). Qed.
  Lemma mapi_2 : forall (Q : X.t -> Prop)  (elt elt':Type)(m: t Q elt)(x:key Q)
                        (f:key Q->elt->elt'), In x (mapi f m) -> In x m.
  Proof. intros Q elt elt' m; exact (@Raw.mapi_2 Q elt elt' (this m)). Qed.

  Lemma map2_1 : forall (Q : X.t -> Prop)  (elt elt' elt'':Type)(m: t Q elt)(m': t Q elt')
	                (x:key Q)(f:option elt->option elt'->option elt''),
      In x m \/ In x m' ->
      find x (map2 f m m') = f (find x m) (find x m').
  Proof.
    intros Q elt elt' elt'' m m' x f;
      exact (@Raw.map2_1 Q elt elt' elt'' f (this m) (NoDup m) (this m') (NoDup m') x).
  Qed.
  Lemma map2_2 : forall (Q : X.t -> Prop)  (elt elt' elt'':Type)(m: t Q elt)(m': t Q elt')
	                (x:key Q)(f:option elt->option elt'->option elt''),
      In x (map2 f m m') -> In x m \/ In x m'.
  Proof.
    intros Q elt elt' elt'' m m' x f;
      exact (@Raw.map2_2 Q elt elt' elt'' f (this m) (NoDup m) (this m') (NoDup m') x).
  Qed.

End Make.

Require Import Coq.Structures.OrdersEx.
Module NatSubsetMap := Make Nat_as_DT.

Section MySection.
  Variable n : nat.
  
  Definition GtN := NatSubsetMap.t (fun m => m > n).
  
  Variable o_gt_n : 1 > n.

  Definition ogtn := exist _ 1 o_gt_n.
  Definition map_gtn : GtN bool := NatSubsetMap.add ogtn true (NatSubsetMap.empty _ _).
  
End MySection.
