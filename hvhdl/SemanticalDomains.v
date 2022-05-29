(** * Semantical domains for H-VHDL *)

(** Module defining the semantical domains used in H-VHDL
    simulation semantics. *)

Require Import common.CoqLib.
Require Import common.GlobalTypes.
Require Import common.ListLib.
Require Import String.

Import ErrMonadNotations.

Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.HVhdlTypes.

Open Scope N_scope.

(** ** Value type and functions about values *)

Section Values.

  (** Defines the type of values used to express the semantics of the
      H-VHDL language.

      A value is either a boolean, a natural number, an array of
      values. *)

  Inductive value : Type :=
  | Vbool : bool -> value
  | Vnat : N -> value
  | Varr : arrofvalues -> value
                            
  with arrofvalues : Type :=
  | Arr_one : value -> arrofvalues
  | Arr_cons : value -> arrofvalues -> arrofvalues.

  Scheme value_ind_mut := Induction for value Sort Prop
      with arrofvalues_ind_mut := Induction for arrofvalues Sort Prop.

  (* Conversion from [arrofvalues] to [list value] *)

  Fixpoint aofv2list (aofv : arrofvalues) {struct aofv} : list (value) :=
    match aofv with
    | Arr_one v => [v]
    | Arr_cons v tl => v :: aofv2list tl
    end.

  Coercion aofv2list : arrofvalues >-> list.

  (** Accesses the element at position [i] in arrofvalues [aofv]. 
    
    Returns an error (i.e, None) if the index is greater
    than the list length.
   *)

  Fixpoint oget_at (i : nat) (aofv : arrofvalues) {struct aofv} : option value :=
    match i, aofv with
    (* Error, index out of bounds. *)
    | S _, Arr_one v => None
    | 0%nat, Arr_one v => Some v
    | 0%nat, Arr_cons v aofv' => Some v
    | S j, Arr_cons a aofv' => oget_at j aofv'
    end.
  
  (** Given a proof that index [i] is strictly less than the size of
      arrofvalues [aofv], accesses the value at position [i] in [aofv].
   *)

  Fixpoint get_at (i : nat) (aofv : arrofvalues) {struct aofv} : (i < List.length aofv)%nat -> value.
    refine (
        match i, aofv with
        (* Error, index out of bounds. *)
        | S _, Arr_one v => fun _ => _
        | 0%nat, Arr_one v => fun _ => v
        | 0%nat, Arr_cons v aofv' => fun pf => v
        | (S j), Arr_cons a aofv' => fun pf => get_at j aofv' _
        end);
      [apply lt_S_n in l; apply Nat.nlt_0_r in l; contradiction
      | apply (lt_S_n j (List.length aofv') pf)].
  Defined.

  (** Stores value [v] at position [i] in list of values [lofv]. 
    
      Returns an error (i.e, None) if the index is greater than 
      the list length. *)

  Fixpoint oset_at (v : value) (i : nat) (aofv : arrofvalues) {struct i} : option arrofvalues :=
    match i, aofv with
    (* Error, index out of bounds. *)
    | S j, Arr_one _ => None
    | 0%nat, Arr_one v' => Some (Arr_one v)
    | 0%nat, Arr_cons v' tl => Some (Arr_cons v tl)
    | (S j), Arr_cons v' tl =>
        (* Inductive step. *)
        match oset_at v j tl with
        | Some aofv' => Some (Arr_cons v' aofv')
        | None => None
        end
    end.

  (** Given a proof that index [i] is strictly less than the size of
    [aofv], stores value [v] at position [i] in [aofv], and returns
    the new [arrofvalues].  *)

  Fixpoint set_at (v : value) (i : nat) (aofv : arrofvalues) {struct i} : (i < List.length aofv)%nat -> arrofvalues.
    refine (match i, aofv with
            (* Error, index out of bounds. *)
            | S j, Arr_one _ => fun _ => _
            | 0%nat, Arr_one _ => fun _ => Arr_one v
            | 0%nat, Arr_cons _ tl => fun _ => Arr_cons v tl
            | (S j), Arr_cons v' tl => fun _ => Arr_cons v' (set_at v j tl _)
            end).
    apply lt_pred in l; simpl in l; apply Nat.nlt_0_r in l; contradiction.
    apply (lt_S_n j (List.length tl) l).
  Defined.

  Functional Scheme set_at_ind := Induction for set_at Sort Prop.

  (** Given a proof that [n > 0], returns an arrofvalues of length [n]
    filled with value [v]. *)

  Definition create_arr (n : nat) (v : value) : (n > 0)%nat -> arrofvalues :=
    match n as n0 return ((n0 > 0)%nat -> arrofvalues) with
    (* Absurd case, 0 > 0. *)
    | 0%nat => fun H : (0 > 0)%nat => False_rect arrofvalues (Nat.nlt_0_r 0 H)
    (* Case n > 0 *)
    | S m =>
        fun _ =>
          (* Internal fixpoint definition, returns [Arr_one v] when size
         is zero. *)
          let fix create_arrm (m : nat) (v : value) {struct m} :=
            match m return arrofvalues with
            | 0%nat => Arr_one v
            | S o => Arr_cons v (create_arrm o v)
            end
          in create_arrm m v
    end.  
  
End Values.

(** ** Semantic type *)

Section Types.

  (** Defines the type of types used to express the semantics of the
      H-VHDL language.
      
      Note that an element of the [type] type does not carry proofs of
      its well-definition, i.e. one can build an ill-formed natural
      range type, for instance [Tnat 10 2]. *)
  
  Inductive type : Type :=
  | Tbool                              (** Boolean type *)
  | Tnat (l : N) (u : N)               (** Natural range from l to u *)
  | Tarray (t : type) (l : N) (u : N). (** Array of t with index range
                                           from l to u *)

  (** Well-formed type predicate *)

  Inductive WFType : type -> Prop :=
  | WFBool : WFType Tbool
  | WFNat : forall l u, l <= u -> u <= NATMAX -> WFType (Tnat l u)
  | WFArr : forall t l u, l <= u -> u <= NATMAX -> WFType t -> WFType (Tarray t l u).

  Fixpoint WFType_dec (t : type) : {WFType t} + {~WFType t}.
    refine (match t with
            | Tbool => left WFBool
            | Tnat l u =>
                match N_le_dec l u, (N_le_dec u NATMAX) with
                | left lelu, left leuN => left (WFNat l u lelu leuN)
                | _, _ => right _
                end
            | Tarray t__a l u =>
                match WFType_dec t__a with
                | left WFt__a =>
                    match N_le_dec l u, (N_le_dec u NATMAX) with
                    | left lelu, left leuN => left (WFArr t__a l u lelu leuN WFt__a)
                    | _, _ => right _
                    end
                | _ => right _
                end
            end); inversion 1; contradiction.
  Defined.
  
  (** Defines the typing relation [IsOfType]. *)

  Inductive IsOfType : value -> type -> Prop :=
  | IsBool : forall (b : bool), IsOfType (Vbool b) Tbool

  (** Value n must satisfy the index constraint, i.e n ∈ [l,u]. *)
  | IsNat : forall (n l u : N),
      WFType (Tnat l u) -> l <= n <= u -> IsOfType (Vnat n) (Tnat l u)

  (** All elements of the array of values [aofv] must be of type [t],
    and the length of [aofv] must satisfy the index constraint.
   *)
  | IsArrOfT (l u : N) :
    forall (aofv : arrofvalues) (t : type),
      WFType (Tarray t l u) ->
      ArrIsOfType aofv (S (N.to_nat (u - l))) t ->
      IsOfType (Varr aofv) (Tarray t l u)
               
  (** Defines the typing relation over array of values. 
    
    By construction, checks that the array size
    is equal to the second argument (of type [nat]). *)
               
  with ArrIsOfType: arrofvalues -> nat -> type -> Prop :=
  | ArrIsOfTypeOne : forall t v, IsOfType v t -> ArrIsOfType (Arr_one v) 1 t
  | ArrIsOfTypeCons :
    forall aofv size t v,
      IsOfType v t ->
      ArrIsOfType aofv size t ->
      ArrIsOfType (Arr_cons v aofv) (S size) t.

  Scheme IsOfType_ind_mut := Induction for IsOfType Sort Prop
      with ArrIsOfType_ind_mut := Induction for ArrIsOfType Sort Prop.

  (** Defines the typing function [is_of_type]. *)

  Fixpoint is_of_type (v : value) (t : type) {struct v} : optionE bool :=
    match v, t with
    | Vbool b, Tbool => Ret true
    | Vnat n, Tnat l u =>
        if WFType_dec t then
          match N_le_dec l n, N_le_dec n u with
          | left _, left _ => Ret true
          | _, _ => Ret false
          end
        else Err "is_of_type: found an ill-formed nat type"
    | Varr aofv, Tarray ta l u =>
        if WFType_dec t then
          arr_is_of_type aofv ta ((u - l) + 1)
        else Err "is_of_type: found an ill-formed array type"
    | _, _ => Ret false
    end
  with arr_is_of_type (aofv : arrofvalues) (t : type) (size : N) {struct aofv} : optionE bool :=
         match aofv, size with
         | Arr_one v, 1 => is_of_type v t
         | Arr_cons v tl, Npos n =>
             do b1 <- is_of_type v t; do b2 <- arr_is_of_type tl t (size - 1); Ret (b1 && b2)
         | _, _ => Ret false
         end.
  
End Types.

(** ** Equality between two values *)

Section ValueEq.

  (** Specifies the equality relation between two values,
      and the result of the equality evaluation;
      result can either be an error (i.e, [None]), or
      some boolean value.

      Not possible to distinguish errors from "falsity":

      - [~VEq (Vnat 0) (Vnat 1)] is provable because 0 ≠ 1.
      - [~VEq (Vnat 0) (Vbool false)] is provable because 0 and 
      false are not comparable, however it is an error case.
   *)

  Inductive OVEq : value -> value -> option bool -> Prop :=
  | OVEq_BoolT : forall b b', b = b' -> OVEq (Vbool b) (Vbool b') (Some true)
  | OVEq_BoolF : forall b b', b <> b' -> OVEq (Vbool b) (Vbool b') (Some false)
  | OVEq_NatT  : forall n n', n = n' -> OVEq (Vnat n) (Vnat n') (Some true)
  | OVEq_NatF  : forall n n', n <> n' -> OVEq (Vnat n) (Vnat n') (Some false)
  | OVEq_ArrT : forall a a', OArrOfVEq a a' (Some true) -> OVEq (Varr a) (Varr a') (Some true)
  | OVEq_ArrF : forall a a', OArrOfVEq a a' (Some false) -> OVEq (Varr a) (Varr a') (Some false)
  | VEqArr_Err : forall a a', OArrOfVEq a a' None -> OVEq (Varr a) (Varr a') None
                                                          
  (* Error if there is no common type for value [v] and [v'], i.e, [v]
   and [v'] are not comparable. *)
  | OVEq_Err : forall v v', (forall t, ~IsOfType v t \/ ~IsOfType v' t) -> OVEq v v' None
                                                                                
  (** Specifies the equality relation between two arrays of values. *)
  with OArrOfVEq : arrofvalues -> arrofvalues -> option bool -> Prop :=
  (* Convenient to detect errors due to the comparison of two
   arrofvalues of different lengths. *)
  | OArrOfVEq_LengthErr1 : forall v v' aofv, OArrOfVEq (Arr_one v) (Arr_cons v' aofv) None
  | OArrOfVEq_LengthErr2 : forall v v' aofv, OArrOfVEq (Arr_cons v aofv) (Arr_one v') None
  | OArrOfVEq_OneT : forall v v', OVEq v v' (Some true) -> OArrOfVEq (Arr_one v) (Arr_one v') (Some true)
  | OArrOfVEq_OneF : forall v v', OVEq v v' (Some false) -> OArrOfVEq (Arr_one v) (Arr_one v') (Some false)
  | OArrOfVEq_ConsT :
    forall v v' aofv aofv',
      OVEq v v' (Some true) ->
      OArrOfVEq aofv aofv' (Some true) ->
      OArrOfVEq (Arr_cons v aofv) (Arr_cons v' aofv') (Some true)
  | OArrOfVEq_ConsF :
    forall v v' aofv aofv',
      OVEq v v' (Some false) ->
      OArrOfVEq aofv aofv' (Some false) ->
      OArrOfVEq (Arr_cons v aofv) (Arr_cons v' aofv') (Some false)
                
  | OArrOfVEqCons_Err :
    forall v v' aofv aofv' optb,
      OVEq v v' None ->
      OArrOfVEq aofv aofv' optb ->
      OArrOfVEq (Arr_cons v aofv) (Arr_cons v' aofv') None.

  Hint Constructors OVEq : hvhdl.
  Hint Constructors OArrOfVEq : hvhdl.

  Scheme OVEq_ind_mut := Induction for OVEq Sort Prop
      with OArrOfVEq_ind_mut := Induction for OArrOfVEq Sort Prop.

  (** Wrapper around the [OVEq] relation *)

  Definition VEq x y := OVEq x y (Some true).
  Definition VNEq x y := OVEq x y (Some false).

  Definition VEq_refl : forall x, VEq x x.
  Proof. unfold VEq.
         apply (value_ind_mut
                  (fun x => OVEq x x (Some true))
                  (fun x => OArrOfVEq x x (Some true)));
           intros; auto with hvhdl.
  Qed.

  Definition VEq_sym : forall x y, VEq x y -> VEq y x.
  Proof. unfold VEq; intros.       
         apply (OVEq_ind_mut
                  (fun x y o _ => OVEq y x o)
                  (fun x y o _ => OArrOfVEq y x o));
           auto with hvhdl.
         intros; apply OVEq_Err; firstorder.
         intros; eapply OArrOfVEqCons_Err; eauto.
  Defined.

  Definition VEq_trans1 :
    forall y x z, VEq x y -> VEq y z -> VEq x z.
  Proof.
    unfold VEq.
    apply (value_ind_mut
             (fun y => forall x z, OVEq x y (Some true) -> OVEq y z (Some true) -> OVEq x z (Some true))
             (fun y => forall x z, OArrOfVEq x y (Some true) -> OArrOfVEq y z (Some true) -> OArrOfVEq x z (Some true))).
    - (* y = Vbool b *)
      inversion_clear 1; subst; inversion_clear 1; subst.
      constructor; reflexivity.
    - (* y = Vnat n *)
      inversion_clear 1; subst; inversion_clear 1; subst.
      constructor; reflexivity.
    - (* y = Varr a *)
      intros a IH.
      inversion_clear 1; subst; inversion_clear 1; subst.
      constructor; eapply IH; eauto.
    - (* Mutual ind. a = Arr_one *)
      intros v IH.
      inversion_clear 1; subst; inversion_clear 1; subst.
      constructor; eapply IH; eauto.
    - (* Mutual ind. a = Arr_cons *)
      intros v IHv a IHa.
      inversion_clear 1; subst; inversion_clear 1; subst.
      constructor; [ eapply IHv; eauto | eapply IHa; eauto ].
  Defined.

  Definition VEq_trans :
    forall x y z, VEq x y -> VEq y z -> VEq x z.
  Proof. intros x y; generalize x; eapply VEq_trans1. Defined.
  
  Add Parametric Relation : (value) (VEq)
      reflexivity proved by VEq_refl
      symmetry proved by VEq_sym
      transitivity proved by VEq_trans
      as VEq_rel.

  (** Implements the equality operator between two values.
    
      Returns a [bool] corresponding to the result of the comparison
      of the two values.

      Returns an error if the two values do not belong to the same
      domain of values.

   *)

  Fixpoint veq (v v' : value) {struct v} : optionE bool :=
    match v, v' with
    | Vbool b, Vbool b' => Ret (Bool.eqb b b')
    | Vnat n, Vnat n' => Ret (N.eqb n n')
    | Varr aofv, Varr aofv' => arrofveq aofv aofv'
    | _, _ => Err "veq: can not compare two values of different domains"
    end                              
  (** Implements the equality operator between arrays of values.
      
      Returns [Some true] if values of [aofv] and [aofv'] are equal pair-wise.
      
      Returns an error if a pair-wise comparison returns an error or if
      the arrays are of different length. *)
      
  with arrofveq (aofv aofv' : arrofvalues) {struct aofv} : optionE bool :=
         match aofv, aofv' with
         (* Two empty lists are v-equal. *)
         | Arr_one v, Arr_one v' => veq v v'
                                        
         (* Checks that a and b are v-equal. *)
         | (Arr_cons v a), (Arr_cons v' a') =>
             do b <- veq v v'; if b then arrofveq a a' else Ret false
         | _, _ => Err "arrofveq: can not compare to array of values of different size"
         end.
  
End ValueEq.

#[export] Hint Constructors OVEq : hvhdl.
#[export] Hint Constructors OArrOfVEq : hvhdl.

(** ** Index Iterator for [arrofvalues] *)

Section ArrOfV_Iterator.

  (** An array is a least of length [1]; it has at least one
      element. *)
  
  Lemma length_aofv_gt_O : forall aofv : arrofvalues, (0 < List.length aofv)%nat.
    destruct aofv; cbn; eapply Nat.lt_0_succ; eauto.
  Defined.

  (** Generates a contiguous sequence of natural numbers corresponding
      the available indexes of the [aofv] arrofvalues; i.e, the
      sequence ranges from [0] to [length aofv - 1], and for each
      index [i] there is a proof that [i < length aofv]. *)
  
  Definition arrofv_idxs (aofv : arrofvalues) : list { i | (i < List.length aofv)%nat } :=
    seqd 0 (List.length aofv) (length_aofv_gt_O aofv).

  (** [BProd_ArrOfV aofv bprod ≡ ∏i=0 to (length aofv -1), aofv[i]
      ].  If [ aofv[i] ] is not a boolean value, then [true] is passed
      to the product. *)

  Definition get_bool_at (aofv : arrofvalues) (i : nat) : bool :=
    match oget_at i aofv with
    | Some (Vbool b) => b
    | _ => true
    end.
  
  Definition BProd_ArrOfV (aofv : arrofvalues) (bprod : bool) :=
    let f_bprod :=
      fun i =>
        match oget_at i aofv with
        | Some (Vbool b) => b
        | _ => true
        end
    in
    BProd f_bprod (seq 0 (List.length aofv)) bprod.

  (** Dependently-typed version of [BProd_ArrOfV] where there is a
      proof that each index [i] in the generated sequence verifies [i
      < length aofv]. Therefore, we are able to use the error-free
      [get_at] function to access element of [aofv] through their
      index. *)
  
  Definition DepBProd_ArrOfV (aofv : arrofvalues) (bprod : bool) :=
    let f_bprod :=
      fun (i : { n | (n < 0 + List.length aofv)%nat }) =>
        match get_at (proj1_sig i) aofv (proj2_sig i) with
        | Vbool b => b
        | _ => true
        end
    in
    BProd f_bprod (arrofv_idxs aofv) bprod.
  
End ArrOfV_Iterator.



