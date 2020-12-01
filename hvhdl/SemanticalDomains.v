(** * Semantical domains for H-VHDL. *)

(** Module defining the semantics domains used in H-VHDL semantics. *)

Require Import Coqlib.
Require Import AbstractSyntax.
Require Import GlobalTypes.

(** Defines the type of values used in the 
    semantical world.

    A value is either:

    - a boolean
    - a natural number
    - a list of values. *)

Inductive value : Type :=
| Vbool : bool -> value
| Vnat : nat -> value
| Varr : arrofvalues -> value
                         
with arrofvalues : Type :=
| Arr_one : value -> arrofvalues
| Arr_cons : value -> arrofvalues -> arrofvalues.

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

Fixpoint oget_at (i : nat) (aofv : arrofvalues) {struct i} : option value :=
  match i, aofv with
  (* Error, index out of bounds. *)
  | (S _), Arr_one v => None
  | 0, Arr_one v => Some v
  | 0, Arr_cons v aofv' => Some v
  | (S j), Arr_cons a aofv' => oget_at j aofv'
  end.

(** Given a proof that index [i] is strictly less than the size of
    arrofvalues [aofv], accesses the value at position [i] in [aofv].
 *)

Fixpoint get_at (i : nat) (aofv : arrofvalues) {struct i} : i < length aofv -> value.
  refine (
      match i, aofv with
      (* Error, index out of bounds. *)
      | (S j) as i, Arr_one v => fun _ => _
      | 0, Arr_one v => fun _ => v
      | 0, Arr_cons v aofv' => fun pf => v
      | (S j) as i, Arr_cons a aofv' => fun pf => get_at j aofv' _
      end);
    [apply lt_pred in l; simpl in l; apply Nat.nlt_0_r in l; contradiction
    | apply (lt_S_n j (length aofv') pf)].
Defined.

(** Stores value [v] at position [i] in list of values [lofv]. 
    
    Returns an error (i.e, None) if the index is greater than 
    the list length. *)

Fixpoint oset_at (v : value) (i : nat) (aofv : arrofvalues) {struct i} : option arrofvalues :=
  match i, aofv with
  (* Error, index out of bounds. *)
  | S j, Arr_one _ => None
  | 0, Arr_one v' => Some (Arr_one v)
  | 0, Arr_cons v' tl => Some (Arr_cons v tl)
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

Fixpoint set_at (v : value) (i : nat) (aofv : arrofvalues) {struct i} : i < length aofv -> arrofvalues.
  refine (match i, aofv with
          (* Error, index out of bounds. *)
          | S j, Arr_one _ => fun _ => _
          | 0, Arr_one _ => fun _ => Arr_one v
          | 0, Arr_cons _ tl => fun _ => Arr_cons v tl
          | (S j), Arr_cons v' tl => fun _ => set_at v j tl _
          end).
  apply lt_pred in l; simpl in l; apply Nat.nlt_0_r in l; contradiction.
  apply (lt_S_n j (length tl) l).
Defined.

(** Given a proof that [n > 0], returns an arrofvalues of length [n]
    filled with value [v]. *)

Fixpoint create_arr (n : nat) (v : value) {struct n} : n > 0 -> arrofvalues :=
  match n as n0 return (n0 > 0 -> arrofvalues) with
  (* Absurd case, 0 > 0. *)
  | 0 => fun H : 0 > 0 => False_rect arrofvalues (Nat.nlt_0_r 0 H)
  (* Case n > 0 *)
  | S m =>
    fun _ =>
      (* Internal fixpoint definition, returns [Arr_one v] when size
         is zero. *)
      let fix create_arrm (m : nat) (v : value) {struct m} :=
          match m return arrofvalues with
          | 0 => Arr_one v
          | S o => Arr_cons v (create_arrm o v)
          end
      in create_arrm m v
  end.  

(** Defines the type of types used in the
    semantical world. *)

Inductive type : Type :=
| Tbool                                  (** Boolean *)
| Tnat (l : nat) (u : nat)               (** Constrained natural. *)
| Tarray (t : type) (l : nat) (u : nat). (** Fixed-size array. *)

(** Defines the typing relation [is_of_type]. *)

Inductive is_of_type : value -> type -> Prop :=
| IsBool : forall (b : bool), is_of_type (Vbool b) Tbool

(** Value n must satisfy the index constraint, i.e n ∈ [l,u]. *)
| IsNat : forall (n l u : nat), l <= n <= u -> is_of_type (Vnat n) (Tnat l u)

(** All elements of the array of values [aofv] must be of type [t],
    and the length of [aofv] must satisfy the index constraint.
 *)
| IsArrOfT (l u : nat) :
    forall (aofv : arrofvalues) (t : type),
      arris_of_type aofv ((u - l) + 1) t ->
      is_of_type (Varr aofv) (Tarray t l u)
                 
(** Defines the typing relation over array of values. 
    
    By construction, checks that the array size
    is equal to the second argument (of type [nat]). *)
                 
with arris_of_type : arrofvalues -> nat -> type -> Prop :=
| ArrIsOfTypeOne : forall t v, arris_of_type (Arr_one v) 1 t
| ArrIsOfTypeCons :
    forall aofv size t v,
      is_of_type v t ->
      arris_of_type aofv size t ->
      arris_of_type (Arr_cons v aofv) (S size) t.

(** Specifies the equality relation between two values without
    describing the error cases.
 *)

Inductive VEq : value -> value -> Prop :=
| VEq_bool : forall b b', b = b' -> VEq (Vbool b) (Vbool b')
| VEq_nat  : forall n n', n = n' -> VEq (Vnat n) (Vnat n')
| VEq_arr : forall a a', ArrOfVEq a a' -> VEq (Varr a) (Varr a')

with ArrOfVEq : arrofvalues -> arrofvalues -> Prop :=

| ArrOfVEq_one : forall v v', VEq v v' -> ArrOfVEq (Arr_one v) (Arr_one v')
| ArrOfVEq_cons :
    forall v v' aofv aofv',
      VEq v v' ->
      ArrOfVEq aofv aofv' ->
      ArrOfVEq (Arr_cons v aofv) (Arr_cons v' aofv').


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
| OVEq_Err : forall v v', (forall t, ~is_of_type v t \/ ~is_of_type v' t) -> OVEq v v' None
                                                                                                                                   
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

(** Implements the equality operator between two values.
    
    Returns a [bool] corresponding to the result of the comparison of
    the two values.

    Returns an error if the two values do not belong to the same
    domain of values.

 *)

Fixpoint veq (v v' : value) {struct v} : option bool :=
  match v, v' with
  | Vbool b, Vbool b' => Some (Bool.eqb b b')
  | Vnat n, Vnat n' => Some (Nat.eqb n n')
  | Varr aofv, Varr aofv' => arrofveq aofv aofv'

  (* Error, cannot compare two values of different domains. *)
  | _, _ => None
  end                              

(** Implements the equality operator between arrays of values.
      
   Returns [Some true] if values of [aofv] and [aofv'] are equal pair-wise.
      
   Returns an error if a pair-wise comparison returns an error or if
   the arrays are of different length. *)
    
with arrofveq (aofv aofv' : arrofvalues) {struct aofv} : option bool :=
       match aofv, aofv' with
       (* Two empty lists are v-equal. *)
       | Arr_one v, Arr_one v' => veq v v'
                            
       (* Checks that a and b are v-equal. *)
       | (Arr_cons v a), (Arr_cons v' a') =>
         match veq v v' with
         (* Pair-wise comparison returned a boolean value. *)
         | Some false => Some false
         | Some true => arrofveq a a'
         (* Error, pair-wise comparison failed. *)
         | None => None
         end
       (* Error, l and l' are not of the same length. *)
       | _, _ => None
       end.
