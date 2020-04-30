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
| Vlist : lofvalues -> value
                         
with lofvalues : Type :=
| Vnil : lofvalues
| Vcons : value -> lofvalues -> lofvalues.

(** Accesses the element at position [i] in lofvalues [lofv]. 
    
    Returns an error (i.e, None) if the index is greater
    than the list length.
 *)

Fixpoint get_at (i : nat) (lofv : lofvalues) {struct i} : option value :=
  match i, lofv with
  (* Error, cannot access elements in an empty lofvalues. *)
  | _, Vnil => None
  | 0, Vcons a l => Some a
  | (S j), Vcons a l' => get_at j l'
  end.

(** Stores value [v] at position [i] in list of values [lofv]. 
    
    Returns an error (i.e, None) if the index is greater than 
    the list length. *)

Fixpoint set_at (v : value) (i : nat) (lofv : lofvalues) {struct i} : option lofvalues :=
  match i, lofv with
  (* Error, cannot access elements in an empty lofvalues. *)
  | _, Vnil => None
  | 0, Vcons a tl => Some (Vcons v tl)
  | (S j), Vcons a tl =>
    (* Inductive step. *)
    match set_at v j tl with
    | Some lofv' => Some (Vcons a lofv')
    | None => None
    end
  end.

(** Creates a list of length [n] filled with value [v]. *)

Fixpoint create_list (n : nat) (v : value) {struct n} : lofvalues :=
  match n with
  | 0 => Vnil
  | S m => Vcons v (create_list m v)
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

(** All elements of the value list [lv] must be of type [t],
    and the length of [lv] must satisfy the index constraint.
 *)
| IsListOfT :
    forall (lofv : lofvalues) (t : type) (l u : nat),
      lis_of_type lofv ((u - l) + 1) t ->
      is_of_type (Vlist lofv) (Tarray t l u)
                 
(** Defines the typing relation over list of values. 
    
    By construction, checks that the list length
    is equal to the second argument (of type [nat]). *)
                 
with lis_of_type : lofvalues -> nat -> type -> Prop :=
| LIsOfTypeNil : forall {t}, lis_of_type Vnil 0 t
| LIsOfTypeCons :
    forall {lofv size t v},
      is_of_type v t ->
      lis_of_type lofv size t ->
      lis_of_type (Vcons v lofv) (S size) t.

(** Specifies the equality relation between two values. 

    Not possible to distinguish errors from "falsity":

    - [~VEq (Vnat 0) (Vnat 1)] is provable because 0 ≠ 1.
    - [~VEq (Vnat 0) (Vbool false)] is provable because 0 and 
      false are not comparable, however it is an error case.
 *)

Inductive VEq : value -> value -> option bool -> Prop :=
| VEqBoolT : forall {b b'}, b = b' -> VEq (Vbool b) (Vbool b') (Some true)
| VEqBoolF : forall {b b'}, b <> b' -> VEq (Vbool b) (Vbool b') (Some false)
| VEqNatT  : forall {n n'}, n = n' -> VEq (Vnat n) (Vnat n') (Some true)
| VEqNatF  : forall {n n'}, n <> n' -> VEq (Vnat n) (Vnat n') (Some false)
| VEqListT : forall {l l'}, LOfVEq l l' (Some true) -> VEq (Vlist l) (Vlist l') (Some true)
| VEqListF : forall {l l'}, LOfVEq l l' (Some false) -> VEq (Vlist l) (Vlist l') (Some false)
| VEqListErr : forall {l l'}, LOfVEq l l' None -> VEq (Vlist l) (Vlist l') None
                                                            
(* Error if there does not exist a common type for value v and v'. *)
| VEqErr : forall {v v'}, (forall {t}, ~is_of_type v t \/ ~is_of_type v' t) -> VEq v v' None
                                                                                                                                   
(** Specifies the equality relation between two lists of values. *)
with LOfVEq : lofvalues -> lofvalues -> option bool -> Prop :=
| LOfVEqNil : LOfVEq Vnil Vnil (Some true)

(* Convenient to detect errors due to the comparison of two
   lofvalues of different lengths. *)
| LOfVEqLengthErr1 : forall {v l}, LOfVEq Vnil (Vcons v l) None
| LOfVEqLengthErr2 : forall {v l}, LOfVEq (Vcons v l) Vnil None
| LOfVEqConsT :
    forall {v v' l l'},
      VEq v v' (Some true) -> LOfVEq l l' (Some true) -> LOfVEq (Vcons v l) (Vcons v' l') (Some true)
| LOfVEqConsF :
    forall {v v' l l'},
      VEq v v' (Some false) -> LOfVEq l l' (Some false) -> LOfVEq (Vcons v l) (Vcons v' l') (Some false)
| LOfVEqConsErr :
    forall {v v' l l' optb},
      VEq v v' None -> LOfVEq l l' optb -> LOfVEq (Vcons v l) (Vcons v' l') None.

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
  | Vlist l, Vlist l' => lofveq l l'

  (* Error, cannot compare two values of different domains. *)
  | _, _ => None
  end                              

(** Implements the equality operator between list of values.
      
   Returns [Some true] if values of [l] and [l'] are equal pair-wise.
      
   Returns an error if a pair-wise comparison returns an error or if
   the lists are of different length. *)
    
with lofveq (l l' : lofvalues) {struct l} : option bool :=
       match l, l' with
       (* Two empty lists are v-equal. *)
       | Vnil, Vnil => Some true
                            
       (* Checks that a and b are v-equal. *)
       | (Vcons v m), (Vcons v' m') =>
         match veq v v' with
         (* Pair-wise comparison returned a boolean value. *)
         | Some false => Some false
         | Some true => lofveq m m'
         (* Error, pair-wise comparison failed. *)
         | None => None
         end
       (* Error, l and l' are not of the same length. *)
       | _, _ => None
       end.
