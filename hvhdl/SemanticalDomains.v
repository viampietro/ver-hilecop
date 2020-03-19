(** Module defining the semantics domains used in H-VHDL semantics. *)

Require Import Coqlib.
Require Import Arrays.
Require Import AbstractSyntax.
Require Import GlobalTypes.

(** Defines the type of values used in the 
    semantical world.

    A value is either:
    - a boolean
    - a natural number
    - an element of arc_t
    - an element of transition_t
    - a list of values. *)

Inductive value : Type :=
| Vbool : bool -> value
| Vnat : nat -> value
| Varc : arc_t -> value
| Vtransition : transition_t -> value
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

(** Specifies the equality relation between two values. *)

Inductive VEq : value -> value -> Prop :=
| VEqBool : forall {b b'}, b = b' -> VEq (Vbool b) (Vbool b')
| VEqNat  : forall {n n'}, n = n' -> VEq (Vnat n) (Vnat n')
| VEqArc  : forall {a a'}, a = a' -> VEq (Varc a) (Varc a')
| VEqTransition : forall {t t'}, t = t' -> VEq (Vtransition t) (Vtransition t')
| VEqList : forall {l l'}, LOfVEq l l' -> VEq (Vlist l) (Vlist l')

(** Specifies the equality relation between two lists of values. *)
with LOfVEq : lofvalues -> lofvalues -> Prop :=
| LOfVEqNil : LOfVEq Vnil Vnil
| LOfVEqCons : forall {v v' l l'}, VEq v v' -> LOfVEq l l' -> LOfVEq (Vcons v l) (Vcons v' l').
  
(** Implements the equality operator between two values. 
    
    Returns an error if the two values do not belong
    to the same domain of values.

    Returns a [bool] corresponding the result of the comparison
    of the two values if no error.
 *)

Fixpoint veq (v v' : value) {struct v} : option bool :=
  match v, v' with
  | Vbool b, Vbool b' => Some (Bool.eqb b b')
  | Vnat n, Vnat n' => Some (Nat.eqb n n')
  | Varc a, Varc a' => Some (ArcT.eqb a a')
  | Vtransition t, Vtransition t' => Some (TransitionT.eqb t t')
  | Vlist l, Vlist l' => lofveq l l'

  (* Error, cannot compare two values of different domains. *)
  | _, _ => None
  end                              

(** Implements the equality operator between list of values.
      
      Returns [Some true] if values of [l] and [l'] are equal
      pair-wise.
      
      Returns an error if a pair-wise comparison returns an error
      or if the lists are of different length. *)
    
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

(** Defines the type of types used in the
    semantical world. *)

Inductive type : Type :=
| Tbool                                 (** Boolean *)
| Tnat (l : nat) (u : nat)              (** Constrained natural. *)
| Tarray (t : type) (l : nat) (u : nat) (** Fixed-size array. *)
| Tarc_t                                (** arc_t type. *)
| Ttransition_t.                        (** transition_t type. *)


