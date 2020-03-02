(** Module defining the semantics domains used in H-VHDL semantics. *)

Require Import Coqlib.
Require Import Arrays.
Require Import GlobalTypes.
Require Import AbstractSyntax.

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

(** Implements the addition between two values.

    Returns an error if: 
    
    - the two values are not [nat] values.  
    - the addition of the two values results in 
      a [nat] overflow, i.e over [NATMAX]. *)

Definition vadd (v v' : value) : option value :=
  match v, v' with
  (* The two values must be [nat] values. *)
  | Vnat n, Vnat n' =>
    
    (* Checks that the addition does not result
       in an overflow error (over NATMAX). *)
    let result := n + n' in
    if result <=? NATMAX then Some (Vnat result) else None
                                                        
  (* Error, if the two values are not [nat]. *)
  | _, _ => None
  end.

(** Implements the substraction between two values. 

    Returns an error if: 
    
    - the two value are not [nat] values.  
    - the substraction of the two values 
      stays in the nat [domain], i.e, does not go below zero. *)

Definition vsub (v v' : value) : option value :=
  match v, v' with
  | Vnat n, Vnat n' =>
    (* Checks that the substraction does not return a 
     negative result. *)
    if n' <=? n then Some (Vnat (n - n')) else None
  | _, _ => None
  end.

(** Implements the "less or equal" test between two values.
    
    Returns an error if the two tested values are not [nat] values.  
    Returns a [bool] value if no error.
 *)

Definition vle (v v' : value) : option value :=
  match v, v' with
  | Vnat n, Vnat n' => Some (Vbool (n <=? n'))
  | _, _ => None
  end.

(** Implements the "strictly less" test between two values.
    
    Returns an error if the two tested values are not [nat] values.  
    Returns a [bool] value if no error.
 *)

Definition vlt (v v' : value) : option value :=
  match v, v' with
  | Vnat n, Vnat n' => Some (Vbool (n <? n'))
  | _, _ => None
  end.

(** Implements the "greater or equal" test between two values.
    
    Returns an error if the two tested values are not [nat] values.  
    Returns a [bool] value if no error.
 *)

Definition vge (v v' : value) : option value :=
  match v, v' with
  | Vnat n, Vnat n' => Some (Vbool (n' <=? n))
  | _, _ => None
  end.

(** Implements the "strictly greater" test between two values.
    
    Returns an error if the two tested values are not [nat] values.  
    Returns a [bool] value if no error.
 *)

Definition vgt (v v' : value) : option value :=
  match v, v' with
  | Vnat n, Vnat n' => Some (Vbool (n' <? n))
  | _, _ => None
  end.

(** Implements the and operator between two values. 
    
    Returns an error if the two values are not [bool] values. *)

Definition vand (v v' : value) : option value :=
  match v, v' with
  | Vbool b, Vbool b' => Some (Vbool (b && b'))
  | _, _ => None
  end.

(** Implements the or operator between two values. 
    
    Returns an error if the two values are not [bool] values. *)

Definition vor (v v' : value) : option value :=
  match v, v' with
  | Vbool b, Vbool b' => Some (Vbool (b || b'))
  | _, _ => None
  end.

(** Implements the equality operator between two values. 
    
    Returns an error if the two values do not belong
    to the same domain of values.

    Returns a [bool] corresponding the result of the comparison
    of the two values if no error.
 *)

Fixpoint veq_aux (v v' : value) {struct v} : option bool :=
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
         match veq_aux v v' with
         (* Pair-wise comparison returned a boolean value. *)
         | Some false => Some false
         | Some true => lofveq m m'
         (* Error, pair-wise comparison failed. *)
         | None => None
         end
       (* Error, l and l' are not of the same length. *)
       | _, _ => None
       end.

(** Wraps the result of [veq_aux] in a value. *)

Definition veq (v v' : value) : option value :=
  match veq_aux v v' with
  | Some b => Some (Vbool b)
  | None => None
  end.

(** Implements the not operator for values. 
    
    Returns an error if [v] is not a [bool] value.
 *)

Definition vnot (v : value) : option value :=
  match v with
  | Vbool b => Some (Vbool (negb b))
  | _ => None
  end.

(** Defines the type of types used in the
    semantical world. *)

Inductive type : Type :=
| Tbool                                 (** Boolean *)
| Tnat (l : nat) (u : nat)              (** Constrained natural. *)
| Tarray (t : type) (l : nat) (u : nat) (** Fixed-size array. *)
| Tarc_t                                (** arc_t type. *)
| Ttransition_t.                        (** transition_t type. *)


