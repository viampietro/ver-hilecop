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
| Vlist : list value -> value.

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

(** Defines the type of types used in the
    semantical world. *)

Inductive type : Type :=
| Tbool                                 (** Boolean *)
| Tnat (l : nat) (u : nat)              (** Constrained natural. *)
| Tarray (t : type) (l : nat) (u : nat) (** Fixed-size array. *)
| Tarc_t                                (** arc_t type. *)
| Ttransition_t.                        (** transition_t type. *)


