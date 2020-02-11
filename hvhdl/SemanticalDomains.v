(** Module defining the type of identifiers and values that are common
    to the syntax and the semantics of H-VHDL.  *)

Require Import Coqlib.
Require Import GlobalTypes.
Require Import AbstractSyntax.
Require Import HilecopDefinitions.

(** Defines the type of values used in the 
    semantical world.

    A value is either:
    - a boolean
    - a natural number
    - a list of values. *)

Inductive value : Type :=
| Vbool : bool -> value
| Vnat : nat -> value
| Vlist : list value -> value.

(** Defines the type of types used in the
    semantical world. *)

Inductive type : Type :=
| T (tid : typeid)                (** Type id *)
    (constr : option (nat * nat)) (** Constraint is either a couple of
                                      nat, or null (i.e, None here) *)
with typeid : Type :=
| Tid (id : ident)              (** User-defined type id. *)
| Tnat                          (** Natural *)
| Tbool                         (** Boolean *)
| Tarray (t : type).            (** Array of a certain type. *)

(** Defines the type of type definitions used in
    the semantical world.
 *)

Inductive typedef : Type :=
| Tdef_t (t : type)              (** Type definition as an alias to
                                     another type. *)
| Tdef_enum (lme : ident)
            (enum : list ident). (** Type definition as a non-empty definition 
                                     of identifiers. *)

(** Defines the design structure describing 
    H-VHDL design instances in the semantical world. *)

(* Needed because design_struct as a recurvise definition that does
   not respect the strict positivity requirement.  
   
   However, I am not sure that it is too dangerous to do so. *)

Local Unset Positivity Checking.

Inductive design_struct : Type :=
  mk_design {
      Gens     : IdMap (type * value * value);
      Ins      : IdMap type;
      Outs     : IdMap type;
      Sigs     : IdMap type;
      Consts   : IdMap (type * value);
      Ps       : IdMap (IdMap (type * value));
      Comps    : IdMap design_struct;
      Types    : IdMap typedef;
      Behavior : cs;
    }.

(** Defines empty map for all fields of the design_struct. *)

Definition empty_gens := NatMap.empty (type * value * value).
Definition empty_ins := NatMap.empty type.
Definition empty_outs := NatMap.empty type.
Definition empty_sigs := NatMap.empty type.
Definition empty_consts := NatMap.empty (type * value).
Definition empty_localenv := NatMap.empty (IdMap (type * value)).
Definition empty_comps := NatMap.empty design_struct.
Definition empty_types := NatMap.empty typedef.

(** Defines an empty design_struct instance.

    The type of empty_design is cs -> design_struct because the
    Behavior field as no value yet.  *)

Definition empty_design : cs -> design_struct :=
  mk_design
    empty_gens empty_ins empty_outs empty_sigs empty_consts
    empty_localenv empty_comps empty_types.

(** Defines the structure of design state. *)

Inductive design_state : Type :=
  mk_design_state {
      sigstore  : IdMap value;
      compstore : IdMap design_state;
      events    : IdSet;
    }.

(** Definition of the [dom] function that yields a list of identifiers
    corresponding to the definition domain of an IdMap. *)

Definition dom {A : Type} (f : IdMap A) : list ident := fs (NatMap.elements f).

(** Definition of the [enum] function that yields a list of
    identifiers corresponding to all identifiers contained in the data
    part of map [f], which is of type [IdMap typedef]. *)

Fixpoint enum_aux (ltypedef : list typedef) {struct ltypedef} : list ident :=
  match ltypedef with
  | nil => nil
  | cons t tl =>
    match t with
    | Tdef_enum hd e => [hd] ++ e ++ enum_aux tl
    | _ => enum_aux tl
    end
  end.

Definition enum (f : IdMap typedef) : list ident :=
  enum_aux (snd (split (NatMap.elements f))).
