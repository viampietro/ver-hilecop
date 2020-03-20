(** * Macros for the definition of HILECOP Place and Transition designs. *)

Require Import AbstractSyntax.
Require Import GlobalTypes.

(** Defines multiple macros that are convenient to build
    the Place and Transition designs in H-VHDL abstract syntax. 

    Constants, types and subtypes defined in the "petri.vhd" of HILECOP
    find here their equivalent definition in Coq.
 *)

(** Global constant macros. *)

Definition MAXIMAL_GLOBAL_MARKING : nat := 255.

(** Type and subtype macros. *)

Definition weight_t        : tind := tind_natural (e_nat 0, e_nat MAXIMAL_GLOBAL_MARKING).
Definition weight_vector_t : (expr * expr) -> tind := tind_array weight_t.
Definition arc_vector_t    : (expr * expr) -> tind := tind_array tind_arc_t.
Definition bool_vector_t : (expr * expr) -> tind := tind_array tind_boolean.

(** Reserved identifiers for variables. *)

Definition local_var : ident := 100.
Definition loop_var  : ident := 150.
Definition i : ident := loop_var.
