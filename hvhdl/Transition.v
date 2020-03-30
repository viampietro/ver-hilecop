(** * Definition of the HILECOP's Transition design in H-VHDL abstract syntax. *)

(** Defines the Transition design used in the generation of
    VHDL listing from SITPNs.
 *)

Require Import Coqlib.
Require Import GlobalTypes.
Require Import AbstractSyntax.
Require Import SemanticalDomains.
Require Import Petri.

Open Scope natset_scope.
Open Scope ast_scope.

(** ** Entity part of the Transition design. *)

(** *** Generic constants of the Transition design. *)

(** Defines the identifiers of generic constants.
    
    Begins with i + 1 as i is the last reserved identifier.  *)

Definition transition_type      : ident := i + 1.
Definition input_arcs_number    : ident := transition_type + 1.
Definition conditions_number    : ident := input_arcs_number + 1.
Definition maximal_time_counter : ident := conditions_number + 1.

(** Defines the generic clause of the Transition design. *)

Definition transition_gens : list gdecl :=
  [gdecl_ transition_type     tind_transition_t not_temporal;
  gdecl_ input_arcs_number    (tind_natural 0 NATMAX) 1;
  gdecl_ conditions_number    (tind_natural 0 NATMAX) 1;
  gdecl_ maximal_time_counter (tind_natural 0 NATMAX) 1].

(** *** Ports of the Transition design. *)

(** Input ports identifiers. *)

Definition input_conditions        : ident := maximal_time_counter + 1.
Definition time_A_value            : ident := input_conditions + 1.
Definition time_B_value            : ident := time_A_value + 1.
Definition input_arcs_valid        : ident := time_B_value + 1.
Definition reinit_time             : ident := input_arcs_valid + 1.
Definition priority_authorizations : ident := reinit_time + 1.

(** Output ports identifiers. *)

Definition fired                   : ident := priority_authorizations + 1.

(** Port clause of the Transition design. *)

Definition transition_ports : list pdecl :=
  [
  (* Input ports. *)
  pdecl_in clk                     tind_boolean;
  pdecl_in rst                     tind_boolean;
  pdecl_in input_conditions        (bool_vector_t 0 (#conditions_number @- 1));
  pdecl_in time_A_value            (tind_natural 0 (#maximal_time_counter));
  pdecl_in time_B_value            (tind_natural 0 (#maximal_time_counter));
  pdecl_in input_arcs_valid        (bool_vector_t 0 (#input_arcs_number @- 1));
  pdecl_in reinit_time             (bool_vector_t 0 (#input_arcs_number @- 1));
  pdecl_in priority_authorizations (bool_vector_t 0 (#input_arcs_number @- 1));
  
  (* Output ports. *)
  pdecl_out fired                  tind_boolean
  ].


(** ** Architecture part of the Transition design. *)

(** *** Architecture declarative part of the Transition design. *)

(** Declared signal identifiers. *)

Definition s_condition_combination : ident := fired + 1. 
Definition s_enabled : ident := s_condition_combination + 1.
Definition s_firable : ident := s_enabled + 1. 
Definition s_fired : ident := s_firable + 1.
Definition s_firing_condition : ident := s_fired + 1.
Definition s_priority_combination : ident := s_firing_condition + 1.
Definition s_reinit_time_counter : ident := s_priority_combination + 1.
Definition s_time_counter : ident := s_reinit_time_counter + 1.

(** Architecture declaration list. *)

Definition transition_adecls : list adecl :=
  [
  adecl_sig s_condition_combination tind_boolean;
  adecl_sig s_enabled               tind_boolean;
  adecl_sig s_firable               tind_boolean;
  adecl_sig s_fired                 tind_boolean;
  adecl_sig s_firing_condition      tind_boolean;
  adecl_sig s_priority_combination  tind_boolean;
  adecl_sig s_reinit_time_counter   tind_boolean;
  adecl_sig s_time_counter          (tind_natural 0 (#maximal_time_counter))
  ].
