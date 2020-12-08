(** * Definition of the HILECOP's Transition design in H-VHDL abstract syntax. *)

(** Defines the Transition design used in the generation of
    VHDL listing from SITPNs.
 *)

Require Import Coqlib.
Require Import GlobalTypes.
Require Import AbstractSyntax.
Require Import SemanticalDomains.
Require Import Petri.
Require Import HVhdlTypes.

Open Scope natset_scope.
Open Scope abss_scope.

Local Definition i := local_var.

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
  [gdecl_ transition_type     transition_t not_temporal;
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

Definition transition_sigs : list sdecl :=
  [
  sdecl_ s_condition_combination tind_boolean;
  sdecl_ s_enabled               tind_boolean;
  sdecl_ s_firable               tind_boolean;
  sdecl_ s_fired                 tind_boolean;
  sdecl_ s_firing_condition      tind_boolean;
  sdecl_ s_priority_combination  tind_boolean;
  sdecl_ s_reinit_time_counter   tind_boolean;
  sdecl_ s_time_counter          (tind_natural 0 (#maximal_time_counter))
  ].

(** *** Architecture behavioral part of the Transition design. *)

(** Defines the architecture behavioral part of the Transition design
    proceeding process by process.  *)

(** Process "condition_evaluation". *)

(* Process id. *)
Definition condition_evaluation : ident := s_time_counter + 1.

(* Process "condition_evaluation" declarative part. *)

Definition v_internal_condition : ident := local_var.

(* Process "conditio_evaluation" declaration. *)

Definition condition_evaluation_ps :=
  cs_ps condition_evaluation

        (* Sensitivity list. *)
        {[input_conditions]}
        
        (* Local variables. *)
        [vdecl_ v_internal_condition tind_boolean]

        (* Process body. *)
        (
          (v_internal_condition @:= true);;
          (For i In 0 To (#conditions_number @- 1) Loop (
                 v_internal_condition @:= (#v_internal_condition @&& (input_conditions[[#i]]))
          ));;
          (s_condition_combination @<== #v_internal_condition)
        ).

(** Process "enable_evaluation". *)

(* Process id. *)
Definition enable_evaluation : ident := condition_evaluation + 1.

(* Process "enable_evaluation" declarative part. *)

Definition v_internal_enabled : ident := local_var.

(* Process "enable_evaluation" declaration. *)

Definition enable_evaluation_ps :=
  cs_ps enable_evaluation

        (* Sensitivity list. *)
        {[input_arcs_valid]}
        
        (* Local variables. *)
        [vdecl_ v_internal_enabled tind_boolean]

        (* Process body. *)
        (
          (v_internal_enabled @:= true);;
          (For i In 0 To (#input_arcs_number @- 1) Loop (
                 v_internal_enabled @:= (#v_internal_enabled @&& (input_arcs_valid[[#i]]))
          ));;
          (s_enabled @<== #v_internal_enabled)
        ).

(** Process "reinit_time_counter_evaluation". *)

(* Process id. *)
Definition reinit_time_counter_evaluation : ident := enable_evaluation + 1.

(* Process "reinit_time_counter_evaluation" declarative part. *)

Definition v_internal_reinit_time_counter : ident := local_var.

(* Process "reinit_time_counter_evaluation" declaration. *)

Definition reinit_time_counter_evaluation_ps :=
  cs_ps reinit_time_counter_evaluation

        (* Sensitivity list. *)
        {[reinit_time, s_enabled]}
        
        (* Local variables. *)
        [vdecl_ v_internal_reinit_time_counter tind_boolean]

        (* Process body. *)
        (
          (v_internal_reinit_time_counter @:= false);;
          (For i In 0 To (#input_arcs_number @- 1) Loop (
                 v_internal_reinit_time_counter @:= (#v_internal_reinit_time_counter @&& (reinit_time[[#i]]))
          ));;
          (s_reinit_time_counter @<== #v_internal_reinit_time_counter)
        ).

(** Process "time_counter". *)

(* Process id. *)
Definition time_counter : ident := reinit_time_counter_evaluation + 1.

(* Process "time_counter" declaration. *)

Definition time_counter_ps :=
  cs_ps time_counter

        (* Sensitivity list. *)
        {[rst, clk]}
        
        (* Local variables. *)
        []

        (* Process body. *)
        (
          If (#rst @= false)
          Then (s_time_counter @<== 0)
          Else (
            Falling (
                If (#s_enabled @= true @&& (#transition_type @/= not_temporal))
                   Then (If (#s_reinit_time_counter @= false)
                            Then (If (#s_time_counter @< #maximal_time_counter) Then
                                     (s_time_counter @<== (#s_time_counter @+ 1)))
                            Else (s_time_counter @<== 1))
                   Else (s_time_counter @<== 0)))
        ).

(** Process "firing_condition_evaluation". *)

(* Process id. *)
Definition firing_condition_evaluation : ident := time_counter + 1.

(* Process "firing_condition_evaluation" declaration. *)

Definition firing_condition_evaluation_ps :=
  cs_ps firing_condition_evaluation

        (* Sensitivity list. *)
        {[s_enabled, s_condition_combination, s_reinit_time_counter, s_time_counter]}
        
        (* Local variables. *)
        []

        (* Process body. *)
        (
          If ( ((#transition_type @= not_temporal)
                  @&& (#s_enabled @= true)
                  @&& (#s_condition_combination @= true))
                 
                 @|| ( (#transition_type @= temporal_a_b)
                         @&& (#s_reinit_time_counter @= false)
                         @&& (#s_enabled @= true)
                         @&& (#s_condition_combination @= true)
                         @&& (#s_time_counter @>= (#time_A_value @- 1))
                         @&& (#s_time_counter @< #time_B_value)
                         @&& (#time_A_value @/= 0)
                         @&& (#time_B_value @/= 0) )
                 
                 @|| ( (#transition_type @= temporal_a_a)
                         @&& (#s_reinit_time_counter @= false)
                         @&& (#s_enabled @= true)
                         @&& (#s_condition_combination @= true)
                         @&& (#s_time_counter @= (#time_A_value @- 1))
                         @&& (#time_A_value @/= 0) )
                 
                 @|| ( (#transition_type @= temporal_a_inf)
                         @&& (#s_reinit_time_counter @= false)
                         @&& (#s_enabled @= true)
                         @&& (#s_condition_combination @= true)
                         @&& (#s_time_counter @>= (#time_A_value @- 1))
                         @&& (#time_A_value @/= 0) )
                 
                 @|| ( (#transition_type @/= not_temporal)
                         @&& (#s_reinit_time_counter @= true)
                         @&& (#s_enabled @= true)
                         @&& (#s_condition_combination @= true)
                         @&& (#time_A_value @= 1) )
             )
             
             Then (s_firing_condition @<== true)
             Else (s_firing_condition @<== false)
        ).

(** Process "priority_authorization_evaluation". *)

(* Process id. *)
Definition priority_authorization_evaluation : ident := firing_condition_evaluation + 1.

(* Process "priority_authorization_evaluation" declarative part. *)

Definition v_priority_combination : ident := local_var.

(* Process "priority_authorization_evaluation" declaration. *)

Definition priority_authorization_evaluation_ps :=
  cs_ps priority_authorization_evaluation

        (* Sensitivity list. *)
        {[priority_authorizations]}
        
        (* Local variables. *)
        [vdecl_ v_priority_combination tind_boolean]

        (* Process body. *)
        (
          (v_priority_combination @:= false);;

          (For i In 0 To (#input_arcs_number @- 1) Loop (
                 v_priority_combination @:= (#v_priority_combination @&& priority_authorizations[[#i]])
          ));;

          (s_priority_combination @<== #v_priority_combination)
        ).

(** Process "firable". *)

(* Process id. *)
Definition firable : ident := priority_authorization_evaluation + 1.

(* Process "firable" declaration. *)

Definition firable_ps :=
  cs_ps firable
        (* Sensitivity list. *)
        {[rst, clk]}
        
        (* Local variables. *)
        []

        (* Process body. *)
        (
          If (#rst @= false)
             Then (s_firable @<== false)
             Else (
               Falling (s_firable @<== #s_firing_condition)
             )
        ).

(** Process "fired_evaluation". *)

(* Process id. *)
Definition fired_evaluation : ident := firable + 1.

(* Process "fired_evaluation" declaration. *)

Definition fired_evaluation_ps :=
  cs_ps fired_evaluation
        (* Sensitivity list. *)
        {[s_firable, s_priority_combination]}
        
        (* Local variables. *)
        []

        (* Process body. *)
        (s_fired @<== (#s_firable @&& #s_priority_combination)).

(** Process "publish_fired". *)

(* Process id. *)
Definition publish_fired : ident := fired_evaluation + 1.

(* Process "publish_fired" declaration. *)

Definition publish_fired_ps :=
  cs_ps publish_fired
        (* Sensitivity list. *)
        {[s_fired]}
        
        (* Local variables. *)
        []

        (* Process body. *)
        (fired @<== #s_fired).

(** Declaration of the Transition design behavior. *)

Definition transition_behavior : cs :=
  (condition_evaluation_ps
     // enable_evaluation_ps
     // reinit_time_counter_evaluation_ps
     // time_counter_ps
     // firing_condition_evaluation_ps
     // priority_authorization_evaluation_ps
     // firable_ps
     // fired_evaluation_ps
     // publish_fired_ps).

(** ** Declaration of the Place design. *)

Definition transition_design : design :=
  design_ transition_entid
          transition_archid
          transition_gens
          transition_ports
          transition_sigs
          transition_behavior.

