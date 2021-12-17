(** * Definition of the HILECOP's Transition design in H-VHDL abstract syntax. *)

(** Defines the Transition design used in the generation of
    VHDL listing from SITPNs.
 *)

Require Import common.CoqLib.
Require Import common.GlobalTypes.
Require Import common.NatMap.
Require Import common.NatSet.

Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.Petri.
Require Import hvhdl.HVhdlTypes.

Open Scope natset_scope.
Open Scope abss_scope.

Include HVhdlCsNotations.

Local Definition i := 50.
Local Definition local_var_ffid := 51.

(** ** Entity part of the Transition design. *)

(** *** Generic constants of the Transition design. *)

(** Defines the identifiers of generic constants.
    
    Begins the identifier with 1, since 0 is reserved for the clock
    input port. *)

Definition transition_type      : ident := 1.
Definition input_arcs_number    : ident := 2.
Definition conditions_number    : ident := 3.
Definition maximal_time_counter : ident := 4.

(** Defines the generic clause of the Transition design. *)

Definition transition_gens : list gdecl :=
  [gdecl_ transition_type     transition_t not_temporal;
  gdecl_ input_arcs_number    (tind_natural 0 NATMAX) 1;
  gdecl_ conditions_number    (tind_natural 0 NATMAX) 1;
  gdecl_ maximal_time_counter (tind_natural 0 NATMAX) 1].

(** *** Ports of the Transition design. *)

(** Input ports identifiers. *)

Definition input_conditions        : ident := 5.
Definition time_A_value            : ident := 6.
Definition time_B_value            : ident := 7.
Definition input_arcs_valid        : ident := 8.
Definition reinit_time             : ident := 9.
Definition priority_authorizations : ident := 10.

(** Output ports identifiers. *)

Definition fired                   : ident := 11.

(** Port clause of the Transition design. *)

Definition transition_ports : list pdecl :=
  [
  (* Input ports. *)
  pdecl_in clk                     tind_boolean;
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

Definition s_condition_combination : ident := 12. 
Definition s_enabled : ident := 13.
Definition s_firable : ident := 14. 
Definition s_firing_condition : ident := 16.
Definition s_priority_combination : ident := 17.
Definition s_reinit_time_counter : ident := 18.
Definition s_time_counter : ident := 19.

(** Architecture declaration list. *)

Definition transition_sigs : list sdecl :=
  [
  sdecl_ s_condition_combination tind_boolean;
  sdecl_ s_enabled               tind_boolean;
  sdecl_ s_firable               tind_boolean;
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
Definition condition_evaluation : ident := 20.

(* Process "condition_evaluation" declarative part. *)

Definition v_internal_condition : ident := local_var_ffid.

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
Definition enable_evaluation : ident := 21.

(* Process "enable_evaluation" declarative part. *)

Definition v_internal_enabled : ident := local_var_ffid.

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
Definition reinit_time_counter_evaluation : ident := 22.

(* Process "reinit_time_counter_evaluation" declarative part. *)

Definition v_internal_reinit_time_counter : ident := local_var_ffid.

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
Definition time_counter : ident := 23.

(* Process "time_counter" declaration. *)

Definition time_counter_ps :=
  cs_ps time_counter

        (* Sensitivity list. *)
        {[clk]}
        
        (* Local variables. *)
        []

        (* Process body. *)
        (
          Rst (s_time_counter @<== 0)
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
Definition firing_condition_evaluation : ident := 24.

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
Definition priority_authorization_evaluation : ident := 25.

(* Process "priority_authorization_evaluation" declarative part. *)

Definition v_priority_combination : ident := local_var_ffid.

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
Definition firable : ident := 26.

(* Process "firable" declaration. *)

Definition firable_ps :=
  cs_ps firable
        (* Sensitivity list. *)
        {[clk]}
        
        (* Local variables. *)
        []

        (* Process body. *)
        (
          Rst (s_firable @<== false)
              Else (
                Falling (s_firable @<== #s_firing_condition)
              )
        ).

(** Process "fired_evaluation". *)

(* Process id. *)
Definition fired_evaluation : ident := 27.

(* Process "fired_evaluation" declaration. *)

Definition fired_evaluation_ps :=
  cs_ps fired_evaluation
        (* Sensitivity list. *)
        {[s_firable, s_priority_combination]}
        
        (* Local variables. *)
        []

        (* Process body. *)
        (fired @<== (#s_firable @&& #s_priority_combination)).

(** Declaration of the Transition design behavior. *)

Definition transition_behavior : cs :=
  (condition_evaluation_ps
     // enable_evaluation_ps
     // reinit_time_counter_evaluation_ps
     // time_counter_ps
     // firing_condition_evaluation_ps
     // priority_authorization_evaluation_ps
     // firable_ps
     // fired_evaluation_ps).

(** ** Declaration of the Place design. *)

Definition transition_design : design :=
  design_ transition_entid
          transition_archid
          transition_gens
          transition_ports
          transition_sigs
          transition_behavior.

