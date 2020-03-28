(** * Definition of the HILECOP's Place design in H-VHDL abstract syntax. *)

(** Defines the Place design used in the generation of
    VHDL listing from SITPNs.
 *)

Require Import Coqlib.
Require Import GlobalTypes.
Require Import AbstractSyntax.
Require Import SemanticalDomains.
Require Import Petri.

Open Scope natset_scope.
Open Scope ast_scope.

(** ** Entity part of the Place design. *)

(** *** Generic constants of the Place design. *)

(** Defines the identifiers of generic constants.
    
    Begins with i + 1 as i is the last reserved identifier.  *)

Definition input_arcs_number  : ident := i + 1.
Definition output_arcs_number : ident := input_arcs_number + 1.
Definition maximal_marking    : ident := output_arcs_number + 1.

(** Defines the generic clause of the Place design. *)

Definition place_gens : list gdecl :=
  [gdecl_ input_arcs_number (tind_natural (e_nat 0, e_nat NATMAX)) (e_nat 1);
  gdecl_ output_arcs_number (tind_natural (e_nat 0, e_nat NATMAX)) (e_nat 1);
  gdecl_ maximal_marking (tind_natural (e_nat 0, e_nat NATMAX)) (e_nat 1)].

(** *** Ports of the Place design. *)

(** Input ports identifiers. *)

Definition initial_marking          : ident := maximal_marking + 1.
Definition input_arcs_weights       : ident := initial_marking + 1.
Definition output_arcs_types        : ident := input_arcs_weights + 1.
Definition output_arcs_weights      : ident := output_arcs_types + 1.
Definition input_transitions_fired  : ident := output_arcs_weights + 1.
Definition output_transitions_fired : ident := input_transitions_fired + 1.

(** Output ports identifiers. *)

Definition output_arcs_valid       : ident := output_transitions_fired + 1.
Definition priority_authorizations : ident := output_arcs_valid + 1.
Definition reinit_transitions_time : ident := priority_authorizations + 1.
Definition marked                  : ident := reinit_transitions_time + 1.

(** Port clause of the Place design. *)

(* Expression "output_arcs_number - 1" and "input_arcs_number - 1". 
   Used in the range constraints of port type indications.
 *)

Definition out_arcs_nb_minus_1 := #output_arcs_number @- (e_nat 1).
Definition in_arcs_nb_minus_1 := e_binop bo_sub (e_name (n_id input_arcs_number)) (e_nat 1).

(* Port clause. *)

Definition place_ports : list pdecl :=
  [
  (* Output ports. *)
  pdecl_in initial_marking          (tind_natural (e_nat 0, e_name (n_id maximal_marking)));
  pdecl_in input_arcs_weights       (weight_vector_t (e_nat 0, in_arcs_nb_minus_1));
  pdecl_in output_arcs_types        (arc_vector_t (e_nat 0, out_arcs_nb_minus_1));
  pdecl_in output_arcs_weights      (weight_vector_t (e_nat 0, out_arcs_nb_minus_1));
  pdecl_in input_transitions_fired  (bool_vector_t (e_nat 0, in_arcs_nb_minus_1));
  pdecl_in output_transitions_fired (bool_vector_t (e_nat 0, out_arcs_nb_minus_1));

  (* Input ports. *)
  pdecl_out output_arcs_valid       (bool_vector_t (e_nat 0, out_arcs_nb_minus_1));
  pdecl_out priority_authorizations (bool_vector_t (e_nat 0, out_arcs_nb_minus_1));
  pdecl_out reinit_transitions_time (bool_vector_t (e_nat 0, out_arcs_nb_minus_1));
  pdecl_out marked                  tind_boolean
  ].

(** ** Architecture part of the Place design. *)

(** *** Architecture declarative part of the Place design. *)

(* Macro for a type indication used in the architecture declarative
   part of the Place design.  *)

Definition local_weight_t := tind_natural (e_nat 0, e_name (n_id maximal_marking)).

(** Declared signal identifiers. *)

Definition s_input_token_sum : ident := marked + 1.
Definition s_marking : ident := s_input_token_sum + 1.
Definition s_output_token_sum : ident := s_marking + 1.

(** Architecture declaration list. *)

Definition place_adecls : list adecl :=
  [
  adecl_sig s_input_token_sum  local_weight_t;
  adecl_sig s_marking          local_weight_t;
  adecl_sig s_output_token_sum local_weight_t
  ].

(** *** Architecture behavioral part of the Place design. *)

(** Defines the architecture behavioral part of the Place design
    proceeding process by process.
 *)

(** Process "input_tokens_sum". *)

(* Process id. *)
Definition input_tokens_sum : ident := s_output_token_sum + 1.

(* Process "input_tokens_sum" declarative part. *)

Definition v_internal_input_token_sum : ident := local_var.

(* Process "input_tokens_sum" declaration. *)

Definition input_tokens_sum_ps :=
  cs_ps input_tokens_sum

        (* Sensitivity list. *)
        {input_transitions_fired, input_arcs_weights}
        
        (* Local variables. *)
        [vdecl_ v_internal_input_token_sum local_weight_t]

        (* Process body. *)
        (
          ($v_internal_input_token_sum @:= (e_nat 0));;

          (For i In (e_nat 0) To (#input_arcs_number @- (e_nat 1)) Loop
               (If (input_transitions_fired[[ #i ]] @= (e_bool true)) Then
                   $v_internal_input_token_sum @:= (#v_internal_input_token_sum @+ (input_arcs_weights[[ #i ]])))
          );;
         
          ($s_input_token_sum @<== #v_internal_input_token_sum)
        ).

(** Process "output_tokens_sum". *)

(* Process id. *)
Definition output_tokens_sum : ident := input_tokens_sum + 1.

(* Process "output_tokens_sum" declarative part. *)

Definition v_internal_output_token_sum : ident := local_var.

(* Process "output_tokens_sum" declaration. *)

Definition output_tokens_sum_ps :=
  cs_ps output_tokens_sum
        
        (* Sensitivity list. *)
        {output_arcs_types, output_arcs_weights, output_transitions_fired}

        (* Local variables. *)
        [vdecl_ v_internal_output_token_sum local_weight_t]
        
        (* Process body. *)
        (
          ($v_internal_output_token_sum @:= (e_nat 0));;

          (For i In (e_nat 0) To (#output_arcs_number @- (e_nat 1)) Loop 
               (If ((output_transitions_fired[[ #i ]] @= (e_bool true)) @&& (output_arcs_types[[ #i ]] @= (e_arc basic))) Then
                   $v_internal_output_token_sum @:= (#v_internal_output_token_sum @+ (output_arcs_weights[[ #i ]])))
          );;
         
          ($s_output_token_sum @<== #v_internal_output_token_sum)
        ).

(** Process "marking". *)

(* Process id. *)
Definition marking : ident := output_tokens_sum + 1.

(* Process "marking" declaration. *)

Definition marking_ps :=
  cs_ps marking
        
        (* Sensitivity list. *)
        {clk, rst, initial_marking}

        (* Local variables. *)
        []

        (* Process body. *)
        
        (If (#rst @= (e_bool false))
            Then ($s_marking @<== #initial_marking)
            Else (
              Rising ($s_marking @<== (#s_marking @+ (#s_input_token_sum @- #s_output_token_sum)))
            )
        ).

(** Process "determine_marked". *)

(* Process id. *)
Definition determine_marked : ident := marking + 1.

(* Process "determine_marked" declaration. *)

Definition determine_marked_ps :=
  cs_ps determine_marked
        
        (* Sensitivity list. *)
        {s_marking}s

        (* Local variables. *)
        []

        (* Process body. *)
        ($marked @<== (#s_marking @/= (e_nat 0))).

(** Process "marking_validation_evaluation". *)

(* Process id. *)
Definition marking_validation_evaluation := determine_marked + 1.

(* Process "marking_validation_evaluation" declaration. *)
Definition marking_validation_evaluation_ps :=
  cs_ps marking_validation_evaluation
        
        (* Sensitivity list *)
        {output_arcs_types, output_arcs_weights, s_marking} 

        (* Local variables. *)
        []

        (* Process body. *)
        (For i In (e_nat 0) To (#output_arcs_number @- (e_nat 1)) Loop (
             If ((((output_arcs_types[[ #i ]] @= (e_arc basic)) @|| (output_arcs_types[[ #i ]] @= (e_arc test)))
                    @&& (#s_marking @>= (output_arcs_weights[[ #i ]])))
                   @|| ((output_arcs_types[[ #i ]] @= (e_arc inhibitor)) @&& (#s_marking @< (output_arcs_weights[[ #i ]]))))
             Then (output_arcs_valid $[[ #i ]] @<== (e_bool true))
             Else (output_arcs_valid $[[ #i ]] @<== (e_bool false))
             )
        ).

(** Process "priority_evaluation". *)

(* Process id. *)
Definition priority_evaluation := marking_validation_evaluation + 1.

(* Process "priority_evaluation" local variables. *)
Definition v_saved_output_token_sum : ident := local_var.

(* Process "priority_evaluation" declaration. *)
Definition priority_evaluation_ps :=
  cs_ps
    priority_evaluation
    
    (* Sensitivity list. *)
    {output_arcs_types, output_arcs_weights, output_transitions_fired, s_marking}
    
    (* Local variables. *)
    [vdecl_ v_saved_output_token_sum local_weight_t]
    
    (* Process body. *)
    (($v_saved_output_token_sum @:= (e_nat 0));;
     
     (For i In (e_nat 0) To (#output_arcs_number @- (e_nat 1)) Loop
          ((If (#s_marking @>= (#v_saved_output_token_sum @+ (output_arcs_weights[[ #i ]])))
               Then (priority_authorizations $[[ #i ]] @<== (e_bool true))
               Else (priority_authorizations $[[ #i ]] @<== (e_bool false)));;
           
           (If ((output_transitions_fired[[ #i ]] @= (e_bool true)) @&& (output_arcs_types[[ #i ]] @= (e_arc basic)))
               Then ($v_saved_output_token_sum @:= (#v_saved_output_token_sum @+ (output_arcs_weights[[ #i ]]))))))).

(** Process "reinit_transitions_time_evaluation". *)

(* Process id. *)
Definition reinit_transitions_time_evaluation := priority_evaluation + 1.

(* Process "priority_evaluation" declaration. *)

Definition reinit_transitions_time_evaluation_ps :=
  cs_ps
    reinit_transitions_time_evaluation
    
    (* Sensitivity list. *)
    {clk, rst}

    (* Local variables. *)
    []

    (* Process body. *)
    (If (#rst @= (e_bool false))
        Then (For i In (e_nat 0) To (#output_arcs_number @- (e_nat 1)) Loop (reinit_transitions_time $[[ #i ]] @<== (e_bool false)))
        Else (Rising
                (For i In (e_nat 0) To (#output_arcs_number @- (e_nat 1)) Loop
                     (If ((output_arcs_types[[ #i ]] @= (e_arc basic) @|| (output_arcs_types[[ #i ]] @= (e_arc test)))
                            @&& ((#s_marking @- #s_output_token_sum) @< (output_arcs_weights[[ #i ]]))
                            @&& (#s_output_token_sum @> (e_nat 0)))
                      Then (reinit_transitions_time $[[ #i ]] @<== (e_bool true))
                      Else (reinit_transitions_time $[[ #i ]] @<== (e_bool false)))))).

(** Declaration of the Place design behavior. *)

Definition place_behavior : cs :=
  (input_tokens_sum_ps
     // output_tokens_sum_ps
     // marking_ps
     // determine_marked_ps
     // marking_validation_evaluation_ps
     // priority_evaluation_ps
     // reinit_transitions_time_evaluation_ps).

(** ** Declaration of the Place design. *)

Definition place_design : design :=
  design_ place_entid
          place_archid
          place_gens
          place_ports
          place_adecls
          place_behavior.

