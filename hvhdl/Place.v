(** * Definition of the HILECOP's Place design in H-VHDL abstract syntax. *)

(** Defines the Place design used in the generation of
    VHDL listing from SITPNs. *)

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

Include HVhdlSsNotations.
Include HVhdlCsNotations.

(** Loop variable and local variable first fresh identifiers. *)

Local Definition i := 50.
Local Definition local_var_ffid := 51.

(** ** Entity part of the Place design. *)

(** *** Generic constants of the Place design. *)

(** Defines the identifiers of generic constants.
    
    Begins the identifier with 1, since 0 is reserved for the clock
    input port.  *)

Definition input_arcs_number  : ident := 1.
Definition output_arcs_number : ident := 2.
Definition maximal_marking    : ident := 3.

(** Defines the generic clause of the Place design. *)

Definition place_gens : list gdecl :=
  [gdecl_ input_arcs_number  (tind_natural 0%N NATMAX) 1%N;
   gdecl_ output_arcs_number (tind_natural 0%N NATMAX) 1%N;
   gdecl_ maximal_marking    (tind_natural 0%N NATMAX) 1%N].

(** *** Ports of the Place design. *)

(** Input ports identifiers. *)

Definition initial_marking          : ident := 4.
Definition input_arcs_weights       : ident := 5.
Definition output_arcs_types        : ident := 6.
Definition output_arcs_weights      : ident := 7.
Definition input_transitions_fired  : ident := 8.
Definition output_transitions_fired : ident := 9.

(** Output ports identifiers. *)

Definition output_arcs_valid       : ident := 10.
Definition priority_authorizations : ident := 11.
Definition reinit_transitions_time : ident := 12.
Definition marked                  : ident := 13.

(** Port clause of the Place design. *)

(* Expression "output_arcs_number - 1" and "input_arcs_number - 1". 
   Used in the range constraints of port type indications.
 *)

Definition out_arcs_nb_minus_1 := #output_arcs_number @- 1%N.
Definition in_arcs_nb_minus_1 := #input_arcs_number @- 1%N.

(* Port clause. *)

Open Scope N_scope.

Definition place_ports : list pdecl :=
  [
    (* Input ports. *)
  pdecl_in clk                      tind_boolean;
  pdecl_in initial_marking          (tind_natural 0%N (#maximal_marking));
  pdecl_in input_arcs_weights       (weight_vector_t 0%N (#input_arcs_number @- 1%N));
  pdecl_in output_arcs_types        (arc_vector_t 0%N (#output_arcs_number @- 1%N));
  pdecl_in output_arcs_weights      (weight_vector_t 0%N (#output_arcs_number @- 1%N));
  pdecl_in input_transitions_fired  (bool_vector_t 0 (#output_arcs_number @- 1));
  pdecl_in output_transitions_fired (bool_vector_t 0 (#output_arcs_number @- 1));

  (* Output ports. *)
  pdecl_out output_arcs_valid       (bool_vector_t 0 (#output_arcs_number @- 1));
  pdecl_out priority_authorizations (bool_vector_t 0 (#output_arcs_number @- 1));
  pdecl_out reinit_transitions_time (bool_vector_t 0 (#output_arcs_number @- 1));
  pdecl_out marked                  tind_boolean
  ].

(** ** Architecture part of the Place design. *)

(** *** Architecture declarative part of the Place design. *)

(* Macro for a type indication used in the architecture declarative
   part of the Place design.  *)

Definition local_weight_t := tind_natural 0 (#maximal_marking).

(** Declared signal identifiers. *)

Definition s_input_token_sum : ident := 14%nat.
Definition s_marking : ident := 15%nat.
Definition s_output_token_sum : ident := 16%nat.

(** Architecture declaration list. *)

Definition place_sigs : list sdecl :=
  [
  sdecl_ s_input_token_sum  local_weight_t;
  sdecl_ s_marking          local_weight_t;
  sdecl_ s_output_token_sum local_weight_t
  ].

(** *** Architecture behavioral part of the Place design. *)

(** Defines the architecture behavioral part of the Place design
    proceeding process by process.
 *)

(** Process "input_tokens_sum". *)

(* Process id. *)
Definition input_tokens_sum : ident := 17.

(* Process "input_tokens_sum" declarative part. *)

Definition v_internal_input_token_sum : ident := local_var_ffid.

(* Process "input_tokens_sum" declaration. *)

Definition input_tokens_sum_ps :=
  cs_ps input_tokens_sum

        (* Sensitivity list. *)
        {[input_transitions_fired, input_arcs_weights]}
        
        (* Local variables. *)
        [vdecl_ v_internal_input_token_sum local_weight_t]

        (* Process body. *)
        (
          ($v_internal_input_token_sum @:= 0);;

          (For i InR 0 To (#input_arcs_number @- 1) Loop
               (If (input_transitions_fired[[ #i ]] @= true) Then
                   $v_internal_input_token_sum @:= (#v_internal_input_token_sum @+ (input_arcs_weights[[ #i ]])))
          );;
         
          ($s_input_token_sum @<== #v_internal_input_token_sum)
        ).

(** Process "output_tokens_sum". *)

(* Process id. *)
Definition output_tokens_sum : ident := 18.

(* Process "output_tokens_sum" declarative part. *)

Definition v_internal_output_token_sum : ident := local_var_ffid.

(* Process "output_tokens_sum" declaration. *)

Definition output_tokens_sum_ps :=
  cs_ps output_tokens_sum
        
        (* Sensitivity list. *)
        {[output_arcs_types, output_arcs_weights, output_transitions_fired]}

        (* Local variables. *)
        [vdecl_ v_internal_output_token_sum local_weight_t]
        
        (* Process body. *)
        (
          ($v_internal_output_token_sum @:= 0);;

          (For i InR 0 To (#output_arcs_number @- 1) Loop 
               (If ((output_transitions_fired[[ #i ]] @= true) @&& (output_arcs_types[[ #i ]] @= basic)) Then
                   $v_internal_output_token_sum @:= (#v_internal_output_token_sum @+ (output_arcs_weights[[ #i ]])))
          );;
         
          ($s_output_token_sum @<== #v_internal_output_token_sum)
        ).

(** Process "marking". *)

(* Process id. *)
Definition marking : ident := 19.

(* Process "marking" declaration. *)

Definition marking_ps :=
  cs_ps marking
        
        (* Sensitivity list. *)
        {[clk, initial_marking]}

        (* Local variables. *)
        []

        (* Process body. *)
        
        (Rst ($s_marking @<== #initial_marking)
             Else (
               Rising ($s_marking @<== (#s_marking @+ (#s_input_token_sum @- #s_output_token_sum)))
             )
        ).

(** Process "determine_marked". *)

(* Process id. *)
Definition determine_marked : ident := 20.

(* Process "determine_marked" declaration. *)

Definition determine_marked_ps :=
  cs_ps determine_marked
        
        (* Sensitivity list. *)
        {[s_marking]}

        (* Local variables. *)
        []

        (* Process body. *)
        ($marked @<== (#s_marking @/= 0)).

(** Process "marking_validation_evaluation". *)

(* Process id. *)
Definition marking_validation_evaluation := 21.

(* Process "marking_validation_evaluation" declaration. *)
Definition marking_validation_evaluation_ps :=
  cs_ps marking_validation_evaluation
        
        (* Sensitivity list *)
        {[output_arcs_types, output_arcs_weights, s_marking]} 

        (* Local variables. *)
        []

        (* Process body. *)
        (For i InR 0 To (#output_arcs_number @- 1) Loop (
             If ((((output_arcs_types[[ #i ]] @= basic) @|| (output_arcs_types[[ #i ]] @= test))
                    @&& (#s_marking @>= (output_arcs_weights[[ #i ]])))
                   @|| ((output_arcs_types[[ #i ]] @= inhibitor) @&& (#s_marking @< (output_arcs_weights[[ #i ]]))))
             Then (output_arcs_valid $[[ #i ]] @<== true)
             Else (output_arcs_valid $[[ #i ]] @<== false)
             )
        ).

(** Process "priority_evaluation". *)

(* Process id. *)
Definition priority_evaluation := 22.

(* Process "priority_evaluation" local variables. *)
Definition v_saved_output_token_sum : ident := local_var_ffid.

(* Process "priority_evaluation" declaration. *)
Definition priority_evaluation_ps :=
  cs_ps
    priority_evaluation
    
    (* Sensitivity list. *)
    {[output_arcs_types, output_arcs_weights, output_transitions_fired, s_marking]}
    
    (* Local variables. *)
    [vdecl_ v_saved_output_token_sum local_weight_t]
    
    (* Process body. *)
    (($v_saved_output_token_sum @:= 0);;
     
     (For i InR 0 To (#output_arcs_number @- 1) Loop
          ((If (#s_marking @>= (#v_saved_output_token_sum @+ (output_arcs_weights[[ #i ]])))
               Then (priority_authorizations $[[ #i ]] @<== true)
               Else (priority_authorizations $[[ #i ]] @<== false));;
           
           (If ((output_transitions_fired[[ #i ]] @= true) @&& (output_arcs_types[[ #i ]] @= basic))
               Then ($v_saved_output_token_sum @:= (#v_saved_output_token_sum @+ (output_arcs_weights[[ #i ]]))))))).

(** Process "reinit_transitions_time_evaluation". *)

(* Process id. *)
Definition reinit_transitions_time_evaluation := 23.

(* Process "priority_evaluation" declaration. *)

Definition reinit_transitions_time_evaluation_ps :=
  cs_ps
    reinit_transitions_time_evaluation
    
    (* Sensitivity list. *)
    {[clk]}

    (* Local variables. *)
    []

    (* Process body. *)
    (Rst (For i InR 0 To (#output_arcs_number @- 1) Loop (reinit_transitions_time $[[ #i ]] @<== false))
         Else (Rising
                 (For i InR 0 To (#output_arcs_number @- 1) Loop
                      (If (((output_arcs_types[[ #i ]] @= basic @|| (output_arcs_types[[ #i ]] @= test))
                              @&& ((#s_marking @- #s_output_token_sum) @< (output_arcs_weights[[ #i ]]))
                              @&& (#s_output_token_sum @> 0))
                             @|| (output_transitions_fired[[ #i ]] @= true))
                          Then (reinit_transitions_time $[[ #i ]] @<== true)
                          Else (reinit_transitions_time $[[ #i ]] @<== false))))).

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
          place_sigs
          place_behavior.

