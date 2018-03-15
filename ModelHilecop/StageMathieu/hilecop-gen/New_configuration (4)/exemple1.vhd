--------------------------------------------------------------------
-- COPYRIGHT (c) ABC, 2017
-- The copyright to the document herein is the property of ABC.
--
-- All rights reserved.
--------------------------------------------------------------------
--
-- Author: Guillaume Souquet, Ronald Reboul, Arthur Hiairrassary
-- Created: 12-03-2018 15:35
--
--------------------------------------------------------------------
-- Description:
--
-- This is the top design unit of the whole design hierarchy.
-- It mainly instantiates the sub-components of the HILECOP
-- methodology and their connections.
-- TODO
-- TODO Component:
-- TODO Name : exemple1
-- TODO Author : 
-- TODO Description : 
-- TODO Version : 
-- TODO
-- TODO HILECOP version: 7.0.17
-- TODO Traduction version: Place-Pivot 1.0.0
-- TODO Maximal global marking: 255
--
--------------------------------------------------------------------
-- VHDL dialect: VHDL '93
--
--------------------------------------------------------------------

----------------------------------------
-- Libraries
----------------------------------------
library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.petri.all;


----------------------------------------
-- exemple1 entity declaration
----------------------------------------
entity exemple1 is
   port(
      clock : in std_logic; -- Entity clock
      reset_n : in std_logic -- Active low asynchronous reset
   );
end entity exemple1;


----------------------------------------
-- exemple1 architecture
----------------------------------------
architecture exemple1_architecture of exemple1 is

   ----------------------------------------
   -- USER DECLARATION
   ----------------------------------------

   -- Constants

   -- Signals


   ----------------------------------------
   -- PETRI NET DECLARATION
   ----------------------------------------

   ----------------------------------------
   -- Arc declaration
   ----------------------------------------

   -- Arc type constants
   constant arc_type_basicarc_0 : arc_type_t := ARC_BASIC_PT;
   constant arc_type_basicarc_3 : arc_type_t := ARC_BASIC_PT;
   constant arc_type_basicarc_4 : arc_type_t := ARC_BASIC_PT;
   constant arc_type_inhibitorarc_0 : arc_type_t := ARC_INHIBITOR;
   constant arc_type_basicarc_7 : arc_type_t := ARC_BASIC_PT;
   constant arc_type_testarc_0 : arc_type_t := ARC_TEST;
   constant arc_type_basicarc_9 : arc_type_t := ARC_BASIC_PT;
   constant arc_type_basicarc_11 : arc_type_t := ARC_BASIC_PT;
   constant arc_type_basicarc_13 : arc_type_t := ARC_BASIC_PT;
   constant arc_type_basicarc_14 : arc_type_t := ARC_BASIC_PT;

   -- Arc weight constants
   constant arc_weight_basicarc_0 : weight_t := 1;
   constant arc_weight_basicarc_1 : weight_t := 2;
   constant arc_weight_basicarc_2 : weight_t := 1;
   constant arc_weight_basicarc_3 : weight_t := 2;
   constant arc_weight_basicarc_4 : weight_t := 1;
   constant arc_weight_basicarc_5 : weight_t := 1;
   constant arc_weight_inhibitorarc_0 : weight_t := 1;
   constant arc_weight_basicarc_6 : weight_t := 1;
   constant arc_weight_basicarc_7 : weight_t := 1;
   constant arc_weight_testarc_0 : weight_t := 1;
   constant arc_weight_basicarc_8 : weight_t := 1;
   constant arc_weight_basicarc_9 : weight_t := 1;
   constant arc_weight_basicarc_10 : weight_t := 1;
   constant arc_weight_basicarc_11 : weight_t := 1;
   constant arc_weight_basicarc_12 : weight_t := 1;
   constant arc_weight_basicarc_13 : weight_t := 1;
   constant arc_weight_basicarc_14 : weight_t := 1;
   constant arc_weight_basicarc_15 : weight_t := 1;

   -- Arc valid signals
   signal s_arc_valid_basicarc_0 : std_logic;
   signal s_arc_valid_basicarc_3 : std_logic;
   signal s_arc_valid_basicarc_4 : std_logic;
   signal s_arc_valid_inhibitorarc_0 : std_logic;
   signal s_arc_valid_basicarc_7 : std_logic;
   signal s_arc_valid_testarc_0 : std_logic;
   signal s_arc_valid_basicarc_9 : std_logic;
   signal s_arc_valid_basicarc_11 : std_logic;
   signal s_arc_valid_basicarc_13 : std_logic;
   signal s_arc_valid_basicarc_14 : std_logic;

   -- Priority authorization signals

   -- Reinitialisation time signals
   signal s_reinit_time_basicarc_0 : std_logic;
   signal s_reinit_time_basicarc_3 : std_logic;
   signal s_reinit_time_basicarc_4 : std_logic;
   signal s_reinit_time_inhibitorarc_0 : std_logic;
   signal s_reinit_time_basicarc_7 : std_logic;
   signal s_reinit_time_testarc_0 : std_logic;
   signal s_reinit_time_basicarc_9 : std_logic;
   signal s_reinit_time_basicarc_11 : std_logic;
   signal s_reinit_time_basicarc_13 : std_logic;
   signal s_reinit_time_basicarc_14 : std_logic;


   ----------------------------------------
   -- Place declaration
   ----------------------------------------

   -- Initial marking constants
   constant initial_marking_place_0 : weight_t := 1;
   constant initial_marking_place_1 : weight_t := 0;
   constant initial_marking_place_2 : weight_t := 0;
   constant initial_marking_place_3 : weight_t := 0;
   constant initial_marking_place_4 : weight_t := 0;
   constant initial_marking_place_5 : weight_t := 0;
   constant initial_marking_place_6 : weight_t := 0;

   -- Marked place signals


   ----------------------------------------
   -- Transition declaration
   ----------------------------------------

   -- Fired transition signals
   signal s_transition_fired_transition_0 : std_logic;
   signal s_transition_fired_transition_1 : std_logic;
   signal s_transition_fired_transition_2 : std_logic;
   signal s_transition_fired_transition_3 : std_logic;
   signal s_transition_fired_transition_4 : std_logic;
   signal s_transition_fired_transition_5 : std_logic;

   -- Fired exception transition signals

   -- Maximal time counter constants
   constant maximal_time_counter_transition_1 : natural := 5;
   constant maximal_time_counter_transition_5 : natural := 2;

   -- Static temporal transition constants
   constant time_A_transition_1 : natural := 3;
   constant time_B_transition_1 : natural := 5;
   constant time_A_transition_5 : natural := 2;

   -- Constant temporal transition constants

   -- Dynamic temporal transition signals
 
   -- Transition temporal time cleared signals

   -- True condition constant
   constant TRUE_CONDITION : std_logic := '1';

   -- Transition condition signals

   -- Exception asynchronous clear signals


   ----------------------------------------
   -- Macroplace declaration
   ----------------------------------------
   
   -- Macroplace asynchronous clear signals

   -- Enabled macroplace signals


   ----------------------------------------
   -- Declaration of action procedure
   ----------------------------------------


   ----------------------------------------
   -- Declaration of function procedure
   ----------------------------------------


   ----------------------------------------
   -- Declaration of dynamic time procedure
   ----------------------------------------

   
   ----------------------------------------
   -- Declaration of condition function
   ----------------------------------------


begin

   ----------------------------------------
   -- Instanciation of place
   ----------------------------------------

   ----------------------------------------
   -- PLACE
   --    Name: place_0
   --    Initial marking: 1
   place_0 : entity work.place
   generic map(
      input_arcs_number => 1,
      output_arcs_number => 2
   )
   port map(
      clock => clock,
      reset_n => reset_n,
      initial_marking => initial_marking_place_0,
      input_arcs_weights(0) => arc_weight_basicarc_15,
      output_arcs_types(0) => arc_type_basicarc_0,
      output_arcs_types(1) => arc_type_basicarc_7,
      output_arcs_weights(0) => arc_weight_basicarc_0,
      output_arcs_weights(1) => arc_weight_basicarc_7,
      input_transitions_fired(0) => s_transition_fired_transition_5,
      output_transitions_fired(0) => s_transition_fired_transition_0,
      output_transitions_fired(1) => s_transition_fired_transition_2,
      mp_asynchronous_clear => '0',
      output_arcs_valid(0) => s_arc_valid_basicarc_0,
      output_arcs_valid(1) => s_arc_valid_basicarc_7,
      priority_authorizations => open,
      reinit_transitions_time(0) => s_reinit_time_basicarc_0,
      reinit_transitions_time(1) => s_reinit_time_basicarc_7,
      marked => open
   );

   ----------------------------------------
   -- PLACE
   --    Name: place_1
   --    Initial marking: 0
   place_1 : entity work.place
   generic map(
      input_arcs_number => 2,
      output_arcs_number => 1
   )
   port map(
      clock => clock,
      reset_n => reset_n,
      initial_marking => initial_marking_place_1,
      input_arcs_weights(0) => arc_weight_basicarc_5,
      input_arcs_weights(1) => arc_weight_basicarc_12,
      output_arcs_types(0) => arc_type_basicarc_14,
      output_arcs_weights(0) => arc_weight_basicarc_14,
      input_transitions_fired(0) => s_transition_fired_transition_1,
      input_transitions_fired(1) => s_transition_fired_transition_4,
      output_transitions_fired(0) => s_transition_fired_transition_5,
      mp_asynchronous_clear => '0',
      output_arcs_valid(0) => s_arc_valid_basicarc_14,
      priority_authorizations => open,
      reinit_transitions_time(0) => s_reinit_time_basicarc_14,
      marked => open
   );

   ----------------------------------------
   -- PLACE
   --    Name: place_2
   --    Initial marking: 0
   place_2 : entity work.place
   generic map(
      input_arcs_number => 1,
      output_arcs_number => 1
   )
   port map(
      clock => clock,
      reset_n => reset_n,
      initial_marking => initial_marking_place_2,
      input_arcs_weights(0) => arc_weight_basicarc_1,
      output_arcs_types(0) => arc_type_basicarc_3,
      output_arcs_weights(0) => arc_weight_basicarc_3,
      input_transitions_fired(0) => s_transition_fired_transition_0,
      output_transitions_fired(0) => s_transition_fired_transition_1,
      mp_asynchronous_clear => '0',
      output_arcs_valid(0) => s_arc_valid_basicarc_3,
      priority_authorizations => open,
      reinit_transitions_time(0) => s_reinit_time_basicarc_3,
      marked => open
   );

   ----------------------------------------
   -- PLACE
   --    Name: place_3
   --    Initial marking: 0
   place_3 : entity work.place
   generic map(
      input_arcs_number => 1,
      output_arcs_number => 1
   )
   port map(
      clock => clock,
      reset_n => reset_n,
      initial_marking => initial_marking_place_3,
      input_arcs_weights(0) => arc_weight_basicarc_2,
      output_arcs_types(0) => arc_type_basicarc_4,
      output_arcs_weights(0) => arc_weight_basicarc_4,
      input_transitions_fired(0) => s_transition_fired_transition_0,
      output_transitions_fired(0) => s_transition_fired_transition_1,
      mp_asynchronous_clear => '0',
      output_arcs_valid(0) => s_arc_valid_basicarc_4,
      priority_authorizations => open,
      reinit_transitions_time(0) => s_reinit_time_basicarc_4,
      marked => open
   );

   ----------------------------------------
   -- PLACE
   --    Name: place_4
   --    Initial marking: 0
   place_4 : entity work.place
   generic map(
      input_arcs_number => 1,
      output_arcs_number => 3
   )
   port map(
      clock => clock,
      reset_n => reset_n,
      initial_marking => initial_marking_place_4,
      input_arcs_weights(0) => arc_weight_basicarc_6,
      output_arcs_types(0) => arc_type_inhibitorarc_0,
      output_arcs_types(1) => arc_type_testarc_0,
      output_arcs_types(2) => arc_type_basicarc_13,
      output_arcs_weights(0) => arc_weight_inhibitorarc_0,
      output_arcs_weights(1) => arc_weight_testarc_0,
      output_arcs_weights(2) => arc_weight_basicarc_13,
      input_transitions_fired(0) => s_transition_fired_transition_0,
      output_transitions_fired(0) => s_transition_fired_transition_0,
      output_transitions_fired(1) => s_transition_fired_transition_2,
      output_transitions_fired(2) => s_transition_fired_transition_4,
      mp_asynchronous_clear => '0',
      output_arcs_valid(0) => s_arc_valid_inhibitorarc_0,
      output_arcs_valid(1) => s_arc_valid_testarc_0,
      output_arcs_valid(2) => s_arc_valid_basicarc_13,
      priority_authorizations => open,
      reinit_transitions_time(0) => s_reinit_time_inhibitorarc_0,
      reinit_transitions_time(1) => s_reinit_time_testarc_0,
      reinit_transitions_time(2) => s_reinit_time_basicarc_13,
      marked => open
   );

   ----------------------------------------
   -- PLACE
   --    Name: place_5
   --    Initial marking: 0
   place_5 : entity work.place
   generic map(
      input_arcs_number => 1,
      output_arcs_number => 1
   )
   port map(
      clock => clock,
      reset_n => reset_n,
      initial_marking => initial_marking_place_5,
      input_arcs_weights(0) => arc_weight_basicarc_8,
      output_arcs_types(0) => arc_type_basicarc_9,
      output_arcs_weights(0) => arc_weight_basicarc_9,
      input_transitions_fired(0) => s_transition_fired_transition_2,
      output_transitions_fired(0) => s_transition_fired_transition_3,
      mp_asynchronous_clear => '0',
      output_arcs_valid(0) => s_arc_valid_basicarc_9,
      priority_authorizations => open,
      reinit_transitions_time(0) => s_reinit_time_basicarc_9,
      marked => open
   );

   ----------------------------------------
   -- PLACE
   --    Name: place_6
   --    Initial marking: 0
   place_6 : entity work.place
   generic map(
      input_arcs_number => 1,
      output_arcs_number => 1
   )
   port map(
      clock => clock,
      reset_n => reset_n,
      initial_marking => initial_marking_place_6,
      input_arcs_weights(0) => arc_weight_basicarc_10,
      output_arcs_types(0) => arc_type_basicarc_11,
      output_arcs_weights(0) => arc_weight_basicarc_11,
      input_transitions_fired(0) => s_transition_fired_transition_3,
      output_transitions_fired(0) => s_transition_fired_transition_4,
      mp_asynchronous_clear => '0',
      output_arcs_valid(0) => s_arc_valid_basicarc_11,
      priority_authorizations => open,
      reinit_transitions_time(0) => s_reinit_time_basicarc_11,
      marked => open
   );


   ----------------------------------------
   -- Instanciation of transition
   ----------------------------------------

   ----------------------------------------
   -- TRANSITION
   --    Name: transition_0
   --    Type: TRANSITION_NOT_TEMPORAL
   transition_0 : entity work.transition 
   generic map(
      transition_type => TRANSITION_NOT_TEMPORAL,
      input_arcs_number => 2,
      conditions_number => 1,
      maximal_time_counter => 1
   )
   port map(
      clock => clock,
      reset_n => reset_n,
      input_conditions(0) => TRUE_CONDITION,
      time_A_value => 0,
      time_B_value => 0,
      input_arcs_valid(0) => s_arc_valid_basicarc_0,
      input_arcs_valid(1) => s_arc_valid_inhibitorarc_0,
      reinit_time(0) => s_reinit_time_basicarc_0,
      reinit_time(1) => s_reinit_time_inhibitorarc_0,
      mp_asynchronous_clear => '0',
      priority_authorization => '1',
      exception_asynchronous_clear => '1',
      exception_fired => open,
      fired => s_transition_fired_transition_0,
      time_cleared => open
   );

   ----------------------------------------
   -- TRANSITION
   --    Name: transition_1
   --    Type: TRANSITION_TEMPORAL_A_B
   transition_1 : entity work.transition 
   generic map(
      transition_type => TRANSITION_TEMPORAL_A_B,
      input_arcs_number => 2,
      conditions_number => 1,
      maximal_time_counter => maximal_time_counter_transition_1
   )
   port map(
      clock => clock,
      reset_n => reset_n,
      input_conditions(0) => TRUE_CONDITION,
      time_A_value => time_A_transition_1,
      time_B_value => time_B_transition_1,
      input_arcs_valid(0) => s_arc_valid_basicarc_3,
      input_arcs_valid(1) => s_arc_valid_basicarc_4,
      reinit_time(0) => s_reinit_time_basicarc_3,
      reinit_time(1) => s_reinit_time_basicarc_4,
      mp_asynchronous_clear => '0',
      priority_authorization => '1',
      exception_asynchronous_clear => '1',
      exception_fired => open,
      fired => s_transition_fired_transition_1,
      time_cleared => open
   );

   ----------------------------------------
   -- TRANSITION
   --    Name: transition_2
   --    Type: TRANSITION_NOT_TEMPORAL
   transition_2 : entity work.transition 
   generic map(
      transition_type => TRANSITION_NOT_TEMPORAL,
      input_arcs_number => 2,
      conditions_number => 1,
      maximal_time_counter => 1
   )
   port map(
      clock => clock,
      reset_n => reset_n,
      input_conditions(0) => TRUE_CONDITION,
      time_A_value => 0,
      time_B_value => 0,
      input_arcs_valid(0) => s_arc_valid_basicarc_7,
      input_arcs_valid(1) => s_arc_valid_testarc_0,
      reinit_time(0) => s_reinit_time_basicarc_7,
      reinit_time(1) => s_reinit_time_testarc_0,
      mp_asynchronous_clear => '0',
      priority_authorization => '1',
      exception_asynchronous_clear => '1',
      exception_fired => open,
      fired => s_transition_fired_transition_2,
      time_cleared => open
   );

   ----------------------------------------
   -- TRANSITION
   --    Name: transition_3
   --    Type: TRANSITION_NOT_TEMPORAL
   transition_3 : entity work.transition 
   generic map(
      transition_type => TRANSITION_NOT_TEMPORAL,
      input_arcs_number => 1,
      conditions_number => 1,
      maximal_time_counter => 1
   )
   port map(
      clock => clock,
      reset_n => reset_n,
      input_conditions(0) => TRUE_CONDITION,
      time_A_value => 0,
      time_B_value => 0,
      input_arcs_valid(0) => s_arc_valid_basicarc_9,
      reinit_time(0) => s_reinit_time_basicarc_9,
      mp_asynchronous_clear => '0',
      priority_authorization => '1',
      exception_asynchronous_clear => '1',
      exception_fired => open,
      fired => s_transition_fired_transition_3,
      time_cleared => open
   );

   ----------------------------------------
   -- TRANSITION
   --    Name: transition_4
   --    Type: TRANSITION_NOT_TEMPORAL
   transition_4 : entity work.transition 
   generic map(
      transition_type => TRANSITION_NOT_TEMPORAL,
      input_arcs_number => 2,
      conditions_number => 1,
      maximal_time_counter => 1
   )
   port map(
      clock => clock,
      reset_n => reset_n,
      input_conditions(0) => TRUE_CONDITION,
      time_A_value => 0,
      time_B_value => 0,
      input_arcs_valid(0) => s_arc_valid_basicarc_11,
      input_arcs_valid(1) => s_arc_valid_basicarc_13,
      reinit_time(0) => s_reinit_time_basicarc_11,
      reinit_time(1) => s_reinit_time_basicarc_13,
      mp_asynchronous_clear => '0',
      priority_authorization => '1',
      exception_asynchronous_clear => '1',
      exception_fired => open,
      fired => s_transition_fired_transition_4,
      time_cleared => open
   );

   ----------------------------------------
   -- TRANSITION
   --    Name: transition_5
   --    Type: TRANSITION_TEMPORAL_A_INFINITE
   transition_5 : entity work.transition 
   generic map(
      transition_type => TRANSITION_TEMPORAL_A_INFINITE,
      input_arcs_number => 1,
      conditions_number => 1,
      maximal_time_counter => maximal_time_counter_transition_5
   )
   port map(
      clock => clock,
      reset_n => reset_n,
      input_conditions(0) => TRUE_CONDITION,
      time_A_value => time_A_transition_5,
      time_B_value => 0,
      input_arcs_valid(0) => s_arc_valid_basicarc_14,
      reinit_time(0) => s_reinit_time_basicarc_14,
      mp_asynchronous_clear => '0',
      priority_authorization => '1',
      exception_asynchronous_clear => '1',
      exception_fired => open,
      fired => s_transition_fired_transition_5,
      time_cleared => open
   );


   ----------------------------------------
   -- Instanciation of exception unit
   ----------------------------------------


   ----------------------------------------
   -- Instanciation of macroplace
   ----------------------------------------






   ----------------------------------------
   -- Combinatory assignment
   ----------------------------------------

   -- Assessment of condition

   -- Assessment of not condition signal

   -- Assessment of dynamic time condition

   -- Signal assignments

   -- Macroplace signal assignments

   -- Transition exception with multi macroplace signal assignments

   -- Static port assignments

   -- Static signal assignments
   
   -- Priority authorization signal assignments

   -- User raw code

end architecture exemple1_architecture;
