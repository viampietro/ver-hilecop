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
-- This entity describes the behavior of the exception unit used by
-- the HILECOP methodology.
-- TODO
-- TODO File name: exception_unit.vhd
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
-- exception unit entity declaration
----------------------------------------
entity exception_unit is
   generic(
      mp_places_number               : natural := 1; -- Number of places included in the macroplace
      mp_transitions_number          : natural := 1; -- Number of transitions included in the macroplace
      mp_temporal_transitions_number : natural := 1 -- Number of temporal transitions included in the macroplace
   );
   port(
      reset_n                         : in std_logic; -- Active low asynchronous reset
      mp_places_marked                : in std_logic_vector (mp_places_number-1 downto 0); -- Indicates if each place included in the macroplace is marked or not
      mp_transitions_fired            : in std_logic_vector (mp_transitions_number-1 downto 0); -- Indicates if each transition included in the macroplace is fired or not
      mp_temporal_transitions_cleared : in std_logic_vector (mp_temporal_transitions_number-1 downto 0); -- Indicates if each temporal transition is cleared or not
      exception_transition_fired      : in std_logic; -- Indicates if the exception transition is fired
      asynchronous_clear              : out std_logic -- Indicates if an asynchronous clear is needed
   );
end exception_unit;


----------------------------------------
-- exception unit architecture
----------------------------------------
architecture exception_unit_architecture of exception_unit is

   -- Signal declarations
   signal s_enable_d                 : std_logic; -- Indicates if the exception is enabled
   signal s_one_place_marked         : std_logic; -- Indicates if at least one place is marked
   signal s_one_time_counter_cleared : std_logic; -- Indicates if at least one time counter is cleared
   signal s_one_transition_fired     : std_logic; -- Indicates if at least one transition is fired
   signal s_reset_d                  : std_logic; -- Indicates if the exception is reseted
begin

   ------------------------------------------------------------
   -- Place marked evaluation process
   -- This combinational process evalutes if at least one place is marked
   -- (logic or between all places).
   place_marked_evaluation : process(mp_places_marked)
      variable v_internal_one_place_marked : std_logic; -- Logical combination of the place marked
   begin
      v_internal_one_place_marked := '0'; -- Initial value
      
      for i in 0 to mp_places_number - 1 loop
         v_internal_one_place_marked := v_internal_one_place_marked or mp_places_marked(i);
      end loop;
      
      s_one_place_marked <= v_internal_one_place_marked; -- Assignment of the result
   end process place_marked_evaluation;

   ------------------------------------------------------------
   -- Transition fired evaluation process
   -- This combinational process evalutes if at least one transition is fired
   -- (logic or between all transitions).
   transition_fired_evaluation : process(mp_transitions_fired)
      variable v_internal_one_transition_fired : std_logic; -- Logical combination of the transition fired
   begin
      v_internal_one_transition_fired := '0'; -- Initial value
      
      for i in 0 to mp_transitions_number - 1 loop
         v_internal_one_transition_fired := v_internal_one_transition_fired or mp_transitions_fired(i);
      end loop;
      
      s_one_transition_fired <= v_internal_one_transition_fired; -- Assignment of the result
   end process transition_fired_evaluation;

   ------------------------------------------------------------
   -- Temporal transition cleared evaluation process
   -- This combinational process evalutes if at least one time counter of
   -- a transition is cleared (logic or between all transitions).
   temporal_transition_cleared_evaluation : process(mp_temporal_transitions_cleared)
      variable v_internal_one_time_counter_cleared : std_logic; -- Logical combination of the time counter cleared
   begin
      v_internal_one_time_counter_cleared := '0'; -- Initial value
      
      for i in 0 to mp_temporal_transitions_number - 1 loop
         v_internal_one_time_counter_cleared := v_internal_one_time_counter_cleared or mp_temporal_transitions_cleared(i);
      end loop;
      
      s_one_time_counter_cleared <= v_internal_one_time_counter_cleared; -- Assignment of the result
   end process temporal_transition_cleared_evaluation;

   ------------------------------------------------------------
   
   -- TODO @Guillaume Add comment !
   s_reset_d <= not(reset_n) or ( not(s_one_place_marked) and not(s_one_transition_fired) and not(s_one_time_counter_cleared) and not(exception_transition_fired) );

   -- TODO @Guillaume Add comment !
   s_enable_d <= s_one_place_marked or s_one_transition_fired;

   ------------------------------------------------------------
   -- D flip-flop process
   -- This sequential process ... TODO @Guillaume Add comment !
   d_flip_flop : process(exception_transition_fired, s_reset_d)
   begin
      if (s_reset_d = '1') then
         asynchronous_clear <= '0';
      elsif rising_edge(exception_transition_fired) then
         if (s_enable_d = '1') then
            asynchronous_clear <= '1';
         end if;
      end if;
   end process d_flip_flop;

end exception_unit_architecture;
