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
-- This entity describes the behavior of the petri net transition
-- component in the HILECOP methodology.
-- TODO
-- TODO File name: transition.vhd
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
-- transition entity declaration
----------------------------------------
entity transition is
   generic(
      transition_type      : transition_type_t := TRANSITION_NOT_TEMPORAL; -- Temporal type of the transition 
      input_arcs_number    : natural := 1; -- Number of input arcs
      conditions_number    : natural := 1; -- Number of conditions
      maximal_time_counter : natural := 255 -- Maximal time reachable by the counter
   );
   port(
      clock                        : in std_logic; -- Entity clock
      reset_n                      : in std_logic; -- Active low asynchronous reset
      input_conditions             : in std_logic_vector(conditions_number-1 downto 0); -- Logic result of each of the conditions
      time_A_value                 : in natural range 0 to maximal_time_counter; -- Value of interval time A
      time_B_value                 : in natural range 0 to maximal_time_counter; -- Value of interval time B
      input_arcs_valid             : in std_logic_vector(input_arcs_number-1 downto 0); -- Indicates if the marking is valid for all input arcs
      reinit_time                  : in std_logic_vector(input_arcs_number-1 downto 0); -- Indicates if the time counter needs to be reinitialised
      mp_asynchronous_clear        : in std_logic; -- Macroplace active high asynchronous clear
      priority_authorization       : in std_logic; -- Indicates if the transition has the authorization to be fired
      exception_asynchronous_clear : in std_logic; -- Exception active high asynchronous clear (only for exception transition)
      exception_fired              : out std_logic; -- Indicates if the exception transition is fired or not (only for exception transition)
      fired                        : out std_logic; -- Indicates if the transition is fired or not
      time_cleared                 : out std_logic -- Indicates if the time counter is cleared or not
   );
end transition;


----------------------------------------
-- transition architecture
----------------------------------------
architecture transition_architecture of transition is

   -- Signal declarations
   signal s_condition_combination : std_logic; -- Indicates if all conditions are true or false
   signal s_enabled               : std_logic; -- Indicates if the transition is enabled or not
   signal s_exception_firable     : std_logic; -- Indicates if the exception transition is firable
   signal s_firable               : std_logic; -- Indicates if the transition is firable or not
   signal s_fired                 : std_logic; -- Indicates if the transition is fired or not
   signal s_firing_condition      : std_logic; -- Indicates if the firing condition is true or false
   signal s_reinit_time_counter   : std_logic; -- Indicates if the transition need to be cleared
   signal s_time_counter          : natural range 0 to maximal_time_counter; -- Internal time counter
begin

   ------------------------------------------------------------
   -- Condition evaluation process
   -- This combinational process evalutes if all conditions are true
   -- (logic and between all conditions).
   condition_evaluation : process(input_conditions)
      variable v_internal_condition : std_logic; -- Logical combination of conditions
   begin
      v_internal_condition := '1'; -- Initial value
      
      for i in 0 to conditions_number - 1 loop
         v_internal_condition := v_internal_condition and input_conditions(i);
      end loop;
      
      s_condition_combination <= v_internal_condition; -- Assignment of the result
   end process condition_evaluation;

   ------------------------------------------------------------
   -- Enable evaluation process
   -- This combinational process evalutes if the transtion is enabled
   -- (logic and between all input arcs status).
   enable_evaluation : process(input_arcs_valid)
      variable v_internal_enabled : std_logic; -- Logical combination of the input arcs
   begin
      v_internal_enabled := '1'; -- Initial value
      
      for i in 0 to input_arcs_number - 1 loop
         v_internal_enabled := v_internal_enabled and input_arcs_valid(i);
      end loop;
      
      s_enabled <= v_internal_enabled; -- Assignment of the result
   end process enable_evaluation;

   ------------------------------------------------------------
   -- Reinit time counter evaluation process
   -- This combinational process evaluates if the time counter has
   -- to be reinitialised (logic or between all time counter clear requests).
   reinit_time_counter_evaluation : process(reinit_time, s_enabled)
      variable v_internal_reinit_time_counter : std_logic; -- Logical combination of time counter clear requests
   begin
      v_internal_reinit_time_counter := '0'; -- Initial value
      
      for i in 0 to input_arcs_number - 1 loop
         if (s_enabled = '1') then
            v_internal_reinit_time_counter := v_internal_reinit_time_counter or reinit_time(i);
         end if;
      end loop;
      
      s_reinit_time_counter <= v_internal_reinit_time_counter; -- Assignment of the result
   end process reinit_time_counter_evaluation;

   ------------------------------------------------------------
   -- Time counter process
   -- This sequential process updates the time counter according to the status
   -- of the transition.
   time_counter : process(reset_n, clock, mp_asynchronous_clear)
   begin
      if ( (reset_n = '0') or (mp_asynchronous_clear = '1') ) then
         s_time_counter <= 0;
      elsif falling_edge(clock) then
         if ( (s_enabled = '1') and (transition_type /= transition_type_t(TRANSITION_NOT_TEMPORAL)) ) then
            if ( (s_reinit_time_counter = '0') and (s_fired = '0') ) then
               if (s_time_counter < maximal_time_counter) then
                  s_time_counter <= s_time_counter + 1;
               end if;
            else
               s_time_counter <= 1;
            end if;
         else
            s_time_counter <= 0;
         end if;
      end if;
   end process time_counter;

   time_cleared <= '0' when (s_time_counter = 0) else '1';  -- Updates the status according to the time counter

   ------------------------------------------------------------
   
   -- This condition evaluates if the firing condition is true or false.
   s_firing_condition <= '1' when
      ( ( (transition_type = transition_type_t(TRANSITION_NOT_TEMPORAL)) and (s_enabled = '1') and (s_condition_combination = '1') )

      or ( (transition_type = transition_type_t(TRANSITION_TEMPORAL_A_B)) and (s_reinit_time_counter = '0')
         and (s_enabled = '1') and (s_condition_combination = '1') and (s_time_counter >= (time_A_value-1)) and (s_time_counter < time_B_value)
         and (time_A_value /= 0) and (time_B_value /= 0) )

      or ( (transition_type = transition_type_t(TRANSITION_TEMPORAL_A_A)) and (s_reinit_time_counter = '0')
         and (s_enabled = '1') and (s_condition_combination = '1') and (s_time_counter = (time_A_value-1)) and (time_A_value /= 0) )

      or ( (transition_type = transition_type_t(TRANSITION_TEMPORAL_A_INFINITE)) and (s_reinit_time_counter = '0')
         and (s_enabled = '1') and (s_condition_combination = '1') and (s_time_counter >= (time_A_value-1)) and (time_A_value /= 0) )

      or ( (transition_type /= transition_type_t(TRANSITION_NOT_TEMPORAL)) and (s_reinit_time_counter = '1')
         and (s_enabled = '1') and (s_condition_combination = '1') and (time_A_value = 1) ) )
   else '0';

   ------------------------------------------------------------
   -- Firable process
   -- This sequential process evaluates if the transition is firable.
   firable : process(reset_n, clock, mp_asynchronous_clear)
   begin
      if ( (reset_n = '0') or (mp_asynchronous_clear = '1') ) then
         s_firable <= '0';
      elsif falling_edge(clock) then
         s_firable <= s_firing_condition;
      end if;
   end process firable;

   -- Updates the status according to the priority authorization
   s_fired <= s_firable and priority_authorization;
   fired <= s_fired;

   ------------------------------------------------------------
   -- Exception firable process
   -- This sequential process evaluates if the exception transition is firable.
   exception_firable : process(reset_n, clock, exception_asynchronous_clear)
   begin
      if ( (reset_n = '0') or (exception_asynchronous_clear = '1') ) then
         s_exception_firable <= '0';
      elsif falling_edge(clock) then
         s_exception_firable <= s_firing_condition;
      end if;
   end process exception_firable;

   exception_fired <= s_exception_firable and priority_authorization; -- Updates the status according to the priority authorization

end transition_architecture;
