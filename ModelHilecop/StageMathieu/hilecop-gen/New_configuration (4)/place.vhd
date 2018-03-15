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
-- This entity describes the behavior of the petri net place
-- component in the HILECOP methodology.
-- TODO
-- TODO File name: place.vhd
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
-- place entity declaration
----------------------------------------
entity place is
   generic(
      input_arcs_number  : natural := 1; -- Number of input arcs
      output_arcs_number : natural := 1 -- Number of output arcs
   );
   port(
      clock                    : in std_logic; -- Entity clock
      reset_n                  : in std_logic; -- Active low asynchronous reset
      initial_marking          : in weight_t; -- Initial internal marking
      input_arcs_weights       : in weight_vector_t(input_arcs_number-1 downto 0); -- Weight of every input arc
      output_arcs_types        : in arc_type_vector_t(output_arcs_number-1 downto 0); -- Type of every output arc
      output_arcs_weights      : in weight_vector_t(output_arcs_number-1 downto 0); -- Weight of every output arc
      input_transitions_fired  : in std_logic_vector(input_arcs_number-1 downto 0); -- Indicates if each input transition is fired or not
      output_transitions_fired : in std_logic_vector(output_arcs_number-1 downto 0); -- Indicates if each output transition is fired or not
      mp_asynchronous_clear    : in std_logic; -- Macroplace active high asynchronous reset
      output_arcs_valid        : out std_logic_vector(output_arcs_number-1 downto 0); -- Indicates if the marking is valid for each output arc
      priority_authorizations  : out std_logic_vector(output_arcs_number-1 downto 0);
      reinit_transitions_time  : out std_logic_vector (output_arcs_number-1 downto 0); -- Indicates for each output transition if the time counter needs to be reinitialised
      marked                   : out std_logic -- Indicates if the place is marked or not
   );
end place;


----------------------------------------
-- place architecture
----------------------------------------
architecture place_architecture of place is

   -- Signal declarations
   signal s_input_token_sum  : weight_t; -- Sum of tokens that will be added to the place when the input transitions will be fired
   signal s_marking          : weight_t; -- Internal marking
   signal s_output_token_sum : weight_t; -- Sum of tokens that will be removed to the place when the output transitions will be fired
begin

   ------------------------------------------------------------
   -- Input tokens sum process
   -- This combinational process computes the sum of the tokens that will
   -- be added to the place when all the input transitions are fired.
   input_tokens_sum : process(input_arcs_weights, input_transitions_fired)
      variable v_internal_input_token_sum : weight_t; -- Result of the sum of input tokens
   begin
      v_internal_input_token_sum := 0; -- Initial value
      
      for i in 0 to input_arcs_number - 1 loop
         if (input_transitions_fired(i) = '1') then
            v_internal_input_token_sum := v_internal_input_token_sum + input_arcs_weights(i); -- Add tokens from each fired input transition
         end if;
      end loop;
      
      s_input_token_sum <= v_internal_input_token_sum; -- Assignment of the result
   end process input_tokens_sum;

   ------------------------------------------------------------
   -- Output tokens sum process
   -- This combinational process computes the sum of the tokens that will
   -- be removed from the place when all the input transitions are fired.
   output_tokens_sum : process(output_arcs_types, output_arcs_weights, output_transitions_fired)
      variable v_internal_output_token_sum : weight_t; -- Result of the sum of output tokens
   begin
      v_internal_output_token_sum := 0; -- Initial value
      
      for i in 0 to output_arcs_number - 1 loop
         if (output_transitions_fired(i) = '1' and output_arcs_types(i) = arc_type_t(ARC_BASIC_PT)) then
            v_internal_output_token_sum := v_internal_output_token_sum + output_arcs_weights(i); -- Add tokens from each fired output transition
         end if;
      end loop;
      
      s_output_token_sum <= v_internal_output_token_sum; -- Assignment of the result
   end process output_tokens_sum;

   ------------------------------------------------------------
   -- Marking process
   -- This sequential process updates the internal marking according to the fired
   -- input and output transitions.
   marking : process(clock, reset_n, initial_marking, mp_asynchronous_clear)
   begin
      if (reset_n = '0') then -- Marking initialisation
         s_marking <= initial_marking;
      elsif (mp_asynchronous_clear = '1') then -- Exception transition of a macroplace
         s_marking <= 0;
      elsif rising_edge(clock) then
         -- The new marking is computed from previous marking and the number of tokens
         -- added and removed by the input and output transitions
         s_marking <= s_marking + (s_input_token_sum - s_output_token_sum);
      end if;
   end process marking;

   marked <= '0' when (s_marking = 0) else '1'; -- Updates the status according to the internal marking

   ------------------------------------------------------------
   -- Marking validation evaluation process
   -- This combinational process evalutes for each output arc (between the place and
   -- the associated transition) if the current marking of the place satisfies the arc
   -- properties (arc type and weight). When the properties are satisfied, the arc
   -- is said valid.
   marking_validation_evaluation : process(output_arcs_types, output_arcs_weights, s_marking)
   begin
      for i in 0 to output_arcs_number - 1 loop
         if ( ( ((output_arcs_types(i) = arc_type_t(ARC_BASIC_PT)) or (output_arcs_types(i) = arc_type_t(ARC_TEST))) and (s_marking >= output_arcs_weights(i)) )
            or ( (output_arcs_types(i) = arc_type_t(ARC_INHIBITOR)) and (s_marking < output_arcs_weights(i)) ) )
         then
            output_arcs_valid(i) <= '1';
         else
            output_arcs_valid(i) <= '0';
         end if;
      end loop;
   end process marking_validation_evaluation;

   ------------------------------------------------------------
   -- Priority evaluation process
   -- This combinational process evalutes the authorization to be fired for each
   -- transition in conflict included in a same group of transitions. This
   -- evaluation must be done in less than half a clock period to be ready before
   -- the next clock edge.
   priority_evaluation : process(output_arcs_types, output_arcs_weights, output_transitions_fired, s_marking)
      variable v_sum : weight_t; -- TODO Changer nom variable !!!
      variable v_sum_tmp : weight_t; -- TODO Changer nom variable !!!
   begin
      v_sum := 0;
      v_sum_tmp := 0;

      for i in 0 to output_arcs_number - 1 loop
         v_sum := v_sum_tmp + output_arcs_weights(i);

         if ((output_transitions_fired(i) = '1') and (output_arcs_types(i) = ARC_BASIC_PT)) then
            v_sum_tmp := v_sum_tmp + output_arcs_weights(i);
         end if;

         if (s_marking >= v_sum) then
            if ((output_arcs_types(i) = ARC_BASIC_PT) or (output_arcs_types(i) = ARC_TEST)) then
               priority_authorizations(i) <= '1';
            else
               priority_authorizations(i) <= '0';
            end if;
         else
            if ((output_arcs_types(i) = ARC_BASIC_PT) or (output_arcs_types(i) = ARC_TEST)) then
               priority_authorizations(i) <= '0';
            else
               priority_authorizations(i) <= '1';
            end if;
         end if;
      end loop;
   end process priority_evaluation;

   ------------------------------------------------------------
   -- Reinit transitions time evaluation process
   -- This sequential process evalutes if the time counters of output transitions have
   -- to be reinitialised. This occurs when an output temporal transition is enabled (and
   -- its time counter starts counting) but is later disabled, even for less than a clock cycle.
   -- In this case the time counter must be reset to its initial value.
   reinit_transitions_time_evaluation : process(clock, reset_n, mp_asynchronous_clear)
   begin
      if (reset_n = '0') then -- Marking initialisation
         reinit_transitions_time <= (others => '0');
      elsif (mp_asynchronous_clear = '1') then -- Exception transition of a macroplace
         reinit_transitions_time <= (others => '0');
      elsif rising_edge(clock) then
         for i in 0 to output_arcs_number - 1 loop
            if ( ((output_arcs_types(i) = arc_type_t(ARC_BASIC_PT)) or (output_arcs_types(i) = arc_type_t(ARC_TEST)))
               and (s_marking - s_output_token_sum < output_arcs_weights(i))
               and (s_output_token_sum > 0) )
            then
               reinit_transitions_time(i) <= '1';
            else
               reinit_transitions_time(i) <= '0';
            end if;
         end loop;
      end if;
   end process reinit_transitions_time_evaluation;

end place_architecture;
