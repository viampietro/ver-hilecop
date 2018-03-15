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
-- This entity describes the behavior of the macroplace used by
-- the HILECOP methodology.
-- TODO
-- TODO File name: macroplace.vhd
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
-- macroplace entity declaration
----------------------------------------
entity macroplace is
   generic(
      internal_places_number : natural := 1; -- Number of places in the macroplace
      exception_arcs_number  : natural := 1 -- Number of exception arcs from the macroplace
   );
   port(
      internal_places_marked           : in std_logic_vector(internal_places_number-1 downto 0); -- Indicates if the places in the macroplace are marked or not
      reinit_exception_transition_time : out std_logic_vector (exception_arcs_number-1 downto 0); -- Indicates if exception transitions need to be cleared
      macroplace_enabled               : out std_logic -- Indicates if the macroplace is enabled or not
   );
end macroplace;


----------------------------------------
-- macroplace architecture
----------------------------------------
architecture macroplace_architecture of macroplace is

   -- Signal declarations
   signal s_enabled : std_logic; -- Indicates if the macroplace is enabled or not
begin

   ------------------------------------------------------------
   -- Place marked evaluation process
   -- This combinational process evalutes if at least one place is marked
   -- (logic or between all places in the macroplace).
   place_marked_evaluation : process(internal_places_marked)
      variable v_internal_one_place_marked : std_logic; -- Logical combination of all places marked
   begin
      v_internal_one_place_marked := '0'; -- Initial value
      
      for i in 0 to internal_places_number - 1 loop
         v_internal_one_place_marked := v_internal_one_place_marked or internal_places_marked(i);
      end loop;
      
      s_enabled <= v_internal_one_place_marked; -- Assignment of the result
   end process place_marked_evaluation;
   
   macroplace_enabled <= s_enabled; -- Updates the status

   ------------------------------------------------------------
   -- Reinit exception transition time evaluation process
   -- This combinational process evaluates if exception transitions need
   -- to be cleared.
   reinit_exception_transition_time_evaluation : process(s_enabled)
   begin
      for i in 0 to exception_arcs_number - 1 loop
         if (s_enabled = '0') then
            reinit_exception_transition_time(i) <= '1';
         else
            reinit_exception_transition_time(i) <= '0';
         end if;
      end loop;
   end process reinit_exception_transition_time_evaluation;

end macroplace_architecture;
