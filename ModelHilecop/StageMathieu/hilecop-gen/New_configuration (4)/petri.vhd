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
-- This package defines the global constants and types used
-- by the HILECOP methodology.
-- TODO
-- TODO File name: petri.vhd
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


----------------------------------------
-- petri package declaration
----------------------------------------
package petri is

   constant MAXIMAL_GLOBAL_MARKING : natural := 255; -- Maximal marking of every place and arc in the design
   subtype weight_t is natural range 0 to MAXIMAL_GLOBAL_MARKING; -- Type defining the marking of a place or the weight of an arc
   type weight_vector_t is array (natural range <>) of weight_t; -- Type defining a vector of weight_t

   type arc_type_t is (ARC_BASIC_PT, ARC_TEST, ARC_INHIBITOR); -- Type defining the type of an arc
   type arc_type_vector_t is array (natural range <>) of arc_type_t; -- Type defining a vector of arc_type_t

   type transition_type_t is (TRANSITION_NOT_TEMPORAL, TRANSITION_TEMPORAL_A_B, TRANSITION_TEMPORAL_A_A, TRANSITION_TEMPORAL_A_INFINITE); -- Type defining the type of a transition

end petri;
