package template.file

import inria.hilecop.software.Activator
import java.io.ByteArrayInputStream
import java.io.File
import java.io.IOException
import java.text.SimpleDateFormat
import org.eclipse.core.resources.IProject
import org.eclipse.core.resources.IResource
import org.eclipse.core.resources.ResourcesPlugin
import org.eclipse.core.runtime.FileLocator
import org.eclipse.core.runtime.Path
import org.eclipse.core.runtime.Platform
import others.Messages
import template.interfaceTemplate.IVHDLTemplateFiles

class VHDL_place_pivot_v2_template_files implements IVHDLTemplateFiles {
	IProject currentProject;
	int maxMarkup;
	int maxPriority;
	String configurationName;
	Boolean isDefault;
	String location;
	
	override generateVHDLFiles(String projectName,String configurationName, int maxMarkup, int maxPriority,Boolean isDefault,String location) {
		println("Generate All Files")
		val r = ResourcesPlugin.getWorkspace().getRoot();
		currentProject = r.getProject(projectName);
		this.maxMarkup = maxMarkup
		this.maxPriority = maxPriority
		this.configurationName = configurationName;
		this.isDefault = isDefault;
		this.location = location;
		
		//generateAllFile();
		
		generateFilePetri("petri.vhd")
		generateFilePlace("place.vhd")
		generateFileTransition("transition.vhd")
		generateFileExceptionUnit("exception_unit.vhd")
		generateFileMacroplace("macroplace.vhd")
		
	}
	
	@Deprecated
	def generateAllFile() {
		var bundle = Platform.getBundle(Activator.getDefault().PLUGIN_ID_NON_STATIC)
		var resource_url = bundle.getResource("vhd/"+configurationName+"/petri.vhd");
		try {
			var clean_url = FileLocator.resolve(resource_url);
			var pathname = clean_url.toString();
			var file = new File(pathname.replace("file:/", ""));
			if(file.exists()) {
				val file_new = currentProject.getFile("hilecop-gen/"+configurationName+"/"+file.name);
				file_new.create(null,false,null)
//				file.setContents(file., false, false, null);
			}
		} catch (IOException e) {
			System.err.println("Erreur lors du chargement du ficher html splashscreen");
			e.printStackTrace();
		}
	}
	
	def generateFilePetri(String filename) {
		
		
		var file = currentProject.getFile("hilecop-gen/"+configurationName+"/"+filename);
		if(!isDefault) {
			var fic = new File(location+"/"+filename)
			fic.createNewFile
			var location= Path.fromOSString(fic.getAbsolutePath())
			file = currentProject.getFile("hilecop-gen/"+configurationName+"/"+location.lastSegment());
			file.createLink(location, IResource.NONE, null);
		}
		else if(!file.exists){
			file.create(null,false,null)
		}
		
		var content = '''
--------------------------------------------------------------------
-- COPYRIGHT (c) ABC, 2017
-- The copyright to the document herein is the property of ABC.
--
-- All rights reserved.
--------------------------------------------------------------------
--
-- Author: Guillaume Souquet, Ronald Reboul, Arthur Hiairrassary
-- Created: «new SimpleDateFormat("dd-MM-yyyy HH:mm").format(System.currentTimeMillis)»
--
--------------------------------------------------------------------
-- Description:
--
-- This package defines the global constants and types used
-- by the HILECOP methodology.
-- TODO
-- TODO File name: «filename»
-- TODO HILECOP version: «Messages.VersionForTemplate»
-- TODO Traduction version: Place-Pivot «version()»
-- TODO Maximal global marking: «maxMarkup»
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

   constant MAXIMAL_GLOBAL_MARKING : natural := «maxMarkup»; -- Maximal marking of every place and arc in the design
   subtype weight_t is natural range 0 to MAXIMAL_GLOBAL_MARKING; -- Type defining the marking of a place or the weight of an arc
   type weight_vector_t is array (natural range <>) of weight_t; -- Type defining a vector of weight_t

   type arc_type_t is (ARC_BASIC_PT, ARC_TEST, ARC_INHIBITOR); -- Type defining the type of an arc
   type arc_type_vector_t is array (natural range <>) of arc_type_t; -- Type defining a vector of arc_type_t

   type transition_type_t is (TRANSITION_NOT_TEMPORAL, TRANSITION_TEMPORAL_A_B, TRANSITION_TEMPORAL_A_A, TRANSITION_TEMPORAL_A_INFINITE); -- Type defining the type of a transition

end petri;
'''

		val is = new ByteArrayInputStream(content.getBytes());
		if(file.exists()) {
			file.setContents(is, false, false, null);
		}
		else {
			file.create(is, true, null);
		}
	}
	
	def generateFilePlace(String filename) {
		var file = currentProject.getFile("hilecop-gen/"+configurationName+"/"+filename);
			if(!isDefault) {
			var fic = new File(location+"/"+filename)
			fic.createNewFile
			var location= Path.fromOSString(fic.getAbsolutePath())
			file = currentProject.getFile("hilecop-gen/"+configurationName+"/"+location.lastSegment());
			file.createLink(location, IResource.NONE, null);
		}
		else if(!file.exists){
			file.create(null,false,null)
		}
		
		var content = '''
--------------------------------------------------------------------
-- COPYRIGHT (c) ABC, 2017
-- The copyright to the document herein is the property of ABC.
--
-- All rights reserved.
--------------------------------------------------------------------
--
-- Author: Guillaume Souquet, Ronald Reboul, Arthur Hiairrassary
-- Created: «new SimpleDateFormat("dd-MM-yyyy HH:mm").format(System.currentTimeMillis)»
--
--------------------------------------------------------------------
-- Description:
--
-- This entity describes the behavior of the petri net place
-- component in the HILECOP methodology.
-- TODO
-- TODO File name: «filename»
-- TODO HILECOP version: «Messages.VersionForTemplate»
-- TODO Traduction version: Place-Pivot «version()»
-- TODO Maximal global marking: «maxMarkup»
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
      priority_authorizations  : out std_logic_vector(output_arcs_number-1 downto 0); -- Indicates if each output transition has the authorization to be fired
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
      variable v_temporal_output_token_sum : weight_t; -- Temporal result of the sum of output tokens
      variable v_real_output_token_sum     : weight_t; -- Real result of the sum of output tokens
   begin
      -- Initial values
      v_temporal_output_token_sum := 0;
      v_real_output_token_sum := 0;

      for i in 0 to output_arcs_number - 1 loop
         v_temporal_output_token_sum := v_real_output_token_sum + output_arcs_weights(i);

         if ((output_transitions_fired(i) = '1') and (output_arcs_types(i) = ARC_BASIC_PT)) then
            v_real_output_token_sum := v_real_output_token_sum + output_arcs_weights(i);
         end if;

         -- Assignment of the result
         if (s_marking >= v_temporal_output_token_sum) then
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
'''

		val is = new ByteArrayInputStream(content.getBytes());
		if(file.exists()) {
			file.setContents(is, false, false, null);
		}
		else {
			file.create(is, true, null);
		}
	}
	
	def generateFileTransition(String filename) {
		var file = currentProject.getFile("hilecop-gen/"+configurationName+"/"+filename);
			if(!isDefault) {
			var fic = new File(location+"/"+filename)
			fic.createNewFile
			var location= Path.fromOSString(fic.getAbsolutePath())
			file = currentProject.getFile("hilecop-gen/"+configurationName+"/"+location.lastSegment());
			file.createLink(location, IResource.NONE, null);
		}
		else if(!file.exists){
		file.create(null,false,null)
		}
		
		var content = '''
--------------------------------------------------------------------
-- COPYRIGHT (c) ABC, 2017
-- The copyright to the document herein is the property of ABC.
--
-- All rights reserved.
--------------------------------------------------------------------
--
-- Author: Guillaume Souquet, Ronald Reboul, Arthur Hiairrassary
-- Created: «new SimpleDateFormat("dd-MM-yyyy HH:mm").format(System.currentTimeMillis)»
--
--------------------------------------------------------------------
-- Description:
--
-- This entity describes the behavior of the petri net transition
-- component in the HILECOP methodology.
-- TODO
-- TODO File name: «filename»
-- TODO HILECOP version: «Messages.VersionForTemplate»
-- TODO Traduction version: Place-Pivot «version()»
-- TODO Maximal global marking: «maxMarkup»
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
'''

		val is = new ByteArrayInputStream(content.getBytes());
		if(file.exists()) {
			file.setContents(is, false, false, null);
		}
		else {
			file.create(is, true, null);
		}
	}
	
	def generateFileExceptionUnit(String filename) {
			var file = currentProject.getFile("hilecop-gen/"+configurationName+"/"+filename);
			if(!isDefault) {
				var fic = new File(location+"/"+filename)
				fic.createNewFile
				var location= Path.fromOSString(fic.getAbsolutePath())
				file = currentProject.getFile("hilecop-gen/"+configurationName+"/"+location.lastSegment());
				file.createLink(location, IResource.NONE, null);
			}
		else if(!file.exists){
		file.create(null,false,null)
		}
		
		var content = '''
--------------------------------------------------------------------
-- COPYRIGHT (c) ABC, 2017
-- The copyright to the document herein is the property of ABC.
--
-- All rights reserved.
--------------------------------------------------------------------
--
-- Author: Guillaume Souquet, Ronald Reboul, Arthur Hiairrassary
-- Created: «new SimpleDateFormat("dd-MM-yyyy HH:mm").format(System.currentTimeMillis)»
--
--------------------------------------------------------------------
-- Description:
--
-- This entity describes the behavior of the exception unit used by
-- the HILECOP methodology.
-- TODO
-- TODO File name: «filename»
-- TODO HILECOP version: «Messages.VersionForTemplate»
-- TODO Traduction version: Place-Pivot «version()»
-- TODO Maximal global marking: «maxMarkup»
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
'''

		val is = new ByteArrayInputStream(content.getBytes());
		if(file.exists()) {
			file.setContents(is, false, false, null);
		}
		else {
			file.create(is, true, null);
		}
	}

	def generateFileMacroplace(String filename) {
		var file = currentProject.getFile("hilecop-gen/"+configurationName+"/"+filename);
			if(!isDefault) {
			var fic = new File(location+"/"+filename)
			fic.createNewFile
			var location= Path.fromOSString(fic.getAbsolutePath())
			file = currentProject.getFile("hilecop-gen/"+configurationName+"/"+location.lastSegment());
			file.createLink(location, IResource.NONE, null);
		}
		else if(!file.exists){
		file.create(null,false,null)
		}
		
		var content = '''
--------------------------------------------------------------------
-- COPYRIGHT (c) ABC, 2017
-- The copyright to the document herein is the property of ABC.
--
-- All rights reserved.
--------------------------------------------------------------------
--
-- Author: Guillaume Souquet, Ronald Reboul, Arthur Hiairrassary
-- Created: «new SimpleDateFormat("dd-MM-yyyy HH:mm").format(System.currentTimeMillis)»
--
--------------------------------------------------------------------
-- Description:
--
-- This entity describes the behavior of the macroplace used by
-- the HILECOP methodology.
-- TODO
-- TODO File name: «filename»
-- TODO HILECOP version: «Messages.VersionForTemplate»
-- TODO Traduction version: Place-Pivot «version()»
-- TODO Maximal global marking: «maxMarkup»
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
'''
		
		val is = new ByteArrayInputStream(content.getBytes());
		if(file.exists()) {
			file.setContents(is, false, false, null);
		}
		else {
			file.create(is, true, null);
		}
	}
	
	
	
	def version() {
		return "1.0.0"
	}
	
	
}