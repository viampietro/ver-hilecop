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

class VHDL_transition_pivot_v2_template_files implements IVHDLTemplateFiles {
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
		generateFilePriorityUnit("priority_unit.vhd")
		generateFileExceptionUnit("exception_unit.vhd")
		generateFileMacroplace("macroplace.vhd")
		
	}
	
	
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
--------------------------------------------------------------------------------
-- HILECOP GENERATED FILE 
-- 	HILECOP version 	: «Messages.VersionForTemplate»
-- 	Date 				: «new SimpleDateFormat("yyyy/MM/dd HH:mm").format(System.currentTimeMillis)»

-- COMPONENT
--	Name 				: Petri.vhd

-- TRADUCTION
--	Traduction version 	: Transition-Pivot «version()»
--	Global Max markup 	: «maxMarkup»
--------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;


package petri is


	constant MAXIMAL_GLOBAL_MARKING : natural := «maxMarkup»;

	subtype weight is natural range 0 to MAXIMAL_GLOBAL_MARKING;  

	type weight_vector is array (natural range <>) of weight;  

	type arc_type is (ARC_BASIC_PT, ARC_TEST, ARC_INHIBITOR, ARC_BASIC_TP); 

	type arc_type_vector is array (natural range <>) of arc_type;     

	type transition_type is (TRANSITION_NO_TEMPORAL, TRANSITION_TEMPORAL_A_B, TRANSITION_TEMPORAL_A_A, TRANSITION_TEMPORAL_A_INFINITE); 
    
	-- Priority unit
	constant MAXIMAL_PRIORITY : integer := 15;
    
	type priority_vector is array (natural range <>) of natural range 0 to MAXIMAL_PRIORITY;
    
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
--------------------------------------------------------------------------------
-- HILECOP GENERATED FILE 
-- 	HILECOP version 	: «Messages.VersionForTemplate»
-- 	Date 				: «new SimpleDateFormat("yyyy/MM/dd HH:mm").format(System.currentTimeMillis)»

-- COMPONENT
--	Name 				: Place.vhd

-- TRADUCTION
--	Traduction version 	: Transition-Pivot «version()»
--------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.petri.all;


entity place is
generic(
		input_arc_number	: natural := 1;
		output_arc_number	: natural := 1;
		maximal_marking		: natural := MAXIMAL_GLOBAL_MARKING);
port(
		clock				: in std_logic;
		reset_n				: in std_logic;
		initial_marking		: in weight;
		input_token			: in weight_vector(input_arc_number-1 downto 0);
		output_token		: in weight_vector(output_arc_number-1 downto 0);
		asynchronous_clear	: in std_logic;
		active_place		: out std_logic;
		smaller_transitory_marking	: out weight;
		current_marking		: out weight);
end;


architecture place_architecture of place is

signal internal_marking		: weight;
signal input_token_sum		: weight;
signal output_token_sum		: weight;

begin

	------------------------------------------------
	InputTokenSumProcess : process(input_token)
	variable internal_input_token_sum : weight;
	begin
		internal_input_token_sum := 0;
		for i in 0 to input_arc_number-1 loop			-- Sum of input tokens
			internal_input_token_sum := internal_input_token_sum + input_token(i);
		end loop;
		input_token_sum <= internal_input_token_sum;
	end process InputTokenSumProcess;
	
	------------------------------------------------
	OutputTokenSumProcess : process(output_token)
	variable internal_output_token_sum : weight;
	begin
		internal_output_token_sum := 0;
		for j in 0 to output_arc_number-1 loop			-- Sum of output tokens
			internal_output_token_sum := internal_output_token_sum + output_token(j);
		end loop;
		output_token_sum <= internal_output_token_sum;
	end process OutputTokenSumProcess;

	------------------------------------------------
	MarkingProcess : process(clock, reset_n, asynchronous_clear, input_token_sum, output_token_sum, initial_marking)
	begin
		if ( reset_n = '0' ) then
			internal_marking <= initial_marking;		-- marking initialisation
		elsif ( asynchronous_clear = '1' ) then			-- exception transition of a macro place
			internal_marking <= 0;
		elsif rising_edge(clock) then
			internal_marking <= internal_marking + (input_token_sum - output_token_sum);
		end if;
	end process MarkingProcess;
	
	current_marking <= internal_marking;				-- external copy of the internal signal

	active_place <= '0' when (internal_marking = 0) else '1';

	------------------------------------------------
	MinTransitoryMarkingProcess : process(clock, reset_n, asynchronous_clear, input_token_sum, output_token_sum, initial_marking)
	begin
		if ( reset_n = '0' ) then
			smaller_transitory_marking <= initial_marking;
		elsif ( asynchronous_clear = '1' ) then			-- exception transition of a macro place
			smaller_transitory_marking <= 0;
		elsif rising_edge(clock) then
			if (output_token_sum /= 0) then
				smaller_transitory_marking <= internal_marking - output_token_sum;
			else
				smaller_transitory_marking <= internal_marking + (input_token_sum - output_token_sum);
			end if;
		end if;
	end process MinTransitoryMarkingProcess;

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
--------------------------------------------------------------------------------
-- HILECOP GENERATED FILE 
-- 	HILECOP version 	: «Messages.VersionForTemplate»
-- 	Date 				: «new SimpleDateFormat("yyyy/MM/dd HH:mm").format(System.currentTimeMillis)»

-- COMPONENT
--	Name 				: Transition.vhd

-- TRADUCTION
--	Traduction version 	: Transition-Pivot «version()»
--------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.petri.all;


entity transition is
generic(
		input_arc_number	: natural := 1;
		output_arc_number	: natural := 1;
		condition_number	: natural := 1;
		transition_type		: transition_type := TRANSITION_NO_TEMPORAL;
		max_time_counter	: natural := 255);
port(
		clock						: in std_logic;
		reset_n						: in std_logic;
		input_condition				: in std_logic_vector(condition_number-1 downto 0);
		time_A_value				: in natural range 0 to max_time_counter;
		time_B_value				: in natural range 0 to max_time_counter;
		input_arc_type				: in arc_type_vector(input_arc_number-1 downto 0);
		input_arc_weight			: in weight_vector(input_arc_number-1 downto 0);
		output_arc_weight			: in weight_vector(output_arc_number-1 downto 0);
		input_place_marking			: in weight_vector(input_arc_number-1 downto 0);
		input_smaller_transitory_marking	: in weight_vector(input_arc_number-1 downto 0);
		priority_unit_authorization	: in std_logic;
		asynchronous_clear			: in std_logic;
		timer_clear_ack				: out std_logic;
		active_transition			: out std_logic;
		remove_input_token			: out weight_vector(input_arc_number-1 downto 0);
		add_output_token			: out weight_vector(output_arc_number-1 downto 0);
		exception_transition_asynchronous_clear_MP	: in std_logic;
		exception_transition_active_exception_unit	: out std_logic);
end;


architecture transition_architecture of transition is

signal condition_combination		: std_logic;
signal sensitive_transition			: std_logic;
signal time_counter					: natural range 0 to max_time_counter;
signal internal_remove_input_token	: weight_vector(input_arc_number-1 downto 0);
signal internal_add_output_token	: weight_vector(output_arc_number-1 downto 0);
signal internal_active_transition 	: std_logic;
signal internal_exception_transition_active_exception_unit	: std_logic;
signal synchronous_timer_clear		: std_logic;
signal s_active_transition			: std_logic;

begin

	------------------------------------------------
	-- Condition Evaluation
	ConditionProcess : process(input_condition)
	variable internal_condition : std_logic;
	begin
		internal_condition := '1';
		for g in 0 to condition_number-1 loop
			internal_condition := internal_condition and input_condition(g);
		end loop;
		condition_combination <= internal_condition;
	end process ConditionProcess;

	------------------------------------------------
	-- Sensitisation Evaluation
	SensitiveProcess : process(input_place_marking, input_arc_type, input_arc_weight)
	variable internal_sensitive : std_logic;
	begin
		internal_sensitive := '1';
		for k in 0 to input_arc_number-1 loop
			if ( (input_arc_type(k) = ARC_BASIC_PT) or (input_arc_type(k) = ARC_TEST) ) then
				if (input_place_marking(k) < input_arc_weight(k)) then internal_sensitive := '0';
				end if;
			else
				if (input_arc_type(k) = ARC_INHIBITOR) then
					if (input_place_marking(k) >= input_arc_weight(k)) then internal_sensitive := '0';
					end if;
				end if;
			end if;
		end loop;
		sensitive_transition <= internal_sensitive;
	end process SensitiveProcess;

	------------------------------------------------
	-- Synchronous reset of others temporal transitons
	SyncResetProcess : process(input_smaller_transitory_marking, input_arc_type, input_arc_weight, sensitive_transition)
	variable internal_synchronous_timer_clear : std_logic;
	begin
		internal_synchronous_timer_clear := '0';
		for k in 0 to input_arc_number-1 loop
			if ( (input_arc_type(k) = ARC_BASIC_PT) or (input_arc_type(k) = ARC_TEST) ) then
				if ( (input_smaller_transitory_marking(k) < input_arc_weight(k)) and (sensitive_transition = '1') ) then
					internal_synchronous_timer_clear := '1';
				end if;
			end if;
		end loop;
		synchronous_timer_clear <= internal_synchronous_timer_clear;
	end process SyncResetProcess;

	------------------------------------------------
	CounterProcess : process(reset_n, clock, sensitive_transition, asynchronous_clear)
	begin
		if ( (reset_n = '0') or (asynchronous_clear = '1') ) then
			time_counter <= 0;
		elsif falling_edge(clock) then
			if ( (sensitive_transition = '1') and (transition_type /= TRANSITION_NO_TEMPORAL) ) then
				if (synchronous_timer_clear = '0') and (s_active_transition = '0') then
					if (time_counter < max_time_counter) then
						time_counter <= time_counter + 1;
					end if;
				else
					time_counter <= 1;
				end if;
			else
				time_counter <= 0;
			end if;
		end if;
	end process CounterProcess;
	
	timer_clear_ack <= '0' when (time_counter = 0) else '1';
	
	------------------------------------------------
	-- Add / Remove tokens
	TokenProcess : process(reset_n, clock, sensitive_transition, condition_combination, time_counter, time_A_value, time_B_value, input_arc_type, input_arc_weight, asynchronous_clear)
	begin
		if ( (reset_n = '0') or (asynchronous_clear = '1') ) then
			for i in 0 to input_arc_number-1 loop
				internal_remove_input_token(i) <= 0;
			end loop;
			for j in 0 to output_arc_number-1 loop
				internal_add_output_token(j) <= 0;
			end loop;
			internal_active_transition <= '0';
			
		elsif falling_edge(clock) then

			if ( ( (transition_type = TRANSITION_NO_TEMPORAL) and (sensitive_transition = '1') and (condition_combination = '1') )

				or ( (transition_type = TRANSITION_TEMPORAL_A_B) and (synchronous_timer_clear = '0') and
					(sensitive_transition = '1') and (condition_combination = '1') and (time_counter >= (time_A_value-1)) and (time_counter < time_B_value)
					and (time_A_value /= 0) and (time_B_value /= 0) )

				or ( (transition_type = TRANSITION_TEMPORAL_A_A) and (synchronous_timer_clear = '0') and
					(sensitive_transition = '1') and (condition_combination = '1') and (time_counter = (time_A_value-1)) and (time_A_value /= 0) )

				or ( (transition_type = TRANSITION_TEMPORAL_A_INFINITE) and (synchronous_timer_clear = '0') and
					(sensitive_transition = '1') and (condition_combination = '1') and (time_counter >= (time_A_value-1)) and (time_A_value /= 0) )

				or ( (transition_type /= TRANSITION_NO_TEMPORAL) and (synchronous_timer_clear = '1') and
					(sensitive_transition = '1') and (condition_combination = '1') and (time_A_value = 1) )
					) then

				for i in 0 to input_arc_number-1 loop
					if (input_arc_type(i) = ARC_BASIC_PT) then internal_remove_input_token(i) <= input_arc_weight(i);
					end if;
				end loop;
				for j in 0 to output_arc_number-1 loop
					internal_add_output_token(j) <= output_arc_weight(j);
				end loop;
				internal_active_transition <= '1';
			else
				for i in 0 to input_arc_number-1 loop
					internal_remove_input_token(i) <= 0;
				end loop;
				for j in 0 to output_arc_number-1 loop
					internal_add_output_token(j) <= 0;
				end loop;
				internal_active_transition <= '0';
			end if;
		end if;
	end process TokenProcess;

	------------------------------------------------
	-- Control signal of exception unit that is a copy of Token process with a different asynchronous reset
	ActiveExceptionUnit : process(reset_n, clock, sensitive_transition, condition_combination, time_counter, time_A_value, time_B_value, exception_transition_asynchronous_clear_MP)
	begin
		if ( (reset_n = '0') or (exception_transition_asynchronous_clear_MP = '1') ) then
			internal_exception_transition_active_exception_unit <= '0';
			
		elsif falling_edge(clock) then

			if ( ( (transition_type = TRANSITION_NO_TEMPORAL) and (sensitive_transition = '1') and (condition_combination = '1') )

				or ( (transition_type = TRANSITION_TEMPORAL_A_B) and (synchronous_timer_clear = '0') and
					(sensitive_transition = '1') and (condition_combination = '1') and (time_counter >= (time_A_value-1)) and (time_counter < time_B_value)
					and (time_A_value /= 0) and (time_B_value /= 0) )

				or ( (transition_type = TRANSITION_TEMPORAL_A_A) and (synchronous_timer_clear = '0') and
					(sensitive_transition = '1') and (condition_combination = '1') and (time_counter = (time_A_value-1)) and (time_A_value /= 0) )

				or ( (transition_type = TRANSITION_TEMPORAL_A_INFINITE) and (synchronous_timer_clear = '0') and
					(sensitive_transition = '1') and (condition_combination = '1') and (time_counter >= (time_A_value-1)) and (time_A_value /= 0) )

				or ( (transition_type /= TRANSITION_NO_TEMPORAL) and (synchronous_timer_clear = '1') and
					(sensitive_transition = '1') and (condition_combination = '1') and (time_A_value = 1) )
					) then
					
				internal_exception_transition_active_exception_unit <= '1';
			else
				internal_exception_transition_active_exception_unit <= '0';
			end if;
		end if;
	end process ActiveExceptionUnit;
	
	------------------------------------------------
	-- Priority
	PriorityProcess : process(priority_unit_authorization, internal_remove_input_token, internal_add_output_token, internal_active_transition)
	begin
		for i in 0 to input_arc_number-1 loop
			if (priority_unit_authorization = '1') then
				remove_input_token(i) <= internal_remove_input_token(i);
			else
				remove_input_token(i) <= 0;
			end if;
		end loop;
		for j in 0 to output_arc_number-1 loop
			if (priority_unit_authorization = '1') then
				add_output_token(j) <= internal_add_output_token(j);
			else
				add_output_token(j) <= 0;
			end if;
		end loop;
	end process PriorityProcess;

	s_active_transition <= internal_active_transition and priority_unit_authorization;
	active_transition <= s_active_transition;

	exception_transition_active_exception_unit <= internal_exception_transition_active_exception_unit and priority_unit_authorization;

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
--------------------------------------------------------------------------------
-- HILECOP GENERATED FILE 
-- 	HILECOP version 	: «Messages.VersionForTemplate»
-- 	Date 				: «new SimpleDateFormat("yyyy/MM/dd HH:mm").format(System.currentTimeMillis)»

-- COMPONENT
--	Name 				: Exception_unit.vhd

-- TRADUCTION
--	Traduction version 	: Transition-Pivot «version()»
--------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.petri.all;


entity exception_unit is
generic(
		place_number_in_macroP				: natural := 1;
		transition_number_in_macroP			: natural := 1;
		transition_temp_number_in_macroP	: natural := 1);
port(
		reset_n						: in std_logic;
		active_exception_transition	: in std_logic;
		active_place_i				: in std_logic_vector (place_number_in_macroP-1 downto 0);
		active_transition_i			: in std_logic_vector (transition_number_in_macroP-1 downto 0);
		timer_clear_ack_i			: in std_logic_vector (transition_temp_number_in_macroP-1 downto 0);
		clear						: out std_logic);
end exception_unit;


architecture exception_unit_architecture of exception_unit is
	signal reset_d : std_logic;
	signal enable_d : std_logic;
	signal active_place_i_sum : std_logic;
	signal active_transition_i_sum : std_logic;
	signal timer_clear_ack_i_sum : std_logic;

begin

	------------------------------------------------
	ActivePlaceSum : process (active_place_i)
	variable internal_active_place_i_sum : std_logic;
	begin
		internal_active_place_i_sum := '0';
		for i in 0 to place_number_in_macroP-1 loop
			internal_active_place_i_sum := internal_active_place_i_sum or active_place_i(i);
		end loop;
		active_place_i_sum <= internal_active_place_i_sum;
	end process ActivePlaceSum;
	
	------------------------------------------------
	ActiveTransitionSum : process (active_transition_i)
	variable internal_active_transition_i_sum : std_logic;
	begin
		internal_active_transition_i_sum := '0';
		for i in 0 to transition_number_in_macroP-1 loop
			internal_active_transition_i_sum := internal_active_transition_i_sum or active_transition_i(i);
		end loop;
		active_transition_i_sum <= internal_active_transition_i_sum;
	end process ActiveTransitionSum;
	
	------------------------------------------------
	TimersAckSum : process (timer_clear_ack_i)
	variable internal_timer_clear_ack_i_sum : std_logic;
	begin
		internal_timer_clear_ack_i_sum := '0';
		for j in 0 to transition_temp_number_in_macroP-1 loop
			internal_timer_clear_ack_i_sum := internal_timer_clear_ack_i_sum or timer_clear_ack_i(j);
		end loop;
		timer_clear_ack_i_sum <= internal_timer_clear_ack_i_sum;
	end process TimersAckSum;
	
	------------------------------------------------
	
	reset_d <= (not(reset_n)) or ( (not(active_place_i_sum)) and (not(active_transition_i_sum)) and (not(timer_clear_ack_i_sum)) and (not(active_exception_transition)) );

    enable_d <= active_place_i_sum or active_transition_i_sum;

    ------------------------------------------------
    d_flip_flop : process (reset_d, enable_d, active_exception_transition)
    begin
        if (reset_d = '1') then
            clear <= '0';
        elsif rising_edge(active_exception_transition) then
            if (enable_d = '1') then
                clear <= '1';
            end if;
        end if;
    end process;

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
	
	def generateFilePriorityUnit(String filename) {
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
--------------------------------------------------------------------------------
-- HILECOP GENERATED FILE 
-- 	HILECOP version 	: «Messages.VersionForTemplate»
-- 	Date 				: «new SimpleDateFormat("yyyy/MM/dd HH:mm").format(System.currentTimeMillis)»

-- COMPONENT
--	Name 				: Priority_unit.vhd

-- TRADUCTION
--	Traduction version 	: Transition-Pivot «version()»
--------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.petri.all;


entity priority_unit is
generic(
		transition_number	: natural := 2);
port(
		active_transition		: in std_logic_vector (transition_number-1 downto 0);
		priority_number			: in priority_vector (transition_number-1 downto 0);
		transition_authorization: out std_logic_vector (transition_number-1 downto 0));
end;


architecture priority_unit_architecture of priority_unit is

begin

gen_each_transitions:
for n_active_transition in 0 to transition_number-1 generate

	process(active_transition, priority_number)
	variable calcul_autorisation : std_logic;
	begin
		calcul_autorisation := '1';
		for n_others_transitions in 0 to transition_number-1 loop
			if ( (n_active_transition /= n_others_transitions) and (active_transition(n_others_transitions) = '1')
					and (priority_number(n_others_transitions) > priority_number(n_active_transition)) ) then
				calcul_autorisation := '0';
			end if;
		end loop;
		transition_authorization(n_active_transition) <= calcul_autorisation;
	end process;
	
end generate gen_each_transitions;

end priority_unit_architecture;
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
--------------------------------------------------------------------------------
-- HILECOP GENERATED FILE 
-- 	HILECOP version 	: «Messages.VersionForTemplate»
-- 	Date 				: «new SimpleDateFormat("yyyy/MM/dd HH:mm").format(System.currentTimeMillis)»

-- COMPONENT
--	Name 				: Macroplace.vhd

-- TRADUCTION
--	Traduction version 	: Transition-Pivot «version()»
--------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.petri.all;


entity macroplace is
generic(
		place_number	 			: natural := 1;
		exception_arc_number		: natural := 1);
port(
		internal_place_activation	: in std_logic_vector(place_number-1 downto 0);
        output_token		       	: in weight_vector(exception_arc_number-1 downto 0);
		smaller_transitory_marking 	: out weight;
		active_macroplace	 	 	: out weight
		);
end;


architecture macroplace_architecture of macroplace is

signal s_active_macroplace 	: std_logic;
signal s_internal_output_token_sum 	: weight;

begin

    --Process for macroplace activation evaluation
	------------------------------------------------
	MacroplaceActivation : process(internal_place_activation)
	variable internal_active_macroplace : std_logic;
	begin
		internal_active_macroplace := '0';
		for i in 0 to place_number-1 loop	 	 	
				internal_active_macroplace := internal_active_macroplace or internal_place_activation(i);
		end loop;
		s_active_macroplace <= internal_active_macroplace;
	end process MacroplaceActivation;

	active_macroplace <= 1 when (s_active_macroplace = '1') else 0;

    --Process for transitory marking evaluation   
	------------------------------------------------
	SyncTimerClearProcess : process(output_token)
		variable internal_output_token_sum : weight;
	begin
		internal_output_token_sum := 0;
		for j in 0 to exception_arc_number-1 loop			
			internal_output_token_sum := internal_output_token_sum + output_token(j);
		end loop;
		s_internal_output_token_sum <= internal_output_token_sum;
	end process SyncTimerClearProcess;

    smaller_transitory_marking <= 1 when (s_internal_output_token_sum = 0) else 0;
	

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
}