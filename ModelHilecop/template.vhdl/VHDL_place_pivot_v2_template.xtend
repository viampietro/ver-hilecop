package template.vhdl

import field.PortMode
import field.SimpleConnection
import field.VHDLConstant
import field.VHDLGeneric
import field.VHDLPort
import field.VHDLSignal
import gestionPriorityTransition.PriorityGroup
import java.io.ByteArrayInputStream
import java.text.SimpleDateFormat
import java.util.ArrayList
import java.util.HashSet
import macroplace.ArcException
import org.eclipse.core.resources.IFile
import org.eclipse.emf.common.util.EList
import others.Messages
import petriNet.Arc
import petriNet.BasicArc
import petriNet.BasicNode
import petriNet.ClassicArc
import petriNet.InhibitorArc
import petriNet.Operator
import petriNet.Place
import petriNet.TestArc
import petriNet.TimeType
import petriNet.Transition
import petriNet.impl.PlaceImpl
import petriNet.impl.TransitionImpl
import root.HilecopComponent
import root.HilecopRoot
import script.VHDLAction
import script.VHDLCondition
import script.VHDLElement
import script.VHDLFunction
import script.VHDLRawCode
import script.VHDLTime
import script.VHDLTimeType
import script.impl.VHDLActionImpl
import script.impl.VHDLElementImpl
import template.interfaceTemplate.IVHDLTemplate

class VHDL_place_pivot_v2_template implements IVHDLTemplate {
	var HilecopComponent compo;
	
	override addVHDLTemplate(IFile file, HilecopRoot root, int maxMarkup,ArrayList<PriorityGroup> list_group_conflit) {
		var hilecopComponent = root.component
		this.compo = hilecopComponent
		var cpt = 0
		var BasicNode basicnode = null
		var fonction_parametres_reset = new HashSet<String>;
		var action_parametres_reset = new HashSet<String>;
		var list_max_time_counter = new ArrayList<String>();
		var String[] tab
		
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
-- This is the top design unit of the whole design hierarchy.
-- It mainly instantiates the sub-components of the HILECOP
-- methodology and their connections.
-- TODO
-- TODO Component:
-- TODO Name : «hilecopComponent.name»
-- TODO Author : «hilecopComponent.author»
-- TODO Description : «hilecopComponent.description»
-- TODO Version : «hilecopComponent.version»
-- TODO
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
«hilecopComponent.vhdHeader»
use work.petri.all;


----------------------------------------
-- «hilecopComponent.name» entity declaration
----------------------------------------
entity «hilecopComponent.name» is
   «IF hilecopComponent.fields.filter(typeof(VHDLGeneric)).size > 0»
   generic(
      «FOR gen : hilecopComponent.fields.filter(typeof(VHDLGeneric)) SEPARATOR ";"»
         «gen.name» : «gen.type» := «gen.defaultValue»
      «ENDFOR»
   );
   «ENDIF»
   port(
      clock : in std_logic; -- Entity clock
      «IF hilecopComponent.fields.filter(typeof(VHDLPort)).size > 0»
         reset_n : in std_logic; -- Active low asynchronous reset
         «FOR port : hilecopComponent.fields.filter(typeof(VHDLPort)) SEPARATOR ";"»
            «port.name» : «port.mode» «port.type»
         «ENDFOR»
      «ELSE»
         reset_n : in std_logic -- Active low asynchronous reset
      «ENDIF»
   );
end entity «hilecopComponent.name»;


----------------------------------------
-- «hilecopComponent.name» architecture
----------------------------------------
architecture «hilecopComponent.name»_architecture of «hilecopComponent.name» is

   ----------------------------------------
   -- USER DECLARATION
   ----------------------------------------

   -- Constants
   «FOR constant : hilecopComponent.fields.filter(typeof(VHDLConstant))»
      «IF constant.inputConnections.size == 0»
         constant «constant.name» : «constant.type» := «constant.defaultValue»;
      «ELSE»
         constant «constant.name» : «constant.type» := «constant.inputConnections.get(0).inputField.name»;
      «ENDIF»
   «ENDFOR»

   -- Signals
   «FOR signal : hilecopComponent.fields.filter(typeof(VHDLSignal))»
      signal «signal.name» : «signal.type»;
   «ENDFOR»


   ----------------------------------------
   -- PETRI NET DECLARATION
   ----------------------------------------

   ----------------------------------------
   -- Arc declaration
   ----------------------------------------

   -- Arc type constants
   «FOR arc : (hilecopComponent.PNStructureObjects.filter(typeof(ClassicArc)).filter[it.sourceNode instanceof Place])»
      constant arc_type_«arc.name» : arc_type_t := «IF arc instanceof BasicArc»ARC_BASIC_PT«ELSEIF arc instanceof TestArc»ARC_TEST«ELSEIF arc instanceof InhibitorArc»ARC_INHIBITOR«ELSE»ARC_BASIC_PT«ENDIF»;
   «ENDFOR»

   -- Arc weight constants
   «FOR arc : (hilecopComponent.PNStructureObjects.filter(typeof(ClassicArc)))»
      constant arc_weight_«arc.name» : weight_t := «arc.ruleExpression»;
   «ENDFOR»

   -- Arc valid signals
   «FOR arc : hilecopComponent.PNStructureObjects.filter(typeof(ClassicArc)).filter[it.sourceNode instanceof Place && it.targetNode instanceof Transition]»
      signal s_arc_valid_«arc.name» : std_logic;
   «ENDFOR»

   -- Priority authorization signals
   «FOR place :  hilecopComponent.PNStructureObjects.filter(typeof(Place)).filter[(it as PlaceImpl).isInSubGroup]»
«««      «FOR arc : place.sortedOutputArc.filter(typeof(BasicArc))»
      «FOR arc : place.sortedOutputArc»
         signal s_authorization_«arc.name» : std_logic;
      «ENDFOR»
   «ENDFOR»
   «FOR transition : hilecopComponent.PNStructureObjects.filter(typeof(Transition)).filter[(it as TransitionImpl).inMultiplePrioritySubGroup]»
      signal s_authorization_«transition.name» : std_logic;
   «ENDFOR»

   -- Reinitialisation time signals
   «FOR arc : hilecopComponent.PNStructureObjects.filter(typeof(ClassicArc)).filter[it.sourceNode instanceof Place && it.targetNode instanceof Transition]»
      signal s_reinit_time_«arc.name» : std_logic;
   «ENDFOR»
   «FOR mp : hilecopComponent.macroplace»
      «FOR arc_e : mp.arcs.filter(typeof(ArcException))»
         signal s_reinit_time_«mp.name»_exception_arc_«arc_e.transition.name» : std_logic;
      «ENDFOR»
      «IF mp.arcs.filter(typeof(ArcException)).size == 0»
         signal s_reinit_time_«mp.name» : std_logic;
      «ENDIF»
   «ENDFOR»


   ----------------------------------------
   -- Place declaration
   ----------------------------------------

   -- Initial marking constants
   «FOR place : hilecopComponent.PNStructureObjects.filter(typeof(Place))»
      constant initial_marking_«place.name» : weight_t := «place.marking»;
   «ENDFOR»

   -- Marked place signals
   «FOR place : (hilecopComponent.PNStructureObjects.filter(typeof(Place)).filter[it.actions.size > 0 || (it as PlaceImpl).isInMacroplace])»
      signal s_place_marked_«place.name» : std_logic;
   «ENDFOR»


   ----------------------------------------
   -- Transition declaration
   ----------------------------------------

   -- Fired transition signals
   «FOR transition : (hilecopComponent.PNStructureObjects.filter(typeof(Transition)))»
      signal s_transition_fired_«transition.name» : std_logic;
   «ENDFOR»

   -- Fired exception transition signals
   «FOR transition : hilecopComponent.PNStructureObjects.filter(typeof(Transition)).filter[(it as TransitionImpl).isTransitionException]»
      signal s_exception_transition_fired_«transition.name» : std_logic;
   «ENDFOR»

   -- Maximal time counter constants
   «FOR transition : (hilecopComponent.PNStructureObjects.filter(typeof(Transition)).filter[it.time != null])»
      constant maximal_time_counter_«transition.name» : natural := «getMaxTimeCounter(transition)»;
   «ENDFOR»

   -- Static temporal transition constants
   «FOR transition : (hilecopComponent.PNStructureObjects.filter(typeof(Transition)))»
      «IF transition.time != null»
         «IF transition.time.script_time == null»
            constant time_A_«transition.name» : natural := «transition.time.tmin»;
            «IF transition.time.timeType.equals(TimeType.AB)»
               constant time_B_«transition.name» : natural := «transition.time.tmax»;
            «ENDIF»
         «ENDIF»
      «ENDIF»
   «ENDFOR»

   -- Constant temporal transition constants
   «FOR transition : (hilecopComponent.PNStructureObjects.filter(typeof(Transition)))»
      «IF transition.time != null»
         «IF transition.time.script_time != null»
            «IF transition.time.script_time.type.equals(VHDLTimeType.CONSTANT)»
               constant time_A_«transition.name» : natural := «get_tmin_from_constant_time(transition.time.script_time)»;
               «IF transition.time.timeType.equals(TimeType.AB)»
                  constant time_B_«transition.name» : natural := «get_tmax_from_constant_time(transition.time.script_time)»;
               «ENDIF»
            «ENDIF»
         «ENDIF»
      «ENDIF»
   «ENDFOR»

   -- Dynamic temporal transition signals
   «FOR transition : (hilecopComponent.PNStructureObjects.filter(typeof(Transition)))»
      «IF transition.time != null»
         «IF transition.time.script_time != null»
            «IF transition.time.script_time.type.equals(VHDLTimeType.DYNAMIC)»
               signal time_A_«transition.name» : natural range 0 to maximal_time_counter_«transition.name»;
               «IF transition.time.timeType.equals(TimeType.AB)»
                  signal time_B_«transition.name» : natural range 0 to maximal_time_counter_«transition.name»;
               «ENDIF»
            «ENDIF»
         «ENDIF»
      «ENDIF»
   «ENDFOR»
 
   -- Transition temporal time cleared signals
   «FOR transition : (hilecopComponent.PNStructureObjects.filter(typeof(Transition)).filter[(it as TransitionImpl).isInMacroplace])»
      «IF transition.time != null»
         signal s_time_cleared_«transition.name» : std_logic;
      «ENDIF»
   «ENDFOR»

   -- True condition constant
   constant TRUE_CONDITION : std_logic := '1';

   -- Transition condition signals
   «FOR condition : hilecopComponent.VHDLElements.filter(typeof(VHDLCondition)).filter[it.associated_conditions.size>0]»
      «{cpt = 0;""}»
      signal s_«condition.name» : std_logic;
      «FOR t : hilecopComponent.PNStructureObjects.filter(typeof(Transition))»
         «FOR cond : t.conditions.filter[(it.script_condition.name == condition.name)&&(it.operator == Operator.NOT)]»
            «IF cpt == 0»
               signal s_not_«condition.name» : std_logic;
               «{cpt++;""}»
            «ENDIF»
         «ENDFOR»
      «ENDFOR»
    «ENDFOR»

   -- Exception asynchronous clear signals
   «FOR transition : hilecopComponent.PNStructureObjects.filter(typeof(Transition)).filter[(it as TransitionImpl).isTransitionException]»
      «FOR mp : (transition as TransitionImpl).liste_mp»
         signal s_exception_asynchronous_clear_«transition.name»_«mp» : std_logic;
      «ENDFOR»
      «IF (transition as TransitionImpl).liste_mp.size >1»
         signal s_exception_asynchronous_clear_«transition.name» : std_logic;
      «ENDIF»
   «ENDFOR»


   ----------------------------------------
   -- Macroplace declaration
   ----------------------------------------
   
   -- Macroplace asynchronous clear signals
   «FOR mp : hilecopComponent.macroplace»
      signal s_mp_asynchronous_clear_«mp.name» : std_logic;
   «ENDFOR»

   -- Enabled macroplace signals
   «FOR mp : hilecopComponent.macroplace»
   signal s_mp_enabled_«mp.name» : std_logic;
   «ENDFOR»   


   ----------------------------------------
   -- Declaration of action procedure
   ----------------------------------------

   «FOR action : hilecopComponent.VHDLElements.filter(typeof(VHDLAction)).filter[it.associated_actions.size>0]»
      «FOR place : hilecopComponent.PNStructureObjects.filter(typeof(Place))»
         «FOR p_action : place.actions.filter[it.script_action != null && it.script_action.name == action.name]»
            «{basicnode = place;(action as VHDLElementImpl).refreshParametersList(basicnode);""}»«««REFRESH DE LA LISTE DES PARAMETRES (copie de la vhdlAction dans le composant top
         «ENDFOR»
      «ENDFOR»
      ----------------------------------------
      -- ACTION
      --    Name: «action.name»
      procedure «action.name»«IF action.parametersForProcedureDeclaration.length > 0»(«action.parametersForProcedureDeclaration»)«ENDIF» is
      begin
      «IF !action.content.contains("reset_signal")»
         «action.content»
            return;
         end «action.name»;

      «ELSE»
         «{tab = traitementResetAction(action.content);""}»
         «tab.get(0)»
            return;
         end «action.name»;

         ----------------------------------------
         -- RESET_ACTION
         --    Name: «action.name»
         procedure «IF(action as VHDLActionImpl).svg_name_reset_action != null && (action as VHDLActionImpl).svg_name_reset_action != ""»«(action as VHDLActionImpl).svg_name_reset_action»«ELSE»reset_«action.name»«ENDIF»(«(action as VHDLActionImpl).parametersResetForProcedureDeclaration») is
         begin
         «traitement_reset(tab.get(1))»
            return;
         end «IF(action as VHDLActionImpl).svg_name_reset_action != null && (action as VHDLActionImpl).svg_name_reset_action != ""»«(action as VHDLActionImpl).svg_name_reset_action»«ELSE»reset_«action.name»«ENDIF»;

      «ENDIF»
   «ENDFOR»

   ----------------------------------------
   -- Declaration of function procedure
   ----------------------------------------

   «FOR fonction : hilecopComponent.VHDLElements.filter(typeof(VHDLFunction)).filter[it.associated_functions.size>0]»
      «FOR transition : hilecopComponent.PNStructureObjects.filter(typeof(Transition))»
         «FOR t_function : transition.functions.filter[it.script_function.name == fonction.name]»
            «{basicnode = transition;(fonction as VHDLElementImpl).refreshParametersList(basicnode);""}»«««REFRESH DE LA LISTE DES PARAMETRES (copie de la vhdlAction dans le composant top
         «ENDFOR»
      «ENDFOR»
      ----------------------------------------
      -- FUNCTION
      --    Name: «fonction.name»
      procedure «fonction.name»«IF fonction.parametersForProcedureDeclaration.length>0»(«fonction.parametersForProcedureDeclaration»)«ENDIF» is
      begin
      «fonction.content»
         return;
      end «fonction.name»;

   «ENDFOR»
   «{list_max_time_counter.clear;""}»

   ----------------------------------------
   -- Declaration of dynamic time procedure
   ----------------------------------------

   «FOR time : hilecopComponent.VHDLElements.filter(typeof(VHDLTime)).filter[it.associated_time.size>0]»«{list_max_time_counter.clear;""}»
   «FOR transition : hilecopComponent.PNStructureObjects.filter(typeof(Transition))»
      «IF transition.time != null && transition.time.script_time != null && transition.time.script_time.name.equals(time.name) && transition.time.script_time.type.equals(VHDLTimeType.DYNAMIC)»
         «IF !list_max_time_counter.contains(""+transition.time.tmax)»
           «{list_max_time_counter.add(""+transition.time.tmax);null}»
           ----------------------------------------
           -- DYNAMIC TIME
           --    Name: «time.name»_t«transition.time.tmax»
           procedure «time.name»_t«transition.time.tmax»(signal tmin : out integer range 0 to «transition.time.tmax»«IF timeContainsTMax(time.content)»; signal tmax : out integer range 0 to «transition.time.tmax»«ENDIF»«IF time.INOUTTypeParameters.size + time.OUTTypeParameters.size + time.INTypeParameters.size > 0»; «time.parametersForProcedureDeclaration»«ENDIF») is
           begin
           «time.content»
              return;
           end «time.name»_t«transition.time.tmax»;

         «ENDIF»
      «ENDIF»
   «ENDFOR»
   «ENDFOR»

   ----------------------------------------
   -- Declaration of condition function
   ----------------------------------------

   «FOR condition : hilecopComponent.VHDLElements.filter(typeof(VHDLCondition)).filter[it.associated_conditions.size>0]»
      «FOR transition : hilecopComponent.PNStructureObjects.filter(typeof(Transition))»
         «FOR t_condition : transition.conditions.filter[it.script_condition.name == condition.name]»
            «{basicnode = transition;(condition as VHDLElementImpl).refreshParametersList(basicnode);""}»«««REFRESH DE LA LISTE DES PARAMETRES (copie de la vhdlAction dans le composant top
         «ENDFOR»
      «ENDFOR»
      ----------------------------------------
      -- CONDITION
      --    Name: «condition.name»
      function «condition.name»«IF condition.parametersForProcedureDeclaration.length>0»(«condition.parametersForProcedureDeclaration»)«ENDIF» return boolean is
      begin
      «condition.content»
      end «condition.name»;
      
   «ENDFOR»

begin

   ----------------------------------------
   -- Instanciation of place
   ----------------------------------------

   «FOR place : hilecopComponent.PNStructureObjects.filter(typeof(Place))»
   ----------------------------------------
   -- PLACE
   --    Name: «place.name»
   --    Initial marking: «place.marking»
   «place.name» : entity work.place
   generic map(
      input_arcs_number => «IF place.inputArcs.filter(typeof(ClassicArc)).size == 0»1«ELSE»«place.inputArcs.filter(typeof(ClassicArc)).size»«ENDIF»,
      output_arcs_number => «IF place.outputArcs.filter(typeof(ClassicArc)).size == 0»1«ELSE»«place.outputArcs.filter(typeof(ClassicArc)).size»«ENDIF»
«««      maximal_marking => «maxMarkup»
«««      TODO MARQUAGE PLACE
«««      macroplace_enable => «IF ((place as PlaceImpl).isInMacroplace)»true«ELSE»false«ENDIF»
   )
   port map(
      clock => clock,
      reset_n => reset_n,
      initial_marking => initial_marking_«place.name»,
      «{cpt =0;""}»
      «IF place.inputArcs.filter(typeof(ClassicArc)).size == 0»
         input_arcs_weights(0) => 0,
      «ENDIF»
      «FOR arc : place.inputArcs.filter(typeof(ClassicArc))»
         input_arcs_weights(«cpt») => arc_weight_«arc.name»,
         «{cpt++;""}»
      «ENDFOR»
      «IF place.outputArcs.filter(typeof(ClassicArc)).size == 0»
         output_arcs_types(0) => ARC_BASIC_PT,
         output_arcs_weights(0) => 0,
      «ENDIF»
      «{cpt =0;""}»
      «FOR arc : place.sortedOutputArc»
         output_arcs_types(«cpt») => arc_type_«arc.name»,
         «{cpt++;""}»
      «ENDFOR»
      «{cpt=0;""}»
      «FOR arc : place.sortedOutputArc»
         output_arcs_weights(«cpt») => arc_weight_«arc.name»,
         «{cpt++;""}»
      «ENDFOR»
      «IF place.inputArcs.filter(typeof(ClassicArc)).size == 0»
         input_transitions_fired(0) => '0',
      «ENDIF»
      «{cpt=0;""}»
      «FOR arc : place.inputArcs.filter(typeof(ClassicArc))»
         input_transitions_fired(«cpt»«{cpt++;""}») => s_transition_fired_«(arc.sourceNode as BasicNode).name»,
      «ENDFOR»
      «{cpt=0;""}»
      «FOR arc : place.sortedOutputArc»
         output_transitions_fired(«cpt»«{cpt++;""}») => s_transition_fired_«(arc.targetNode as BasicNode).name»,
      «ENDFOR»
      «IF place.outputArcs.filter(typeof(ClassicArc)).size == 0»
         output_transitions_fired(0) => '0',
      «ENDIF»
      «IF (place as PlaceImpl).isInMacroplace»
         mp_asynchronous_clear => s_mp_asynchronous_clear_«(place as PlaceImpl).macroplaceName»,
      «ELSE»
         mp_asynchronous_clear => '0',
      «ENDIF»
      «{cpt=0;""}»
      «FOR arc : place.sortedOutputArc»
         output_arcs_valid(«cpt»«{cpt++;""}») => s_arc_valid_«arc.name»,
      «ENDFOR»
      «{cpt=0;""}»
      «IF (place as PlaceImpl).isInSubGroup»
         «FOR arc : place.sortedOutputArc»
            priority_authorizations(«cpt»«{cpt++;""}») => s_authorization_«arc.name»,
         «ENDFOR»
      «ELSE»
         priority_authorizations => open,
      «ENDIF»
      «{cpt=0;null}»
      «FOR arc : place.sortedOutputArc»
         reinit_transitions_time(«cpt»«{cpt++;""}») => s_reinit_time_«arc.name»,
      «ENDFOR»
      «IF place.outputArcs.filter(typeof(ClassicArc)).size == 0»
         output_arcs_valid => open,
         reinit_transitions_time => open,
      «ENDIF»
      marked => «IF place.actions.size>0 || (place as PlaceImpl).isInMacroplace»s_place_marked_«place.name»«ELSE»open«ENDIF»
   );

   «ENDFOR»

   ----------------------------------------
   -- Instanciation of transition
   ----------------------------------------

   «FOR transition :(hilecopComponent.PNStructureObjects.filter(typeof(Transition)))»
   ----------------------------------------
   -- TRANSITION
   --    Name: «transition.name»
   --    Type: «getTypeTransition(transition)»
   «transition.name» : entity work.transition 
   generic map(
      transition_type => «getTypeTransition(transition)»,
      input_arcs_number => «getInputArcNumber(transition)»,
      «IF transition.conditions.size > 0»
         conditions_number => «transition.conditions.size»,
      «ELSE»
         conditions_number => 1,
      «ENDIF»
      maximal_time_counter => «IF transition.time != null »maximal_time_counter_«transition.name»«ELSE»1«ENDIF»
«««      macroplace_enable => «IF (transition as TransitionImpl).isInMacroplace»true«ELSE»false«ENDIF»
   )
   port map(
      clock => clock,
      reset_n => reset_n,
      «IF transition.conditions.size == 0»
         input_conditions(0) => TRUE_CONDITION,
      «ELSE»
         «{cpt=0;""}»
         «FOR condition : transition.conditions» 
            «IF condition.operator == Operator.NOT»
               input_conditions(«cpt») => s_not_«condition.name.replaceFirst("not ","")»,
            «ELSE»
               input_conditions(«cpt») => s_«condition.name»,
            «ENDIF»
            «{cpt++;""}»
         «ENDFOR»
      «ENDIF»
      time_A_value => «getTimeA(transition)»,
      time_B_value => «getTimeB(transition)»,
      «{cpt=0;""}»
      «IF transition.inputArcs.filter(typeof(ClassicArc)).size == 0»
         «{cpt=1;""}»
         input_arcs_valid(0) => '1',
      «ELSE»
         «FOR arc : transition.inputArcs.filter(typeof(ClassicArc))»
            input_arcs_valid(«cpt»«{cpt++;""}») => s_arc_valid_«arc.name»,
         «ENDFOR»
      «ENDIF»
      «FOR mp : (transition as TransitionImpl).liste_mp»
         input_arcs_valid(«cpt»«{cpt++;""}») => s_mp_enabled_«mp»,
      «ENDFOR»
      «{cpt=0;""}»
      «IF transition.inputArcs.filter(typeof(ClassicArc)).size ==0»
         reinit_time(0) => '0',
         «{cpt++;"";}»
      «ENDIF»
      «FOR arc : transition.inputArcs.filter(typeof(ClassicArc))»
         reinit_time(«cpt»«{cpt++;""}») => s_reinit_time_«arc.name»,
      «ENDFOR»
      «FOR mp : (transition as TransitionImpl).liste_mp»
         reinit_time(«cpt»«{cpt++;""}») => s_reinit_time_«mp»_exception_arc_«transition.name»,
      «ENDFOR»
      «IF (transition as TransitionImpl).isInMacroplace»
         mp_asynchronous_clear => s_mp_asynchronous_clear_« (transition as TransitionImpl).macroplaceName»,
      «ELSE»
         mp_asynchronous_clear => «getAsynchronousTimerClear(transition)»,
      «ENDIF»
      «IF (transition as TransitionImpl).isInSubGroupConflict»
         «IF (transition as TransitionImpl).inMultiplePrioritySubGroup»
            priority_authorization => s_authorization_«transition.name»,
         «ELSE»
            priority_authorization => s_authorization_«FOR arc : transition.inputArcs.filter(typeof(BasicArc)).filter[(it.sourceNode as Place).name.equals(transition.getListSubGroupInConflict.get(0).place_conflit.name)]»«arc.name»«ENDFOR»,
         «ENDIF»
      «ELSE»
         priority_authorization => '1',
      «ENDIF»
      «IF (transition as TransitionImpl).isTransitionException»
         exception_asynchronous_clear => «IF (transition as TransitionImpl).liste_mp.size == 1»s_mp_asynchronous_clear_«(transition as TransitionImpl).liste_mp.get(0)»«ELSE»s_exception_asynchronous_clear_«transition.name»«ENDIF»,
         exception_fired => s_exception_transition_fired_«transition.name»,
      «ELSE»
         exception_asynchronous_clear => '1',
         exception_fired => open,
      «ENDIF»
      fired => s_transition_fired_«transition.name»,
      «IF transition.time != null && (transition as TransitionImpl).isInMacroplace»
         time_cleared => s_time_cleared_«transition.name»
      «ELSE»
         time_cleared => open
      «ENDIF»
   );

   «ENDFOR»

   ----------------------------------------
   -- Instanciation of exception unit
   ----------------------------------------

   «FOR transition :(hilecopComponent.PNStructureObjects.filter(typeof(Transition)).filter[(it as TransitionImpl).isTransitionException])»
   «FOR mp_name : (transition as TransitionImpl).liste_mp»
   ----------------------------------------
   -- EXCEPTION UNIT
   --    Name: exception_«transition.name»_«mp_name»
   exception_«transition.name»_«mp_name» : entity work.exception_unit
   generic map(
      mp_places_number => «IF getMacroplaceByName(mp_name).PNElements.filter(typeof(Place)).size==0»1«ELSE»«getMacroplaceByName(mp_name).PNElements.filter(typeof(Place)).size»«ENDIF»,
      mp_transitions_number => «IF getMacroplaceByName(mp_name).PNElements.filter(typeof(Transition)).size ==0»1«ELSE»«getMacroplaceByName(mp_name).PNElements.filter(typeof(Transition)).size»«ENDIF»,
      mp_temporal_transitions_number => «IF getMacroplaceByName(mp_name).PNElements.filter(typeof(Transition)).filter[it.time != null].size ==0»1«ELSE»«getMacroplaceByName(mp_name).PNElements.filter(typeof(Transition)).filter[it.time != null].size»«ENDIF»
   )
   port map(
      reset_n => reset_n,
      exception_transition_fired => s_exception_transition_fired_«transition.name»,
      «IF getMacroplaceByName(mp_name).PNElements.filter(typeof(Place)).size==0»
         mp_places_marked(0) => '0',
      «ENDIF»
      «{cpt=0;""}»
      «FOR place : getMacroplaceByName(mp_name).PNElements.filter(typeof(Place))»
         mp_places_marked(«cpt»«{cpt++;""}») => s_place_marked_«mp_name»_«place.name»,
      «ENDFOR»
      «IF getMacroplaceByName(mp_name).PNElements.filter(typeof(Transition)).size ==0»
         mp_transitions_fired(0) => '0',
      «ENDIF»
      «{cpt=0;""}»
      «FOR t_mp : getMacroplaceByName(mp_name).PNElements.filter(typeof(Transition))»
         mp_transitions_fired(«cpt»«{cpt++;""}») => s_transition_fired_«mp_name»_«t_mp.name»,
      «ENDFOR»
      «IF getMacroplaceByName(mp_name).PNElements.filter(typeof(Transition)).filter[it.time != null].size ==0»
         mp_temporal_transitions_cleared(0) => '0',
      «ENDIF»
      «{cpt=0;""}»
      «FOR t_mp : getMacroplaceByName(mp_name).PNElements.filter(typeof(Transition)).filter[it.time != null]»
         mp_temporal_transitions_cleared(«cpt»«{cpt++;""}») => s_time_cleared_«mp_name»_«t_mp.name»,
      «ENDFOR»
      asynchronous_clear => s_exception_asynchronous_clear_«transition.name»_«mp_name»
   );

   «ENDFOR»
   «ENDFOR»

   ----------------------------------------
   -- Instanciation of macroplace
   ----------------------------------------

   «FOR mp : hilecopComponent.macroplace»
   ----------------------------------------
   -- MACROPLACE
   --    Name: «mp.name»
   «mp.name» : entity work.macroplace
   generic map(
      internal_places_number => «IF mp.PNElements.filter(typeof(Place)).size==0»1«ELSE»«mp.PNElements.filter(typeof(Place)).size»«ENDIF»,
      exception_arcs_number => «IF mp.arcs.filter(typeof(ArcException)).size==0»1«ELSE»«mp.arcs.filter(typeof(ArcException)).size»«ENDIF»
   )
   port map(
      «IF mp.PNElements.filter(typeof(Place)).size==0»
         internal_places_marked(0) => '0',
      «ENDIF»
      «{cpt=0;""}»
      «FOR place : mp.PNElements.filter(typeof(Place))»
         internal_places_marked(«cpt»«{cpt++;""}») => s_place_marked_«mp.name»_«place.name»,
      «ENDFOR»
      «IF mp.arcs.filter(typeof(ArcException)).size ==0»
         reinit_exception_transition_time(0) => s_reinit_time_«mp.name»,
      «ENDIF»
      «{cpt=0;""}»
      «FOR arc : mp.arcs.filter(typeof(ArcException))»
         reinit_exception_transition_time(«cpt»«{cpt++;""}») => s_reinit_time_«mp.name»_exception_arc_«arc.transition.name»,
      «ENDFOR»
      macroplace_enabled => s_mp_enabled_«mp.name»
   );
   
   «ENDFOR»
   «{cpt = 0;""}»
   «FOR action : hilecopComponent.VHDLElements.filter(typeof(VHDLAction))»
      «{cpt+= action.associated_actions.size;""}»
   «ENDFOR»

   «IF hilecopComponent.VHDLElements.filter(typeof(VHDLAction)).size > 0 && cpt > 0»
   ------------------------------------------------------------
   -- Actions process
   -- This sequential process evaluates on the falling edge if the actions
   -- have to be executed.
   actions : process(clock, reset_n)
   begin
      if (reset_n = '0') then -- Reset of signals and output ports used in actions
         «FOR action : hilecopComponent.VHDLElements.filter(typeof(VHDLAction))»
            «IF action.associated_actions.size > 0»
               «FOR out_field :action.OUTTypeParameters»
                  «IF out_field instanceof VHDLPort»
                     «««out_field.name» <= «(out_field as VHDLPort).defaultValue»;
                     «{action_parametres_reset.add( out_field.name +" <= "+out_field.defaultValue+";");""}»
                  «ELSEIF out_field instanceof VHDLSignal»
                     «IF !(out_field.inputConnections.filter(typeof(SimpleConnection)).size > 0)»
                        «««out_field.name» <= «(out_field as VHDLSignal).defaultValue»;
                        «{action_parametres_reset.add( out_field.name +" <= "+(out_field as VHDLSignal).defaultValue+";");""}»
                     «ENDIF»
                  «ENDIF»
               «ENDFOR»
               «FOR out_field :action.INOUTTypeParameters»
                  «IF out_field instanceof VHDLPort»
                     «««out_field.name» <= «(out_field as VHDLPort).defaultValue»;
                     «{action_parametres_reset.add( out_field.name +" <= "+(out_field as VHDLSignal).defaultValue+";");""}»
                  «ELSEIF out_field instanceof VHDLSignal»«IF !(out_field.inputConnections.filter(typeof(SimpleConnection)).size > 0)»
                     «««out_field.name» <= «(out_field as VHDLSignal).defaultValue»;«ENDIF»
                     «{action_parametres_reset.add( out_field.name +" <= "+(out_field as VHDLSignal).defaultValue+";");""}»«ENDIF»
                  «ENDIF»
               «ENDFOR»
            «ENDIF»
         «ENDFOR»
         «FOR r_s : action_parametres_reset»
            «r_s»
         «ENDFOR»
      elsif falling_edge(clock) then 
      «FOR action : hilecopComponent.VHDLElements.filter(typeof(VHDLAction))»«{cpt=0;""}»
         «IF action.associated_actions.size >0»
            if («FOR place : hilecopComponent.PNStructureObjects.filter(typeof(Place))»«FOR p_action : place.actions.filter[it.script_action != null && it.script_action.name == action.name]»«IF cpt > 0» or «ENDIF»s_place_marked_«place.name» = '1'«{cpt++;""}»«ENDFOR»«ENDFOR») then
               «action.name»«IF action.parametersForProcedureCall.length>0»(«action.getParametersForProcedureCall»);
            «ENDIF»
            else
               «IF action.content.contains("reset_signal")»
                  «IF(action as VHDLActionImpl).svg_name_reset_action != null && (action as VHDLActionImpl).svg_name_reset_action != ""»«(action as VHDLActionImpl).svg_name_reset_action»«ELSE»reset_«action.name»«ENDIF»(«(action as VHDLActionImpl).getParametersResetForProcedureCall»);
               «ELSE»
                  «FOR field : action.OUTTypeParameters»
                     «IF field instanceof VHDLPort»
                        «field.name» <= «(field as VHDLPort).defaultValue»;
                     «ENDIF»
                     «IF field instanceof VHDLSignal»
                        «field.name» <= «(field as VHDLSignal).defaultValue»;
                     «ENDIF»
                  «ENDFOR»
               «ENDIF»
            end if;
         «ENDIF»
      «ENDFOR»
      end if;
   end process actions;
   «ENDIF»


   «IF hilecopComponent.VHDLElements.filter(typeof(VHDLFunction)).size >0 && hilecopComponent.VHDLElements.filter(typeof(VHDLFunction)).filter[it.associated_functions.size>0].size>0»
   ------------------------------------------------------------
   -- Functions process
   -- This sequential process evaluates on the rising edge if the functions
   -- have to be executed.
   functions : process(clock, reset_n)
   begin
      if (reset_n = '0') then -- Reset of signals and output ports used in functions
         «FOR fonction : hilecopComponent.VHDLElements.filter(typeof(VHDLFunction)).filter[it.associated_functions.size>0]»
            «FOR out_field :fonction.OUTTypeParameters»
               «IF out_field instanceof VHDLPort»
                  «««out_field.name» <= «(out_field as VHDLPort).defaultValue»;
                  «{fonction_parametres_reset.add( out_field.name +" <= "+out_field.defaultValue+";");""}»
               «ELSEIF out_field instanceof VHDLSignal && !(out_field.inputConnections.filter(typeof(SimpleConnection)).size > 0 )»
                  «««out_field.name» <= «(out_field as VHDLSignal).defaultValue»;
                  «{fonction_parametres_reset.add(out_field.name +" <= "+(out_field as VHDLSignal).defaultValue+";");""}»
               «ENDIF»
            «ENDFOR»
            «FOR out_field :fonction.INOUTTypeParameters»
               «IF out_field instanceof VHDLPort»
                  «««out_field.name» <= «(out_field as VHDLPort).defaultValue»;
                  «{fonction_parametres_reset.add( out_field.name +" <= "+out_field.defaultValue+";");""}»
               «ELSEIF out_field instanceof VHDLSignal && !(out_field.inputConnections.filter(typeof(SimpleConnection)).size > 0 )»
                  «««out_field.name» <= «(out_field as VHDLSignal).defaultValue»;
                  «{fonction_parametres_reset.add( out_field.name +" <= "+(out_field as VHDLSignal).defaultValue+";");""}»
               «ENDIF»
            «ENDFOR»
         «ENDFOR» 
         «FOR r_s : fonction_parametres_reset»
            «r_s»
         «ENDFOR»
      elsif rising_edge(clock) then
         «{cpt=0;""}»
         «FOR transition : hilecopComponent.PNStructureObjects.filter(typeof(Transition))»
            «{basicnode=transition;""}»
            «IF transition.functions.size  >0»
               if (s_transition_fired_«transition.name» = '1') then
                  «{cpt++;""}»
                  «FOR fonction : transition.functions»
                     «fonction.script_function.name»«IF fonction.script_function.parametersForProcedureCall.length>0»(«fonction.script_function.getParametersForProcedureCall»)«ENDIF»;
                  «ENDFOR»
               end if;
            «ENDIF»
         «ENDFOR»
      end if;
   end process functions;
   «ENDIF»


   ----------------------------------------
   -- Combinatory assignment
   ----------------------------------------

   -- Assessment of condition
   «FOR condition : hilecopComponent.VHDLElements.filter(typeof(VHDLCondition)).filter[it.associated_conditions.size>0]»
      s_«condition.name» <= '1' when «condition.name»«IF condition.parametersForProcedureCall.length>0»(«condition.getParametersForProcedureCall»)«ENDIF» else '0';
   «ENDFOR»

   -- Assessment of not condition signal
   «FOR condition : (hilecopComponent.VHDLElements.filter(typeof(VHDLCondition)))»
      «{cpt=0;""}»
      «FOR cond : condition.associated_conditions.filter[it.operator == Operator.NOT]»
         «IF cpt == 0»
            «{cpt=1;""}»
            s_not_«condition.name» <= not s_«condition.name»;
         «ENDIF»
      «ENDFOR»
   «ENDFOR»

   -- Assessment of dynamic time condition
   «FOR transition : hilecopComponent.PNStructureObjects.filter(typeof(Transition)).filter[it.time != null]»
      «IF transition.time.script_time != null && transition.time.script_time.type.equals(VHDLTimeType.DYNAMIC)»
         «transition.time.script_time.name»_t«transition.time.tmax»(time_A_«transition.name»«IF timeContainsTMax(transition.time.script_time.content)», time_B_«transition.name»«ENDIF»«IF transition.time.script_time.INOUTTypeParameters.size + transition.time.script_time.OUTTypeParameters.size + transition.time.script_time.INTypeParameters.size > 0», «transition.time.script_time.parametersForProcedureCall»«ENDIF»);
      «ENDIF»
   «ENDFOR»

   -- Signal assignments
   «FOR connection : hilecopComponent.connections.filter(typeof(SimpleConnection))»
      «IF !(connection.outputField instanceof VHDLConstant)»
         «connection.outputField.name»«IF(connection as SimpleConnection).targetSelectionExpression != null»«(connection as SimpleConnection).targetSelectionExpression»«ENDIF» <= «connection.inputField.name»«IF(connection as SimpleConnection).sourceSelectionExpression != null»«(connection as SimpleConnection).sourceSelectionExpression»«ENDIF»;
      «ENDIF»
   «ENDFOR»

   -- Macroplace signal assignments
   «FOR mp : hilecopComponent.macroplace»
      «IF mp.arcs.filter(typeof(ArcException)).size > 0»
         s_mp_asynchronous_clear_«mp.name» <= «FOR arc_exception : mp.arcs.filter(typeof(ArcException)) SEPARATOR " or "»s_exception_asynchronous_clear_«arc_exception.transition.name»_«mp.name»«ENDFOR»;
      «ELSE»
         s_mp_asynchronous_clear_«mp.name» <= '0';
      «ENDIF»   
   «ENDFOR»

   -- Transition exception with multi macroplace signal assignments
   «FOR transition : hilecopComponent.PNStructureObjects.filter(typeof(Transition)).filter[(it as TransitionImpl).isTransitionException]»
      «IF (transition as TransitionImpl).liste_mp.size > 1»
         s_exception_asynchronous_clear_«transition.name» <= «FOR mp :(transition as TransitionImpl).liste_mp SEPARATOR ' or '»s_mp_asynchronous_clear_«mp»«ENDFOR»;
      «ENDIF»
  «ENDFOR»

   -- Static port assignments
   «FOR port : hilecopComponent.fields.filter(typeof(VHDLPort)).filter[(it.defaultValue != null && it.defaultValue != "")&&(it.mode.equals(PortMode.OUT) || it.mode.equals(PortMode.INOUT))]»
      «{cpt=0;""}»
      «FOR elt : hilecopComponent.VHDLElements.filter[it instanceof VHDLAction || it instanceof VHDLFunction || it instanceof VHDLRawCode]»
         «FOR field : elt.OUTTypeParameters»
            «IF field.name.equals(port.name)»
               «{cpt++;""}»
            «ENDIF»
         «ENDFOR»
         «IF cpt==0»
            «FOR field : elt.INOUTTypeParameters»
               «IF field.name.equals(port.name)»
                  «{cpt++;""}»
               «ENDIF»
            «ENDFOR»
         «ENDIF»
      «ENDFOR»
      «{cpt+=port.inputConnections.filter(typeof(SimpleConnection)).size;""}»
   «IF cpt == 0»«port.name» <= «port.defaultValue»;«ENDIF»
  «ENDFOR»

   -- Static signal assignments
   «FOR signal : hilecopComponent.fields.filter(typeof(VHDLSignal)).filter[(it.defaultValue != null && it.defaultValue != "")]»«{cpt=0;""}»
      «FOR elt : hilecopComponent.VHDLElements.filter[it instanceof VHDLAction || it instanceof VHDLFunction || it instanceof VHDLRawCode]»
         «FOR field : elt.OUTTypeParameters»
            «IF field.name.equals(signal.name)»
               «{cpt++;""}»
            «ENDIF»
         «ENDFOR»
         «IF cpt==0»
            «FOR field : elt.INOUTTypeParameters»
               «IF field.name.equals(signal.name)»
                  «{cpt++;""}»
               «ENDIF»
            «ENDFOR»
         «ENDIF»
      «ENDFOR»
      «{cpt+=signal.inputConnections.filter(typeof(SimpleConnection)).size;""}»
   «IF cpt == 0»«signal.name» <= «signal.defaultValue»;«ENDIF»
   «ENDFOR»

   -- Priority authorization signal assignments
   «FOR transition : hilecopComponent.PNStructureObjects.filter(typeof(Transition)).filter[(it as TransitionImpl).inMultiplePrioritySubGroup]»
      s_authorization_«transition.name» <= «FOR arc : transition.inputArcs.filter(BasicArc).filter[(it.sourceNode as PlaceImpl).isInSubGroup] SEPARATOR " and "»s_authorization_«arc.name»«ENDFOR»;
   «ENDFOR»

   -- User raw code
   «FOR raw : hilecopComponent.VHDLElements.filter(typeof(VHDLRawCode))»
«raw.content»
   «ENDFOR»

end architecture «hilecopComponent.name»_architecture;
'''
	
				val is = new ByteArrayInputStream(content.getBytes());
				if(file.exists()) {
					file.setContents(is, false, false, null);
				}
				else {
					file.create(is, true, null);
				}
			}
	
	def getInputArcNumber(Transition transition) {
		var cpt = 0;
		if(transition.inputArcs.filter(typeof(ClassicArc)).size ==0)  {cpt = 1;}
		else {cpt = transition.inputArcs.filter(typeof(ClassicArc)).size;}
		if((transition as TransitionImpl).isTransitionException)  {
			cpt += (transition as TransitionImpl).liste_mp.size;
		}
		return cpt;
	}
	
	
	def timeContainsTMax(String content) {
		if(content.contains("tmax ") || content.contains("tmax	")) {
			return true;
		}
		return false;
	}
	
	def get_tmin_from_constant_time(VHDLTime time) {
		var content = time.content
		if(content != null && !content.equals("")) {
			var pos_deb = content.indexOf("tmin")
			var sub = content.substring(pos_deb)
			sub = sub.replaceAll("tmin","")
			sub = sub.replaceAll("<=" ,"")
//			var pos_fin = sub.indexOf(";")
//			sub = sub.trim
//			println("SUB : "+sub)
//			sub = sub.substring(0,pos_fin)
//			return sub.trim
//			println("SUB : "+sub)
			sub = sub.replaceAll(";","")
			return sub.trim
		}
		else return 0;
	}
	
	def get_tmax_from_constant_time(VHDLTime time) {
		var content = time.content
		if(content != null && !content.equals("") && content.contains("tmax")) {
			var pos_deb = content.indexOf("tmax")
			var sub = content.substring(pos_deb)
			sub = sub.replaceAll("tmax","")
			sub = sub.replaceAll("<=" ,"")
			var pos_fin = sub.indexOf(";")
			sub = sub.substring(0,pos_fin)
			return sub.trim
		}
		else return 0;
	}
	
	def getAsynchronousTimerClear(Transition transition) {
		if(transition.time == null) return "'0'" else return "'0'"
	}
	
	def getMaxTimeCounter(Transition transition) {
		if(transition.time == null) return "1" // Transition sans TIME
		else { // Transitiona avec TIME
			var time = transition.time
			if(time.script_time != null) { 
				if(time.script_time.type.equals(VHDLTimeType.CONSTANT)) {// Transition TIME CONSTANT
					if(time.timeType.equals(TimeType.AA) || time.timeType.equals(TimeType.AINFINITY)) {
						return get_tmin_from_constant_time(transition.time.script_time)
					}
					else {
						return get_tmax_from_constant_time(transition.time.script_time)
					}
				}
				else {// Transition TIME DYNAMIC
					return time.tmax
				}
			}
			else {  //TIME STATIC
				if(time.timeType.equals(TimeType.AA) || time.timeType.equals(TimeType.AINFINITY)) {
					return ""+time.tmin
				}
				else {
					return ""+time.tmax
				}
			}
		}
	}
	
	def getTimeA(Transition transition) {
		if(transition.time == null) return "0" // Transition non temporelle
		else { // Transition temp
			var time = transition.time
			if(time.tmax == 0) {
				return "time_A_"+transition.name
			}
			else if(time.tmin == time.tmax) {
				return "time_A_"+transition.name
			}
			else {
				return "time_A_"+transition.name
			}
		}
	}
	
	def getTimeB(Transition transition) {
		if(transition.time == null) return "0" // transition non temporelle
		else { // Transition temporelle
			var time = transition.time
			if(time.timeType.equals(TimeType.AA) || time.timeType.equals(TimeType.AINFINITY)) {
				return "0"
			}
			else {
				return "time_B_"+transition.name
			}
		}
	}
	
	
	
	def getTypeTransition(Transition transition) {
		if(transition.time == null) return "TRANSITION_NOT_TEMPORAL"
		else {
			var time = transition.time
			if(time.timeType.equals(TimeType.AINFINITY)) {
				return "TRANSITION_TEMPORAL_A_INFINITE"
			}
			else if(time.timeType.equals(TimeType.AA)) {
				return "TRANSITION_TEMPORAL_A_A"
			}
			else {
				return "TRANSITION_TEMPORAL_A_B"
			}
		}
	}
			
	
	def getMacroplaceByName(String mp_name) {
	 	for(mp :this.compo.macroplace) {
	 		if(mp.name.equals(mp_name)) {
	 			return mp
	 		}
	 	}
	 	return null
	}
			
			
			def traitement_reset(String reset_signal) {
				var split = reset_signal.split("\\)")
				return ("TO_REMOVE" + split.get(1)).replaceAll("TO_REMOVE[ ]*[\n]{0,1}", "")
			}
			
			def getParametersReset(HilecopComponent component, String reset_signal) {
				var split = reset_signal.split("\\)")
				var param = split.get(0)
				param = param.replace("(","")
				return getParameterByName(component,param)
			}
			
			def traitementResetAction(String content) {
				var split = content.split("reset_signal")
				var n_content = (split.get(0) + "TO_REMOVE").replaceAll("[\n]{0,1}[ ]*TO_REMOVE", "")
				var reset = split.get(1)
		//		split = reset.split(";")
		//		reset = split.get(0).trim()
		//		if (split.length >1) {
		//				n_content += "\t"+split.get(1)+";".trim()
		//			}
				return #[n_content,reset]
			}
			
			def getParameters(VHDLElement element) {
				var has_param = false
				var list_param = "("
				for (param : element.INTypeParameters) {
					if(param instanceof VHDLPort) {
						list_param+="signal "+param.name+" : "+param.mode+" "+param.type+",";
					}
					else if (param instanceof VHDLSignal) {
						
					}
				}
				for (param : element.INTypeParameters) {
					if(param instanceof VHDLPort) {
						list_param+="signal "+param.name+" : "+param.mode+" "+param.type+",";
					}
					else if (param instanceof VHDLSignal) {
						
					}
				}
				list_param+=")"
				if(has_param) return list_param 
				else return ""
			}
			
			def getParameters(HilecopComponent component, VHDLElement element) {
				var hasParam = false;
				var list_param = "("
				var list_nom =  newLinkedHashMap()
				for(p : component.fields.filter(typeof(VHDLPort))){
					list_nom.put(p.name,"port")
				}
				for(s : component.fields.filter(typeof(VHDLSignal))){
					list_nom.put(s.name,"signal")
				}
				var first = true
				for(param : list_nom.keySet) {
					if(element.content.contains(param)) {
						if(!first) list_param+=","
						hasParam= true;
						if(list_nom.get(param)=="port"){
							list_param+="signal "+port_infos(component,param)
						}
					}
				}
				list_param+=")"
				if(hasParam) return list_param
				else return ""
			}
			
				def getParameterList(HilecopComponent component,VHDLElement element) {
				var hasParam = false;
				var list_param = ""
				var list_nom =  newLinkedHashMap()
				for(p : component.fields.filter(typeof(VHDLPort))){
					list_nom.put(p.name,"port")
				}
				for(s : component.fields.filter(typeof(VHDLSignal))){
					list_nom.put(s.name,"signal")
				}
				var first = true
				for(param : list_nom.keySet) {
					if(element.content.contains(param)) {
						if(!first) list_param+=","
						hasParam= true;
						list_param+=param;
					}
				}
				list_param+=""
				if(hasParam) return list_param
				else return ""
			}
			
			
			def getParameterByName(HilecopComponent component, String param_name) {
				var list_param = "("
				var list_nom =  newLinkedHashMap()
				for(p : component.fields.filter(typeof(VHDLPort))){
					list_nom.put(p.name,"port")
				}
				for(s : component.fields.filter(typeof(VHDLSignal))){
					list_nom.put(s.name,"signal")
				}
				for(param : list_nom.keySet) {
					if(param_name == param) {
						if(list_nom.get(param)=="port"){
							list_param+="signal "+port_infos(component,param)
						}
					}
				}
				list_param+=")"
		        return list_param
		
			}
			
			def port_infos(HilecopComponent component, String port_name) {
				var ports = (component.fields.filter(typeof(VHDLPort))).filter[it.name == port_name]
				var port = ports.get(0)
				if(port != null) {
					return port.name+" : "+port.mode+" "+port.type
				}
				else 
					return "port_error";
			}
	

	
	override auteur() {
		return "Basé sur le code des Places/Transition/Petri/ExceptionUnit/PriorityUnit de G. Souquet du 29_07_2016)"
	}
	
	override infos() {
		"";
	}
	
	override version() {
		"1.0.0"
	}
	
}