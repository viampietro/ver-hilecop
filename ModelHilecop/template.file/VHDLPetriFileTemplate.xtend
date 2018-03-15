package template.file

import java.io.ByteArrayInputStream
import java.text.SimpleDateFormat
import org.eclipse.core.resources.IFile

class VHDLPetriFileTemplate {
	def static addGeneralVHDLPetriFileTemplate(IFile file,int maxMarkup) {
		var content = '''
		-- HILECOP - Package Petri VHDL --
		
		-- File generated on : «new SimpleDateFormat("yyyy/MM/dd HH:mm").format(System.currentTimeMillis)»

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

package petri is
       constant marque_max_net : integer := «maxMarkup» ;  -- valeur fixée par l'éditeur
       type vect_link is array (natural range <>) of integer range 0 to marque_max_net ;
       type vec_at is array (natural range <>) of std_logic_vector(1 downto 0);
end petri;

--Fin de la génération VHDL -- HILECOP
		'''
		val is = new ByteArrayInputStream(content.getBytes());
		if(file.exists()) {
			file.setContents(is, false, false, null);
		}
		else {
			file.create(is, true, null);
		}
	}
	
	def static addBinaryVHDLPetriFileTemplate(IFile file,int maxMarkup) {
		var content = '''
		-- HILECOP - Package Petri Binaire VHDL --

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

package petri_b is
       type vec_at is array (natural range <>) of std_logic_vector(1 downto 0);
end petri_b;

--Fin de la génération VHDL -- HILECOP
		'''
		val is = new ByteArrayInputStream(content.getBytes());
		if(file.exists()) {
			file.setContents(is, false, false, null);
		}
		else {
			file.create(is, true, null);
		}
	}
	
	
	def static add_P_Pivot_VHDLPetriFileTemplate(IFile file,int maxMarkup) {
		var content = '''
		-- HILECOP - Package Petri PPivot VHDL --
library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

package petri is
		constant mark_max_net : natural := «maxMarkup»;
		-- valeur fixée par l'éditeur, seulement pour version pondérée
		
		type vect_link is array (natural range <>) of natural range 0 to mark_max_net; 
		-- seulement pour version pondérée
		
		type vect_at is array (natural range <>) of natural range 0 to 3;
		-- Type d'arc :
		--	* basic place -> transition 	= 0
		--	* test place -> transition 		= 1
		--	* inhibitor place -> transition = 2
		--	* basic transition -> place 	= 3
end petri;

--Fin de la génération VHDL -- HILECOP
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