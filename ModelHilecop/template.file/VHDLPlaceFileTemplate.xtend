package template.file

import java.io.ByteArrayInputStream
import java.text.SimpleDateFormat
import org.eclipse.core.resources.IFile

class VHDLPlaceFileTemplate {
		def static addGeneralVHDLPlaceFileTemplate(IFile file) {
		var content = '''
		-- HILECOP - Composant Place VHDL --
		
		-- File generated on : «new SimpleDateFormat("yyyy/MM/dd HH:mm").format(System.currentTimeMillis)»

library ieee;
library work;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.petri.all;

entity place is
generic ( nb_entrees   : integer := 1;
          nb_sorties   : integer := 1;
          marque_max_p : integer := marque_max_net);
port    ( clk          : in std_logic;
          reset_n      : in std_logic;
          ini_jetons   : in integer range 0 to marque_max_p; -- marque_max_net ?
          aj_jetons    : in vect_link (nb_entrees-1 downto 0);
          ret_jetons   : in vect_link (nb_sorties-1 downto 0);
          marque       : out integer range 0 to marque_max_p); -- marque_max_net ?
end;

architecture a_place of place is

signal marquage : integer range 0 to marque_max_p; -- marque_max_net ?

begin

     process(clk, reset_n)
        variable sum_aj  : integer range 0 to marque_max_p; -- marque_max_net ?
        variable sum_ret : integer range 0 to marque_max_p; -- marque_max_net ?
     begin

          if ( reset_n = '0' ) then marquage <= ini_jetons;  -- initialisation du marquage
          elsif rising_edge(clk) then
                  sum_aj := 0;
                  sum_ret := 0;
                  for i in 0 to nb_entrees-1 loop -- jetons à ajouter
                         sum_aj := sum_aj + aj_jetons(i);
                  end loop;  -- i
                  for j in 0 to nb_sorties-1 loop -- jetons à retirer
                         sum_ret := sum_ret + ret_jetons(j);
                  end loop;  -- j
                  marquage <= marquage + sum_aj - sum_ret;
          end if;
     end process;
     marque <= marquage; -- positionnement du marquage (propagé)
end a_place;

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
	
	def static addBinaryVHDLPlaceFileTemplate(IFile file) {
		var content = '''
		-- HILECOP - Composant Place Binaire VHDL --

library ieee;
library work;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.petri_b.all;

entity place_b is
generic ( nb_entrees   : integer := 1;
          nb_sorties   : integer := 1);
port    ( clk          : in std_logic;
          reset_n      : in std_logic;
          ini_jetons   : in std_logic;
          aj_jetons    : in std_logic_vector(nb_entrees-1 downto 0);
          ret_jetons   : in std_logic_vector(nb_sorties-1 downto 0);
          marque       : out std_logic);
end;

architecture a_place_b of place_b is

signal marquage : std_logic;

begin

     process(clk, reset_n)
        variable sum_aj  : std_logic;
        variable sum_ret : std_logic;
     begin

          if ( reset_n = '0' ) then marquage <= ini_jetons;  -- initialisation du marquage
          elsif rising_edge(clk) then
                  sum_aj := '0';
                  sum_ret := '0';
                  for i in 0 to nb_entrees-1 loop -- jetons à ajouter
                         sum_aj := sum_aj or aj_jetons(i);
                  end loop;  -- i
                  for j in 0 to nb_sorties-1 loop -- jetons à retirer
                         sum_ret := sum_ret or ret_jetons(j);
                  end loop;  -- j
                  if sum_aj = '1' then marquage <= '1';
                  elsif sum_ret='1' then marquage <= '0';
                  end if;
          end if;
     end process;
     marque <= marquage; -- positionnement du marquage (propagé)
end a_place_b;

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
	
		def static add_P_Pivot_VHDLPlaceFileTemplate(IFile file) {
		var content = '''
				-- HILECOP - Composant Place PPivot VHDL --
------------------------------------------------------------------------------------------------
-- Composant Place
--
-- Méthode de synthèse RdP vers VHDL : P-Pivot, full synchrone, pondérée
-- Dernières modifications : 09/01/2014 par Guillaume Coppey (voir fichier de suivi)
-- 30/03/16 par B.Colombani : Ajout du signal clear pour gestion de la Macroplace
------------------------------------------------------------------------------------------------

library ieee;
library work;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.petri.all;

entity place is

generic(input_arc_count		: natural := 1;
		output_arc_count	: natural := 1;
		initial_markup 		: natural := 0;
		max_markup 			: natural := mark_max_net);
port(	clk					: in std_logic; 
		reset_n				: in std_logic; 
		clear				: in std_logic;
		output_arc_type		: in vect_at(0 to output_arc_count-1);
		input_arc_weight	: in vect_link(0 to input_arc_count-1);
		output_arc_weight	: in vect_link(0 to output_arc_count-1);
		input_arc_fire		: in std_logic_vector(0 to input_arc_count-1);
		output_arc_fire 	: in std_logic_vector(0 to output_arc_count-1);
		output_arc_sensitisation : out std_logic_vector(0 to output_arc_count-1);
		reset_timer			: out std_logic_vector(0 to output_arc_count-1);
		action_activation	: out std_logic);
end;

architecture a_place of place is

signal internal_markup : natural range 0 to max_markup;

begin

weighted_gen : if max_markup /= 1 generate
process(clk, reset_n)
	variable local_markup : natural range 0 to max_markup;
	variable sum_add : natural range 0 to max_markup;	
	variable sum_ret : natural range 0 to max_markup;	

begin

	if (reset_n = '0') then 
		internal_markup <= initial_markup; -- markup initialisation
		output_arc_sensitisation <= (others => '0');
		action_activation <= '0';
		
	elsif (clear = '0') then
		internal_markup <= 0; 
		output_arc_sensitisation <= (others => '0');
		action_activation <= '0';
		
	elsif rising_edge(clk) then
		local_markup := internal_markup;
		sum_add := 0;
		sum_ret := 0;	

		for i in 0 to input_arc_count-1 loop -- add token
			if (input_arc_fire(i) = '1') then 
				sum_add := sum_add + input_arc_weight(i);
			end if;
		end loop;
		for j in 0 to output_arc_count-1 loop -- retrieve token
			if (output_arc_fire(j) = '1' and output_arc_type(j) = 0) then -- if classic arc P->T
				sum_ret := sum_ret + output_arc_weight(j);
			end if;
		end loop;

		for l in 0 to output_arc_count-1 loop -- reset timer
			if ((internal_markup - sum_ret < output_arc_weight(l)) and (sum_ret > 0)) then
				reset_timer(l) <= '1';
			else
				reset_timer(l) <= '0';
			end if;
		end loop;
		
		-- update markup
		local_markup := local_markup + (sum_add - sum_ret);

		-- evaluation of output sensitisation
		for k in 0 to output_arc_count-1 loop 
			if (output_arc_type(k) = 2) then -- if inhibitor arc P->T
				if (local_markup >= output_arc_weight(k)) then
					output_arc_sensitisation(k) <= '0';
				else
					output_arc_sensitisation(k) <= '1';
				end if;
			elsif (local_markup >= output_arc_weight(k)) then -- if test or classic arc P->T
				output_arc_sensitisation(k) <= '1';
			else
				output_arc_sensitisation(k) <= '0';
			end if;
		end loop;
		
		-- signals for activation of action
		if (local_markup >= 1) then
			action_activation <= '1';
		else
			action_activation <= '0';
		end if;

		-- save markup
		internal_markup <= local_markup;
	end if;
end process;
end generate weighted_gen;

binary_gen : if max_markup = 1 generate
process(clk, reset_n)
	variable local_markup : natural range 0 to 1;
	variable add : std_logic ;	
	variable ret : std_logic ;	

begin
	if (reset_n = '0') then 
		internal_markup <= initial_markup; -- markup initialisation
		output_arc_sensitisation <= (others =>'0');
		action_activation <= '0';
		
	elsif (clear = '0') then
		internal_markup <= 0; 
		output_arc_sensitisation <= (others => '0');
		action_activation <= '0';
		
	elsif rising_edge(clk) then
		local_markup := internal_markup;
		add := '0';
		ret := '0';
		
		for i in 0 to input_arc_count-1 loop -- add token
			if (input_arc_fire(i) = '1') then 
				add := '1';
			end if;
		end loop;
		for j in 0 to output_arc_count-1 loop -- retrieve token
			if (output_arc_fire(j) = '1' and output_arc_type(j) = 0) then -- if classic arc P->T
				ret := '1';
			end if;
		end loop;
		
		for l in 0 to output_arc_count-1 loop -- reset timer
			if ((internal_markup = 1) and (ret = '1')) then
				reset_timer(l) <= '1';
			else
				reset_timer(l) <= '0';
			end if;
		end loop;
				
		-- update markup
		if (add = '1') then 
			local_markup := 1; -- priority to activation
		elsif (ret = '1') then 
			local_markup := 0;
		end if;
	
		-- evaluation of output sensitisation
		for k in 0 to output_arc_count-1 loop 
			if (output_arc_type(k) = 2) then -- if inhibitor arc P->T
				if (local_markup = 1) then
					output_arc_sensitisation(k) <= '0';
				else
					output_arc_sensitisation(k) <= '1';
				end if;
			elsif (local_markup = 1) then -- if test or classic arc P->T
				output_arc_sensitisation(k) <= '1';
			else
				output_arc_sensitisation(k) <= '0';
			end if;
		end loop;
		
		-- signals for activation of action
		if (local_markup = 1) then
			action_activation <= '1';
		else
			action_activation <= '0';
		end if;
		
		-- save markup
		internal_markup <= local_markup;
	end if;
end process;
end generate binary_gen;

end a_place;
		'''
		val is = new ByteArrayInputStream(content.getBytes());
		if(file.exists()) {
			file.setContents(is, false, false, null);
		}
		else {
			file.create(is, true, null);
		}
	}
	
	def static addP_Pivot_New_V1_VHDLPlaceFileTemplate(IFile file) {
		var content = '''
		-- HILECOP - Composant Place Binaire VHDL --

library ieee;
library work;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.petri_b.all;

entity place_b is
generic ( nb_entrees   : integer := 1;
          nb_sorties   : integer := 1);
port    ( clk          : in std_logic;
          reset_n      : in std_logic;
          ini_jetons   : in std_logic;
          aj_jetons    : in std_logic_vector(nb_entrees-1 downto 0);
          ret_jetons   : in std_logic_vector(nb_sorties-1 downto 0);
          marque       : out std_logic);
end;

architecture a_place_b of place_b is

signal marquage : std_logic;

begin

     process(clk, reset_n)
        variable sum_aj  : std_logic;
        variable sum_ret : std_logic;
     begin

          if ( reset_n = '0' ) then marquage <= ini_jetons;  -- initialisation du marquage
          elsif rising_edge(clk) then
                  sum_aj := '0';
                  sum_ret := '0';
                  for i in 0 to nb_entrees-1 loop -- jetons à ajouter
                         sum_aj := sum_aj or aj_jetons(i);
                  end loop;  -- i
                  for j in 0 to nb_sorties-1 loop -- jetons à retirer
                         sum_ret := sum_ret or ret_jetons(j);
                  end loop;  -- j
                  if sum_aj = '1' then marquage <= '1';
                  elsif sum_ret='1' then marquage <= '0';
                  end if;
          end if;
     end process;
     marque <= marquage; -- positionnement du marquage (propagé)
end a_place_b;

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