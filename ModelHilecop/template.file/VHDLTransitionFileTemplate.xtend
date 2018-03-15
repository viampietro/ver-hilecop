package template.file

import java.io.ByteArrayInputStream
import java.text.SimpleDateFormat
import org.eclipse.core.resources.IFile

class VHDLTransitionFileTemplate {
	def static addGeneralVHDLTransitionFileTemplate(IFile file) {
		var content = '''
		-- HILECOP - Composant Transition VHDL --
		
		-- File generated on : «new SimpleDateFormat("yyyy/MM/dd HH:mm").format(System.currentTimeMillis)»

library ieee;
library work;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.petri.all;

entity transition is
generic( nb_entrees        : integer range 0 to 255 := 1;
         nb_sorties        : integer range 0 to 255 := 1;
         nb_termes         : integer range 0 to 255 := 1);
port(    clk               : in std_logic;
         reset_n           : in std_logic;
         c_t               : in std_logic_vector(nb_termes-1 downto 0);
         Ap                : in vect_link (nb_entrees-1 downto 0);
         At                : in vec_at(nb_entrees-1 downto 0);
         Me                : in vect_link (nb_entrees-1 downto 0);
         As                : in vect_link (nb_sorties-1 downto 0);
         ret_amont         : out vect_link (nb_entrees-1 downto 0);
         aj_aval           : out vect_link (nb_sorties-1 downto 0));
end;

architecture a_transition of transition is
begin

 process(clk,reset_n)
        variable sensibilisation : std_logic;
        variable condition : std_logic;

 begin

-- evaluation combinatoire de la condition

          condition:='1';
              for g in 0 to nb_termes-1 loop -- test condition
                  condition := condition and c_t(g);
              end loop;  -- g

          if reset_n = '0' then

               for i in 0 to nb_entrees-1 loop -- reset du flux de jetons consommé
                     ret_amont(i) <= 0;
                 end loop;  -- i
                 for j in 0 to nb_sorties-1 loop -- reset du flux de jetons produit
                     aj_aval(j) <= 0;
                 end loop;  -- j

            elsif falling_edge(clk) then  -- phase d'évaluation du franchissement

               for i in 0 to nb_entrees-1 loop -- reset du flux de jetons consommé
                     ret_amont(i) <= 0;
                 end loop;  -- i
                 for j in 0 to nb_sorties-1 loop -- reset du flux de jetons produit
                     aj_aval(j) <= 0;
                 end loop;  -- j
                 sensibilisation := '1';
                 for k in 0 to nb_entrees-1 loop -- test sensibilisation
                     if (At(k) = "00" or At(k) = "01") then -- si arc PT ou TST
                        if (Me(k) < Ap(k)) then sensibilisation := '0';
                        end if;
                     else
                        if At(k) = "10" then -- si arc INH
                            if Me(k) /= 0 then sensibilisation := '0';
                            end if;
                        end if;
                     end if;
                 end loop;  -- k
                 if ((sensibilisation = '1') and (condition = '1')) then
                     for l in 0 to nb_entrees-1 loop  -- flux de jetons consommé
                         if At(l)="00" then ret_amont(l) <= Ap(l);
                         end if;
                     end loop;  -- l
                     for m in 0 to nb_sorties-1 loop -- flux de jetons produit
                         aj_aval(m) <= As(m);
                     end loop;  -- m
                 end if;
              end if;
     end process;
end a_transition;

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
	
	def static addBinaryVHDLTransitionFileTemplate(IFile file) {
		var content = '''
		-- HILECOP - Composant Transition Binaire VHDL --

library ieee;
library work;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.petri_b.all;

entity transition_b is
generic( nb_entrees        : integer range 0 to 255 := 1;
         nb_sorties        : integer range 0 to 255 := 1;
         nb_termes         : integer range 0 to 255 := 1);
port(    clk               : in std_logic;
         reset_n           : in std_logic;
         c_t               : in std_logic_vector(nb_termes-1 downto 0);
         At                : in vec_at(nb_entrees-1 downto 0);
         Me                : in std_logic_vector(nb_entrees-1 downto 0);
         ret_amont         : out std_logic_vector(nb_entrees-1 downto 0);
         aj_aval           : out std_logic_vector(nb_sorties-1 downto 0));
end;

architecture a_transition_b of transition_b is
begin

 process(clk,reset_n)
        variable sensibilisation : std_logic;
        variable condition : std_logic;

 begin

-- evaluation combinatoire de la condition

          condition:='1';
              for g in 0 to nb_termes-1 loop -- test condition
                  condition := condition and c_t(g);
              end loop;  -- g

          if reset_n = '0' then

             for i in 0 to nb_entrees-1 loop -- reset du flux de jetons consommé
                     ret_amont(i) <= '0';
                 end loop;  -- i
                 for j in 0 to nb_sorties-1 loop -- reset du flux de jetons produit
                     aj_aval(j) <= '0';
                 end loop;  -- j

          elsif falling_edge(clk) then  -- phase d'évaluation du franchissement

             for i in 0 to nb_entrees-1 loop -- reset du flux de jetons consommé
                     ret_amont(i) <= '0';
                 end loop;  -- i
                 for j in 0 to nb_sorties-1 loop -- reset du flux de jetons produit
                     aj_aval(j) <= '0';
                 end loop;  -- j
                 sensibilisation := '1';
                 for k in 0 to nb_entrees-1 loop -- test sensibilisation
                     if (At(k) = "00" or At(k) = "01") then -- si arc PT ou TST
                        if (Me(k) = '0') then sensibilisation := '0';
                        end if;
                     else
                        if At(k) = "10" then -- si arc INH
                            if Me(k) = '1' then sensibilisation := '0';
                            end if;
                        end if;
                     end if;
                 end loop;  -- k
                 if ((sensibilisation = '1') and (condition = '1')) then
                     for l in 0 to nb_entrees-1 loop  -- flux de jetons consommé
                         if At(l)="00" then ret_amont(l) <= '1';
                         end if;
                     end loop;  -- l
                     for m in 0 to nb_sorties-1 loop -- flux de jetons produit
                         aj_aval(m) <= '1';
                     end loop;  -- m
                 end if;
              end if;
     end process;
end a_transition_b;

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
		def static add_P_Pivot_VHDLTransitionFileTemplate(IFile file) {
		var content = '''
		-- HILECOP - Composant Transition PPivot VHDL --

------------------------------------------------------------------------------------------------
-- Composant Transition
--
-- Méthode de synthèse RdP vers VHDL : P-Pivot, full synchrone, pondérée et binaire
-- Dernières modifications : 06/09/2013 par Guillaume Coppey (voir fichier de suivi)
------------------------------------------------------------------------------------------------

library ieee;
library work;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.petri.all;

entity transition is
generic(input_arc_count		: natural := 1;
		condition_count		: natural := 1);
port(	clk					: in std_logic;
		reset_n				: in std_logic;
		sensitisation		: in std_logic_vector(0 to input_arc_count-1);
		condition			: in std_logic_vector(0 to condition_count-1);
		fire				: out std_logic);
end;

architecture a_transition of transition is

begin

process(clk, reset_n, sensitisation, condition)
	variable sens : std_logic;
	variable cond : std_logic;
	
begin
	cond := '1';
	sens := '1';
	for f in 0 to condition_count-1 loop -- test condition
		cond := cond and condition(f);
	end loop; -- f

	for g in 0 to input_arc_count-1 loop -- test sensitisation
		sens := sens and sensitisation(g);
	end loop; -- g

	if (reset_n = '0') then 
		fire <= '0';
	elsif falling_edge(clk) then
		-- evaluation of firing
		if ((sens = '1') and (cond = '1')) then
			fire <= '1';
		else 
			fire <= '0';
		end if;
	end if;

end process;

end a_transition;


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