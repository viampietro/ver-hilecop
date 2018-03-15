package template.file

import java.io.ByteArrayInputStream
import java.text.SimpleDateFormat
import org.eclipse.core.resources.IFile

class VHDLTransitionTempFileTemplate {
	def static addGeneralVHDLTransitionTempFileTemplate(IFile file) {
		var content = '''
		-- HILECOP - Composant Transition Temporelle VHDL --
		
		-- File generated on : «new SimpleDateFormat("yyyy/MM/dd HH:mm").format(System.currentTimeMillis)»

library ieee;
library work;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.petri.all;

entity transition_temp is
generic( nb_bits_temps     : integer range 0 to 255 := 24;
         nb_entrees        : integer range 0 to 255 := 1;
         nb_sorties        : integer range 0 to 255 := 1;
         nb_termes         : integer range 0 to 255 := 1);
port(    clk               : in std_logic;
         reset_n           : in std_logic;
         c_t               : in std_logic_vector(nb_termes-1 downto 0);
         t_min,t_max       : in integer range 0 to 2**nb_bits_temps;
         Ap                : in vect_link (nb_entrees-1 downto 0);
         At                : in vec_at(nb_entrees-1 downto 0);
         Me                : in vect_link (nb_entrees-1 downto 0);
         As                : in vect_link (nb_sorties-1 downto 0);
         ret_amont         : out vect_link (nb_entrees-1 downto 0);
         aj_aval           : out vect_link (nb_sorties-1 downto 0));
end;

architecture a_transition_temp of transition_temp is
begin

 process(clk,reset_n)
        variable sensibilisation : std_logic;
        variable condition : std_logic;
        variable cpt : integer range 0 to 2**nb_bits_temps;

 begin

-- evaluation combinatoire de la condition

          condition:='1';
              for g in 0 to nb_termes-1 loop -- test condition
                  condition := condition and c_t(g);
              end loop;  -- g

          if reset_n = '0' then

              cpt:=0;

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
                 if (sensibilisation = '1') then cpt := cpt + 1; -- inc. compteur temps
                 else cpt := 0; -- reset compteur temps
                 end if;
                 if ((cpt < t_min) or (cpt > t_max)) then sensibilisation := '0';
                 end if;
                 if ((sensibilisation = '1') and (condition = '1')) then
                     for l in 0 to nb_entrees-1 loop  -- flux de jetons consommé
                         if At(l)="00" then ret_amont(l) <= Ap(l);
                         end if;
                     end loop;  -- l
                     for m in 0 to nb_sorties-1 loop -- flux de jetons produit
                         aj_aval(m) <= As(m);
                     end loop;  -- m
                 cpt := 0 ;
                 end if;
              end if;
     end process;
end a_transition_temp;

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
	
	def static add_P_PIVOT_VHDLTransitionTempFileTemplate(IFile file) {
		var content = '''
		-- HILECOP - Composant Transition Temporelle PPivot VHDL --

------------------------------------------------------------------------------------------------
-- Composant Transition Temporelle
--
-- Méthode de synthèse RdP vers VHDL : P-Pivot, full synchrone, pondérée et binaire
-- Dernières modifications : 09/12/2013 par Guillaume Coppey (voir fichier de suivi)
------------------------------------------------------------------------------------------------

library ieee;
library work;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.petri.all;

entity transition_time is
generic(time_max			: natural := 1;
		input_arc_count		: natural := 1;
		condition_count		: natural := 1);
port(	clk					: in std_logic;
		reset_n				: in std_logic;
		t_min,t_max			: in natural range 0 to time_max;
		sensitisation		: in std_logic_vector(0 to input_arc_count-1);
		condition			: in std_logic_vector(0 to condition_count-1);
		reset_timer			: in std_logic_vector(0 to input_arc_count-1);
		fire				: out std_logic);
end;

architecture a_transition_time of transition_time is

begin

process(clk, reset_n, sensitisation, condition, reset_timer)
	variable sens : std_logic;
	variable cond : std_logic;
	variable reset_timer_sum : std_logic;
	variable timer : natural range 0 to time_max + 1;
	variable time_condition : std_logic;

begin
	cond := '1';
	for i in 0 to condition_count-1 loop -- test condition
		cond := cond and condition(i);
	end loop; -- i
		
	sens := '1';
	for j in 0 to input_arc_count-1 loop -- test sensitisation
		sens := sens and sensitisation(j);
	end loop; -- j
		
	reset_timer_sum := '0';
	for k in 0 to input_arc_count-1 loop -- test reset_timer input
		reset_timer_sum := reset_timer_sum or reset_timer(k);
	end loop; -- k
	-- if (reset_timer_sum = '1') then
		-- timer := 1;
	-- end if;
		
	if (reset_n = '0') then
		timer := 0;
		fire <= '0';
	elsif falling_edge(clk) then
		if (reset_timer_sum = '1') then
			timer := 1;
		elsif (sens = '1') then 
			if (timer <= t_max) then 
				timer := timer + 1; -- incrementation of timer
			end if;
		else 
			timer := 0; -- reset of timer
		end if;

		-- test of timer validity
		if ((timer < t_min) or (timer > t_max)) then
			time_condition := '0';
		else 
			time_condition := '1';
		end if;
		
		-- evaluation of firing
		if ((time_condition = '1') and (sens = '1') and (cond = '1')) then
			fire <= '1';
			timer := 0 ;
		else 
			fire <= '0';
		end if;
	end if;

end process;

end a_transition_time;

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
	
	def static addBinaryVHDLTransitionTempFileTemplate(IFile file) {
		var content = '''
		-- HILECOP - Composant Transition Temporelle Binaire VHDL --

library ieee;
library work;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.petri_b.all;

entity transition_temp_b is
generic(nb_bits_temps	: integer range 0 to 255 := 24;
		nb_entrees		: integer range 0 to 255 := 1;
		nb_sorties		: integer range 0 to 255 := 1;
		nb_termes		: integer range 0 to 255 := 1);
port(	clk				: in std_logic;
		reset_n			: in std_logic;
		c_t				: in std_logic_vector(nb_termes-1 downto 0);
		t_min,t_max		: in integer range 0 to 2**nb_bits_temps-1;
		At				: in vec_At(nb_entrees-1 downto 0);
		Me				: in std_logic_vector(nb_entrees-1 downto 0);
		ret_amont		: out std_logic_vector(nb_entrees-1 downto 0);
		aj_aval			: out std_logic_vector(nb_sorties-1 downto 0));
end;

architecture a_transition_temp_b of transition_temp_b is

signal condition : std_logic;
signal sensibilisation : std_logic;
signal compteur : integer range 0 to 2**nb_bits_temps-1;
signal tir_cours : std_logic;
signal ret_amont_int : std_logic_vector (nb_entrees-1 downto 0);
signal aj_aval_int : std_logic_vector (nb_sorties-1 downto 0);

begin

	------------------------------------------------
	-- Evaluation Condition
	prCondition : process(c_t)
	variable condition_interne : std_logic;
	begin
		condition_interne := '1';
		for g in 0 to nb_termes-1 loop -- test condition
			condition_interne := condition_interne and c_t(g);
		end loop;
		condition <= condition_interne;
	end process prCondition;

	------------------------------------------------
	-- Condition de Sensibilisation
	prSensib : process(Me, At)
	variable sensibilisation_interne : std_logic;
	begin
		sensibilisation_interne := '1';
		for k in 0 to nb_entrees-1 loop -- test reveil
			if (At(k) = "00" or At(k) = "01") then -- si arc PT ou TST
				if (Me(k) = '0') then sensibilisation_interne := '0';
				end if;
			else
				if At(k) = "10" then -- si arc INH
					if Me(k) = '1' then sensibilisation_interne := '0';
					end if;
				end if;
			end if;
		end loop;  -- k
		sensibilisation <= sensibilisation_interne;
	end process prSensib;

	------------------------------------------------
	-- Compteur
	prEntreeCompteur : process(reset_n, clk, sensibilisation)
	variable compteur_interne : integer range 0 to 2**nb_bits_temps-1;
	begin
		if reset_n = '0' then
			compteur_interne := 1;

		elsif (clk'event and clk='0') then
			if ( (sensibilisation = '1') and (tir_cours = '0') ) then
				compteur_interne := compteur + 1; -- inc. compteur temps
			else compteur_interne := 1; -- reset compteur temps
			end if;
		end if;
		compteur <= compteur_interne;
	end process prEntreeCompteur;

	------------------------------------------------
	-- Calcul Retrait Amont
	prAmont : process(reset_n, clk, sensibilisation, condition, compteur)
	begin
		if reset_n = '0' then
			for i in 0 to nb_entrees-1 loop -- reset du flux de jetons consommé
				ret_amont_int(i) <= '0';
			end loop;  -- i
			
		elsif (clk'event and clk='0') then  -- phase d'évaluation du franchissement
			if ((sensibilisation = '1') and (compteur >= t_min) and (compteur <= t_max)) then
				if (condition = '1') then
					for i in 0 to nb_entrees-1 loop  -- flux de jetons consommé
						if At(i)="00" then ret_amont_int(i) <= '1';
						end if;
					end loop;  -- i
				else
					for i in 0 to nb_entrees-1 loop -- reset du flux de jetons consommé
						ret_amont_int(i) <= '0';
					end loop;  -- i
				end if;
			else
				for i in 0 to nb_entrees-1 loop -- reset du flux de jetons consommé
					ret_amont_int(i) <= '0';
				end loop;  -- i
			end if;
		end if;
	end process prAmont;

	------------------------------------------------
	-- Calcul Ajout Aval
	prAval : process(reset_n, clk, sensibilisation, condition, compteur)
	begin
		if reset_n = '0' then
			for j in 0 to nb_sorties-1 loop -- reset du flux de jetons produit
				aj_aval_int(j) <= '0';
			end loop;  -- j
			
		elsif (clk'event and clk='0') then  -- phase d'évaluation du franchissement
			if ((sensibilisation = '1') and (compteur >= t_min) and (compteur <= t_max)) then
				if (condition = '1') then
					for j in 0 to nb_sorties-1 loop  -- flux de jetons produit
						aj_aval_int(j) <= '1';
					end loop;  -- j
				else
					for j in 0 to nb_sorties-1 loop -- reset du flux de jetons produit
						aj_aval_int(j) <= '0';
					end loop;  -- j
				end if;
			else
				for j in 0 to nb_sorties-1 loop -- reset du flux de jetons produit
					aj_aval_int(j) <= '0';
				end loop;  -- j
			end if;
		end if;
	end process prAval;
	
	------------------------------------------------
	-- Calcul Tir en cours
	prTirCours : process(ret_amont_int, aj_aval_int)
	variable tir_cours_interne : std_logic;
	begin
		tir_cours_interne := '0';
		for i in 0 to nb_entrees-1 loop
			if (ret_amont_int(i) /= '0') then
				tir_cours_interne := '1';
			end if;
		end loop;
		for j in 0 to nb_sorties-1 loop
			if (aj_aval_int(j) /= '0') then
				tir_cours_interne := '1';
			end if;
		end loop;
		tir_cours <= tir_cours_interne;
	end process prTirCours;
	
	ret_amont <= ret_amont_int;
	aj_aval <= aj_aval_int;

end a_transition_temp_b;

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