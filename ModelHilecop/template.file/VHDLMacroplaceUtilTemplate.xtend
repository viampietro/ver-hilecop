package template.file

import java.io.ByteArrayInputStream
import java.text.SimpleDateFormat
import org.eclipse.core.resources.IFile

class VHDLMacroplaceUtilTemplate {
	def static addHandlingClearTemplate(IFile file) {
		var content = '''
		-- HILECOP - Package MacroplaceUtil VHDL --
		
		-- File generated on : «new SimpleDateFormat("yyyy/MM/dd HH:mm").format(System.currentTimeMillis)»

library ieee;
library work;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

entity Handling_clear is
	port(
		clk : in std_logic;
		reset_n : in std_logic;
		sensibilisation_mp : in std_logic;
		tir_te : in std_logic;
		clear : out std_logic);
end Handling_clear;

architecture RTL of Handling_clear is

component BUFD
	port(
		A : in std_logic;
		Y : out std_logic);
end component;

signal clk_late_1 : std_logic;
signal clk_late_2 : std_logic;
signal clk_late_3 : std_logic;
signal clk_late_4 : std_logic;
signal clk_late_5 : std_logic;
signal clk_late_6 : std_logic;
signal clk_late_7 : std_logic;
signal clk_late_8 : std_logic;
signal clk_late_9 : std_logic;
signal clk_late : std_logic;
signal NOR2_0 : std_logic;
signal NOR2_1 : std_logic;
signal NOR2_2 : std_logic;
signal NOR2_3 : std_logic;
signal NOR2_4 : std_logic;
signal NOR2_5 : std_logic;
signal AND3_0 : std_logic;
signal AND2A_1 : std_logic;
signal OR2_0 : std_logic;
signal DFF_Q : std_logic;

begin 
-- Retard horloge (Non générique)

BUF_CLK_0 : BUFD port map (A=>clk, Y => clk_late_1);
BUF_CLK_1 : BUFD port map (A=>clk_late_1, Y => clk_late_2);
BUF_CLK_2 : BUFD port map (A=>clk_late_2, Y => clk_late_3);
BUF_CLK_3 : BUFD port map (A=>clk_late_3, Y => clk_late_4);
BUF_CLK_4 : BUFD port map (A=>clk_late_4, Y => clk_late_5);
BUF_CLK_5 : BUFD port map (A=>clk_late_5, Y => clk_late_6);
BUF_CLK_6 : BUFD port map (A=>clk_late_6, Y => clk_late_7);
BUF_CLK_7 : BUFD port map (A=>clk_late_7, Y => clk_late_8);
BUF_CLK_8 : BUFD port map (A=>clk_late_8, Y => clk_late_9);
BUF_CLK_9 : BUFD port map (A=>clk_late_9, Y => clk_late);


NOR2_0 <= not(sensibilisation_mp or NOR2_1);
NOR2_1 <= not(OR2_0 or NOR2_0);
NOR2_2 <= not(sensibilisation_mp or NOR2_0);
NOR2_3 <= not(AND3_0 or NOR2_4);
NOR2_4 <= not(NOR2_3 or not(reset_n));
NOR2_5 <= not(AND3_0 or NOR2_3);
AND3_0 <= tir_te and not(NOR2_2) and DFF_Q;
AND2A_1 <= not(NOR2_5) and NOR2_4;
OR2_0 <= AND2A_1 or not(reset_n);

process(clk_late, AND2A_1) begin
	if(AND2A_1 = '1') then
		DFF_Q <= '0';
	else if(clk_late'event and clk_late = '0') then
		DFF_Q <= '1';
	end if;
	end if;
end process;
clear <= AND2A_1;

end RTL;

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