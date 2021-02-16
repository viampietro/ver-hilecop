(** * H-VHDL Simple Adder Design *)

Require Import common.Coqlib.
Require Import common.NatSet.
Require Import common.NatMap.
Require Import common.ListPlus.
Require Import common.ListPlusTactics.
Require Import common.ListPlusFacts.

Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.AbstractSyntaxFacts.
Require Import hvhdl.AbstractSyntaxTactics.
Require Import hvhdl.HVhdlTypes.
Require Import hvhdl.Environment.
Require Import hvhdl.Elaboration.
Require Import hvhdl.SemanticalDomains.
Require Import hvhdl.Petri.
Require Import hvhdl.WellDefinedDesign.
Require Import hvhdl.WellDefinedDesignFacts.

Local Open Scope abss_scope.
Local Open Scope natset_scope.

Import HVhdlCsNotations.

(** ** Input ports *)

(** Input port identifiers *)

Definition a : ident := 2.
Definition b : ident := S a.

(** Input port declarations *)

Definition ins : list pdecl := [pdecl_in a tind_boolean; pdecl_in b tind_boolean].

(** ** Output ports *)

(** Out port identifiers *)

Definition o : ident := S b.
Definition outs : list pdecl := [pdecl_out o tind_boolean].

(** ** Declared signals *)

(** Declared signal identifiers *)

Definition s_add : ident := S o.
Definition sigs : list sdecl := [sdecl_ s_add tind_boolean].

(** ** Adder behavior *)

(** Process "add" (combinational) *)

Definition add_ps_id : ident := S s_add.
Definition add_ps : cs := cs_ps add_ps_id {[ a, b ]} [] (s_add @<== (#a @|| #b)).

(** Process "publish" (synchronous) *)

Definition publish_ps_id : ident := S add_ps_id.
Definition publish_ps : cs := cs_ps publish_ps_id {[ clk ]} [] (Falling (o @<== #s_add)).

(** ** Adder design *)
Definition adder_id__e : ident := S publish_ps_id.
Definition adder_id__a : ident := S adder_id__e.
Definition adder : design := design_ adder_id__e adder_id__a [] (ins ++ outs) sigs
                                     (add_ps // publish_ps).
