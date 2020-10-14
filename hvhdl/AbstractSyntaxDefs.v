(** * Misc. Definitions for the H-VHDL Abstract Syntax *)

Require Import hvhdl.AbstractSyntax.

(** States that a simple conc. statement [cstmt] is in a composition
    of concurrent statements [behavior].
    
    Always [False] if cstmt is of the form [x // y] (i.e, not a simple
    concurrent statement).  *)

Fixpoint InCs (cstmt : cs) (behavior : cs) {struct behavior} : Prop :=
  match behavior with
  | cs_ps pid sl vars stmt =>
    cstmt = cs_ps pid sl vars stmt
  | cs_comp compid entid gmap ipmap opmap =>
    cstmt = cs_comp compid entid gmap ipmap opmap
  | cs_par cstmt' cstmt'' =>
    InCs cstmt cstmt' \/ InCs cstmt cstmt''
  end.
