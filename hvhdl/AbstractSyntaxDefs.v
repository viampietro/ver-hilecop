(** * Misc. Definitions for the H-VHDL Abstract Syntax *)

Require Import common.Coqlib.
Require Import hvhdl.AbstractSyntax.

Open Scope abss_scope.

Include HVhdlCsNotations.

(** Relation between a concurrent statement and its list
    representation.  For a given [cstmt] and a list [l] of [cs],
    [FlattenCs ctsmt l] states that l is the flattened version of
    [cstmt].  *)

Inductive FlattenCs : cs -> list cs -> Prop :=
| FlattenCs_null_singl : FlattenCs cs_null nil
| FlattenCs_null_hd :
    forall cstmt l,
      FlattenCs cstmt l ->
      FlattenCs (cs_null // cstmt) l
| FlattenCs_ps_singl :
    forall id__p sl vars body,
      FlattenCs (cs_ps id__p sl vars body) [cs_ps id__p sl vars body]
| FlattenCs_ps_hd :
    forall id__p sl vars body cstmt l,
      FlattenCs cstmt l ->
      FlattenCs ((cs_ps id__p sl vars body) // cstmt) ((cs_ps id__p sl vars body) :: l)
| FlattenCs_comp_singl :
    forall id__c id__e gm ipm opm,
      FlattenCs (cs_comp id__c id__e gm ipm opm) [cs_comp id__c id__e gm ipm opm]
| FlattenCs_comp_hd :
    forall id__c id__e gm ipm opm cstmt l,
      FlattenCs cstmt l ->
      FlattenCs ((cs_comp id__c id__e gm ipm opm) // cstmt) ((cs_comp id__c id__e gm ipm opm) :: l).
