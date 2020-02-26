Require Import SemanticalDomains.
Require Import AbstractSyntax.

Inductive etype : tind -> type -> Prop :=
| etype_nat : etype Tind_natural (Tbase Tnat).
