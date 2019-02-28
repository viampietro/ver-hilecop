Require Import Hilecop.SPNAnimator.

(*! ============================= !*)
(*! ======= SPN Semantics ======= !*)
(*! ============================= !*)


(** * Preliminary definitions *)


(** * Semantics definition *)

(** Represents the two clock events regulating the SPN evolution. *)

Inductive clock : Set :=
| falling_edge : clock
| raising_edge : clock.

(** Represents the SPN Semantics  *)

Inductive SPNSemantics (spn : SPN) (fired : list trans_type) (spn' : SPN) : Prop :=
| SPNSemantics_falling_edge :
| SPNSemantics_raising_edge : .