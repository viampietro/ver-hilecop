(** * Evaluation of sequential statements. *)

Require Import Environment.
Require Import AbstractSyntax.

(** Defines the relation that evaluates the sequential statements
    of H-VHDL. 
    
    [vseq] does not define error cases.
 *)

Inductive vseq (denv : DEnv) (dstate : DState) (lenv : LEnv) : ss -> DState -> LEnv -> Prop :=

(** Evaluates a signal assignment statement where the target is a
    declared signal identifier. *)
  
| VSeqSigAssignSig :
    forall {id e},
      vseq denv dstate lenv (ss_sig (n_id id) e) 

.
