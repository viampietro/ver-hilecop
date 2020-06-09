(** * Semantic Preservation Theorem *)

Require Import GenerateHVhdl.

(** Defines the relation stating that an SITPN execution environment
    and a H-VHDL design execution environment described the same
    behavior.

    - The environment [Ec] provides boolean values to the conditions
    of [sitpn] depending on the cycle count [tau] 
    
    - The environment [Ep] provides values (must be boolean) to the input
    ports of design [d] that implements the conditions of [sitpn].
*)

Definition sim_env () := term.

Theorem sitpn2vhdl_sound :
  forall sitpn d tau Ep Ec dimen s dstate mm,
    sitpn_to_hvhdl sitpn mm = Success d ->
.
