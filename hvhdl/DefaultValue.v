(** * Default values of types. *)

(** Defines the relation yielding the implicit default value 
    associated to a type. 
    
    This relation is useful to determine the default value
    associated to declared signals and variables during the
    elaboration phase.
 
 *)

Require Import GlobalTypes.
Require Import SemanticalDomains.

(** The [defaultv] relation states that a type is associated 
    to an implicit default value. *)

Inductive defaultv : type -> value -> Prop :=
  
| DefaultVBool : defaultv Tbool (Vbool false)
| DefaultVNat : forall {l u}, defaultv (Tnat l u) (Vnat l)
| DefaultVArray :
    forall {t l u v},
      defaultv t v ->
      defaultv (Tarray t l u) (Vlist (create_list (u - l + 1) v)).
