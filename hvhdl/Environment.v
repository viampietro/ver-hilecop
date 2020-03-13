(** Module defining the components of the simulation environment.  *)

Require Import Coqlib.
Require Import ListsPlus.
Require Import GlobalTypes.
Require Import AbstractSyntax.
Require Import SemanticalDomains.

(** Defines the design environment describing H-VHDL design instances
    in the semantical world. The design environment maps identifiers
    of a certain category of constructs (e.g, constant identifiers) to
    their declaration information (e.g, type and value for
    constants). *)

(* Needed because [SemanticalObject] as a recurvise definition that
   does not respect the strict positivity requirement.
   
   However, I am almost sure that it is not dangerous to do so. *)

Local Unset Positivity Checking.

(** Type of semantical objects that populate the design
    environment. *)
                                                     
Inductive SemanticalObject : Type :=
| Generic (t : type) (v : value)
| Constant (t : type) (v : value)
| Input (t : type)
| Output (t : type)
| Declared (t : type)
| Process (lenv : IdMap (type * value))
| Component (denv : IdMap SemanticalObject) (behavior : cs).

(** Macro definition for the design environment type. 
    Mapping from identifiers to 
 *)

Definition DEnv := IdMap SemanticalObject.

(** Defines an empty design environment. *)

Definition EmptyDEnv   := NatMap.empty SemanticalObject.

(** Defines the structure of design state. *)

Inductive DState  : Type :=
  MkDState {
      sigstore  : IdMap value;
      compstore : IdMap DState;
      events    : IdSet;
    }.

(** Defines an empty design state. *)

Definition EmptyDState := MkDState (NatMap.empty value)
                                   (NatMap.empty DState)
                                   (NatSet.empty).

(** Returns a DState with an empty event set. *)

Definition NoEvDState (dstate : DState) :=
  MkDState (sigstore dstate)
           (compstore dstate)
           (NatSet.empty).

(** Macro to add a new mapping id => value in the
    [sigstore] of od a design state [dstate].
 *)

Definition sstore_add (id : ident) (v : value) (dstate : DState) : DState :=
  MkDState (NatMap.add id v (sigstore dstate)) (compstore dstate) (events dstate).

(** Defines the [InSigStore] predicate that states that
    [id] is mapped in the [sigstore] of design state [dstate].

    Wrapper around the [In] predicate.
 *)

Definition InSStore (id : ident) (dstate : DState) :=
  NatMap.In id (sigstore dstate).

(** Defines a local environment of a process
    as a map from id to couples (type * value).
 *)

Definition LEnv := IdMap (type * value).

(** Defines an empty local environment. *)

Definition EmptyLEnv := NatMap.empty (type * value).

(** Definition of the [dom] function that yields a list of identifiers
    corresponding to the definition domain of an IdMap. *)

Definition dom {A : Type} (f : IdMap A) : list ident := fs (NatMap.elements f).
