Require Import FMaps.

(** Defines maps with key of the positive type. *)

Module NMap := FMapWeakList.Make (N_as_OT).
Include NMap.

Module NMapFacts := Facts NMap.
Include NMapFacts.


Export NMap NMapFacts.
