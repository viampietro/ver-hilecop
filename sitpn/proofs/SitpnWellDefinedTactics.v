(** * Tactics for the IsWellDefined Predicate *)

Require Import sitpn.SitpnWellDefined.

Ltac build_nodup_places H :=
  lazymatch type of H with
  | IsWellDefined ?sitpn =>
    let Hndpls := fresh "NoDupPlaces" in
    destruct (H) as (_, (_, (_, (_, (_, (_, (Hndpls, _))))))); Hndpls
  | _ => let to := type of H in
         fail "Term" H "is of type" to "while it is expected to be of type IsWelldefined ?sitpn"
  end.

Ltac get_nodup_places H :=
  lazymatch type of H with
  | IsWellDefined ?sitpn =>
    constr:(proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))
  | _ => let to := type of H in
         fail "Term" H "is of type" to "while it is expected to be of type IsWelldefined ?sitpn"
  end.

