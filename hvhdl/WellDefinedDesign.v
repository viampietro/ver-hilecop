(** * Well-definition of H-VHDL Design *)

Require Import common.CoqLib.
Require Import common.ListPlus.

Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.HVhdlTypes.

(** ** Uniqueness of Behavioral Part Identifiers *)

Definition CsHasUniqueCompIds (cstmt : cs) (compids : list ident):=
  AreCsCompIds cstmt compids
  /\ List.NoDup compids.

Definition CsHasUniquePIds (cstmt : cs) (lofcs : list cs) (pids : list ident):=
  AreCsPIds cstmt pids
  /\ List.NoDup pids.

Definition CsHasUniqueIds (cstmt : cs) (compids pids : list ident) :=
  AreCsCompIds cstmt compids /\ AreCsPIds cstmt pids /\ List.NoDup (compids ++ pids).

(** ** Uniqueness of H-VHDL Design Ids (declarative and behavioral parts) *)


Definition DesignHasUniqueIds (d : design) (genids portids sigids compids pids : list ident) : Prop :=
  let ids := (id__e d) :: (id__a d) :: genids ++ portids ++ sigids ++ compids ++ pids in
  AreDeclPartIds d genids portids sigids /\
  AreBehPartIds d compids pids /\
  List.NoDup ids /\
  (forall id__p sl vars body varids,
      InCs (cs_ps id__p sl vars body) (behavior d) ->
      AreVarIds vars varids ->
      List.NoDup (ids ++ varids)).
