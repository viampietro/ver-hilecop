(** * Well-definition of H-VHDL Design *)

Require Import common.Coqlib.
Require Import common.ListsPlus.

Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.AbstractSyntaxDefs.
Require Import hvhdl.HVhdlTypes.

(** ** Identifiers Unicity *)

(** A well-defined H-VHDL design must have unique identifiers. *)

Definition AreGenIds (gens : list gdecl) (genids : list ident) : Prop :=
  let gdecl2id := (fun gd : gdecl => let '(gdecl_ id τ e) := gd in id) in
  Map gdecl2id gens genids.

Definition ArePortIds (ports : list pdecl) (portids : list ident) : Prop :=
  let pdecl2id := fun pd => match pd with pdecl_in id _ | pdecl_out id _ => id end in
  Map pdecl2id ports portids.

Definition AreSigIds (sigs : list sdecl) (sigids : list ident) : Prop :=
  Map (fun sd : sdecl => let '(sdecl_ id _) := sd in id) sigs sigids.

Definition AreCompIds (behavior : cs) (compids : list ident) : Prop :=
  forall lofcs,
    FlattenCs behavior lofcs ->
    let comp2id := fun cids cstmt => match cstmt with cs_comp id _ _ _ _ => cids ++ [id] | _ => cids end in
    FoldL comp2id lofcs [] compids.

Definition ArePIds (behavior : cs) (pids : list ident) : Prop :=
  forall lofcs,
    FlattenCs behavior lofcs ->
    let ps2id := fun psids cstmt => match cstmt with cs_ps id _ _ _ => psids ++ [id] | _ => psids end in
    FoldL ps2id lofcs [] pids.

Inductive AreDeclPartIds (d : design) : list ident -> Prop :=
  AreDeclPartIds_ :
    forall genids portids sigids,
      AreGenIds (gens d) genids ->
      ArePortIds (ports d) portids ->
      AreSigIds (sigs d) sigids ->
      AreDeclPartIds d ((entid d) :: (archid d) :: genids ++ portids ++ sigids).

Inductive AreBehPartIds (d : design) : list ident -> Prop :=
  AreBehPartIds_ :
    forall compids pids,
      AreCompIds (behavior d) compids ->
      ArePIds (behavior d) pids ->
      AreBehPartIds d (compids ++ pids).

Definition HasUniqueIds (d : design) : Prop :=
  exists declids behids,
    AreDeclPartIds d declids /\
    AreBehPartIds d behids /\
    List.NoDup (declids ++ behids) /\
    (forall id__p sl vars body lofcs varids,
        FlattenCs (behavior d) lofcs ->
        List.In (cs_ps id__p sl vars body) lofcs ->
        let var2id := (fun vd : vdecl => let '(vdecl_ id _) := vd in id) in
        Map var2id vars varids ->
        List.NoDup (declids ++ behids ++ varids)).
