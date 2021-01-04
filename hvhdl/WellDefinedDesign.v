(** * Well-definition of H-VHDL Design *)

Require Import common.Coqlib.
Require Import common.ListsPlus.

Require Import hvhdl.AbstractSyntax.
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

Definition AreCompIds (lofcs : list cs) (compids : list ident) : Prop :=
    let comp2id := fun cids cstmt => match cstmt with cs_comp id _ _ _ _ => cids ++ [id] | _ => cids end in
    FoldL comp2id lofcs [] compids.

Definition ArePIds (lofcs : list cs) (pids : list ident) : Prop :=
  let ps2id := fun psids cstmt => match cstmt with cs_ps id _ _ _ => psids ++ [id] | _ => psids end in
  FoldL ps2id lofcs [] pids.

Definition AreDeclPartIds (d : design) (genids portids sigids : list ident) : Prop :=
  AreGenIds (gens d) genids
  /\ ArePortIds (ports d) portids
  /\ AreSigIds (sigs d) sigids.

Definition AreBehPartIds (d : design) (lofcs : list cs) (compids pids : list ident) : Prop :=
  FlattenCs (behavior d) lofcs
  /\ AreCompIds lofcs compids 
  /\ ArePIds lofcs pids.

Definition AreVarIds (vars : list vdecl) (varids : list ident) : Prop :=
  let var2id := (fun vd : vdecl => let '(vdecl_ id _) := vd in id) in
  Map var2id vars varids.

Definition HasUniqueIds (d : design) : Prop :=
  exists genids portids sigids lofcs compids pids,
    let ids := (entid d) :: (archid d) :: genids ++ portids ++ sigids ++ compids ++ pids in
    
    AreDeclPartIds d genids portids sigids /\
    AreBehPartIds d lofcs compids pids /\
    List.NoDup ids /\
    (forall id__p sl vars body varids,
        List.In (cs_ps id__p sl vars body) lofcs ->
        AreVarIds vars varids ->
        List.NoDup (ids ++ varids)).
