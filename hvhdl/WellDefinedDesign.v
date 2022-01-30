(** * Well-definition of H-VHDL Design *)

Require Import common.CoqLib.
Require Import common.ListPlus.

Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.HVhdlTypes.

(** ** H-VHDL Design Declarative Part Identifiers *)

Definition AreGenIds (gens : list gdecl) (genids : list ident) : Prop :=
  let gdecl2id := (fun gd : gdecl => let '(gdecl_ id τ e) := gd in id) in
  Map gdecl2id gens genids.

Definition ArePortIds (ports : list pdecl) (portids : list ident) : Prop :=
  let pdecl2id := fun pd => match pd with pdecl_in id _ | pdecl_out id _ => id end in
  Map pdecl2id ports portids.

Definition AreSigIds (sigs : list sdecl) (sigids : list ident) : Prop :=
  Map (fun sd : sdecl => let '(sdecl_ id _) := sd in id) sigs sigids.

(** ** H-VHDL Design Behavioral Part Identifiers *)

Definition AreCsCompIds (cstmt : cs) (compids : list ident) : Prop :=
  let comp2id := fun cids cstmt => match cstmt with cs_comp id _ _ _ _ => cids ++ [id] | _ => cids end in
  FoldLCs comp2id cstmt [] compids.

Definition get_cids (cstmt : cs) : list ident :=
  let comp2id := fun cids cstmt => match cstmt with cs_comp id _ _ _ _ => cids ++ [id] | _ => cids end in
  foldl_cs comp2id cstmt [].

Definition AreCsPIds (cstmt : cs) (pids : list ident) : Prop :=
  let ps2id := fun psids cstmt => match cstmt with cs_ps id _ _ _ => psids ++ [id] | _ => psids end in
  FoldLCs ps2id cstmt [] pids.

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

Definition AreDeclPartIds (d : design) (genids portids sigids : list ident) : Prop :=
  AreGenIds (gens d) genids
  /\ ArePortIds (ports d) portids
  /\ AreSigIds (sigs d) sigids.

Definition AreBehPartIds (d : design) (compids pids : list ident) : Prop :=
  AreCsCompIds (behavior d) compids /\ AreCsPIds (behavior d) pids.

Definition AreVarIds (vars : list vdecl) (varids : list ident) : Prop :=
  let var2id := (fun vd : vdecl => let '(vdecl_ id _) := vd in id) in
  Map var2id vars varids.

Definition DesignHasUniqueIds (d : design) (genids portids sigids compids pids : list ident) : Prop :=
  let ids := (id__e d) :: (id__a d) :: genids ++ portids ++ sigids ++ compids ++ pids in
  AreDeclPartIds d genids portids sigids /\
  AreBehPartIds d compids pids /\
  List.NoDup ids /\
  (forall id__p sl vars body varids,
      InCs (cs_ps id__p sl vars body) (behavior d) ->
      AreVarIds vars varids ->
      List.NoDup (ids ++ varids)).
