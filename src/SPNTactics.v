Require Import Hilecop.SPN.

(** Renames all hypotheses resulting of the decomposition 
    of the IsWelldefinedSpn predicate. *)

Ltac rename_well_defined_spn :=
  match goal with
  | [ H: NoDupPlaces ?spn |- _ ] =>
    rename H into Hnodup_places
  end;
  match goal with
  | [ H: NoDupTranss ?spn |- _ ] =>
    rename H into Hnodup_transs
  end;
  match goal with
  | [ H: NoUnknownInPriorityGroups ?spn |- _ ] =>
    rename H into Hno_unk_pgroups
  end;
  match goal with
  | [ H: NoIntersectInPriorityGroups ?spn |- _ ] =>
    rename H into Hno_inter
  end;
  match goal with
  | [ H: NoIsolatedPlace ?spn |- _ ] =>
    rename H into Hiso_place
  end;
  match goal with
  | [ H: NoUnknownPlaceInNeighbours ?spn |- _ ] =>
    rename H into Hunk_pl_neigh
  end;
  match goal with
  | [ H: NoUnknownTransInLNeighbours ?spn |- _ ] =>
    rename H into Hunk_tr_neigh
  end;
  match goal with
  | [ H: NoIsolatedTrans ?spn |- _ ] =>
    rename H into Hiso_trans
  end;
  match goal with
  | [ H: AreWellDefinedPreEdges ?spn |- _ ] =>
    rename H into Hwell_def_pre
  end;
  match goal with
  | [ H: AreWellDefinedTestEdges ?spn |- _ ] =>
    rename H into Hwell_def_test
  end;
  match goal with
  | [ H: AreWellDefinedInhibEdges ?spn |- _ ] =>
    rename H into Hwell_def_inhib
  end;
  match goal with
  | [ H: NoUnmarkedPlace ?spn |- _ ] =>
    rename H into Hunm_place
  end.

Ltac explode_well_defined_spn :=
  match goal with
  | [ H: IsWellDefinedSpn _ |- _ ] =>
    assert (H' := H); 
    unfold IsWellDefinedSpn in H;
    decompose [and] H;
    intros;
    rename_well_defined_spn;
    clear H;
    rename H' into Hwell_def_spn
  end.

Ltac rename_well_defined_spn_state :=
  match goal with
  | [ H: MarkingHaveSameStruct (initial_marking ?spn) ?s |- _ ] =>
    rename H into Hsame_marking_spn
  end;
  match goal with
  | [ H: incl (SPN.fired ?s) (transs ?spn) |- _ ] =>
    rename H into Hincl_fired_transs
  end;
  match goal with
  | [ H: NoDup (SPN.fired ?s) |- _ ] =>
    rename H into Hnodup_fired
  end.

Ltac explode_well_defined_spn_state :=
  match goal with
  | [ H: IsWellDefinedSpnState _ _ |- _ ] =>
    assert (H' := H); 
    unfold IsWellDefinedSpnState in H;
    decompose [and] H;
    intros;
    rename_well_defined_spn_state;
    clear H;
    rename H' into Hwell_def_state
  end.