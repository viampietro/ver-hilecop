Require Import Hilecop.Sitpn.Sitpn.

(** Renames all hypotheses resulting of the decomposition 
    of the IsWelldefinedSitpn predicate. *)

Ltac rename_well_defined_sitpn :=
  match goal with
  | [ H: NoDupPlaces ?sitpn |- _ ] =>
    rename H into Hnodup_places
  end;
  match goal with
  | [ H: NoDupTranss ?sitpn |- _ ] =>
    rename H into Hnodup_transs
  end;
  match goal with
  | [ H: NoUnknownInPriorityGroups ?sitpn |- _ ] =>
    rename H into Hno_unk_pgroups
  end;
  match goal with
  | [ H: NoIntersectInPriorityGroups ?sitpn |- _ ] =>
    rename H into Hno_inter
  end;
  match goal with
  | [ H: AreWellFormedTimeIntervals ?sitpn |- _ ] =>
    rename H into Hwell_formed_itvals
  end;
  match goal with
  | [ H: NoDupConditions ?sitpn |- _ ] =>
    rename H into Hnodup_cond
  end;
  match goal with
  | [ H: NoDupActions ?sitpn |- _ ] =>
    rename H into Hnodup_ac
  end;
  match goal with
  | [ H: NoDupFunctions ?sitpn |- _ ] =>
    rename H into Hnodup_fun
  end;
  match goal with
  | [ H: NoDupInNeighbours ?sitpn |- _ ] =>
    rename H into Hnodup_neigh
  end;
  match goal with
  | [ H: NoIsolatedPlace ?sitpn |- _ ] =>
    rename H into Hiso_place
  end;
  match goal with
  | [ H: NoUnknownPlaceInNeighbours ?sitpn |- _ ] =>
    rename H into Hunk_pl_neigh
  end;
  match goal with
  | [ H: NoIsolatedTrans ?sitpn |- _ ] =>
    rename H into Hiso_trans
  end;
  match goal with
  | [ H: AreWellDefinedPreEdges ?sitpn |- _ ] =>
    rename H into Hwell_def_pre
  end;
  match goal with
  | [ H: AreWellDefinedTestEdges ?sitpn |- _ ] =>
    rename H into Hwell_def_test
  end;
  match goal with
  | [ H: AreWellDefinedInhibEdges ?sitpn |- _ ] =>
    rename H into Hwell_def_inhib
  end;
  match goal with
  | [ H: AreWellDefinedPostEdges ?sitpn |- _ ] =>
    rename H into Hwell_def_post
  end.

Ltac explode_well_defined_sitpn :=
  match goal with
  | [ H: IsWellDefinedSitpn _ |- _ ] =>
    assert (H' := H); 
    unfold IsWellDefinedSitpn in H;
    decompose [and] H;
    intros;
    rename_well_defined_sitpn;
    clear H;
    rename H' into Hwell_def_sitpn
  end.

(** Renames all hypotheses resulting of the decomposition
    of IsWellDefinedSitpnState. *)

Ltac rename_well_defined_sitpn_state :=
  match goal with
  | [ H: incl ?s.(Sitpn.fired) (transs ?sitpn) |- _ ] =>
    rename H into Hincl_state_fired_transs
  | _ => fail "No hypothesis of the form incl (fired ?s) (transs ?sitpn) found"
  end;
  match goal with
  | [ H: NoDup ?s.(Sitpn.fired) |- _ ] =>
    rename H into Hnodup_state_fired
  | _ => fail "No hypothesis of the form NoDup (fired ?s) found"
  end;
  match goal with
  | [ H: ?sitpn.(Sitpn.places) = fst (split (Sitpn.marking ?s))
      |- _ ] =>
    rename H into Hwf_state_marking
  | _ => fail "No hypothesis of the form (places ?sitpn) = fst (split (marking ?s)) found"
  end;
  match goal with
  | [ H: (forall (t : Trans),
             In t ?sitpn.(Sitpn.transs) /\
             (Sitpn.s_intervals ?sitpn t) <> None <->
             In t (fst (split ?s.(Sitpn.d_intervals))))
      |- _ ] =>
    rename H into Hwf_state_ditvals
  | _ => fail "No hypothesis of the form 't ∈ Ti ⇔ I(t) ≠ ∅' found"
  end;
  match goal with
  | [ H: NoDup (fst (split (Sitpn.d_intervals ?s))) |- _ ] =>
    rename H into Hnodup_state_ditvals
  | _ => fail "No hypothesis of the form 'NoDup (fst (split (d_intervals s)))' found"
  end;
  match goal with
  | [ H: (forall (t : Trans),
             In t ?sitpn.(Sitpn.transs) /\
             (Sitpn.s_intervals ?sitpn t) <> None <->
             In t (fst (split ?s.(Sitpn.reset))))
      |- _ ] =>
    rename H into Hwf_state_reset
  | _ => fail "No hypothesis of the form 't ∈ Ti ⇔ t ∈ reset' found"
  end;
  match goal with
  | [ H: NoDup (fst (split (Sitpn.reset ?s))) |- _ ] =>
    rename H into Hnodup_state_reset
  | _ => fail "No hypothesis of the form 'NoDup (fst (split (reset s)))' found"
  end;
  match goal with
  | [ H: (Sitpn.conditions ?sitpn) = fst (split (Sitpn.cond_values ?s))
      |- _ ] =>
    rename H into Hwf_state_condv
  | _ => fail "No hypothesis of the form 'C = (fst (split (cond_values s)))' found"
  end;
  match goal with
  | [ H: (Sitpn.actions ?sitpn) = fst (split (Sitpn.exec_a ?s))
      |- _ ] =>
    rename H into Hwf_state_execa
  | _ => fail "No hypothesis of the form 'A = (fst (split (exec_a s)))' found"
  end;
  match goal with
  | [ H: (Sitpn.functions ?sitpn) = fst (split (Sitpn.exec_f ?s))
      |- _ ] =>
    rename H into Hwf_state_execf
  | _ => fail "No hypothesis of the form 'A = (fst (split (exec_f s)))' found"
  end.

Ltac explode_well_defined_sitpn_state H :=
  match H with
  | H : IsWellDefinedSitpnState _ _  =>
    assert (H' := H); 
    unfold IsWellDefinedSitpnState in H;
    decompose [and] H;
    rename_well_defined_sitpn_state;
    clear H;
    rename H' into Hwell_def_state
  end.
