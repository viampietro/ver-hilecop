Require Import Hilecop.Sitpn.Sitpn.
Require Import Hilecop.Sitpn.SitpnSemantics.
Require Import Hilecop.Utils.HilecopLemmas.

(** Renames all hypotheses resulting of the decomposition 
    of the IsWelldefinedSitpn predicate. *)

Ltac rename_well_defined_sitpn :=
  match goal with
  | [ H: NoDupPlaces ?sitpn |- _ ] =>
    rename H into Hnodup_places
  | _ => idtac "No hypothesis of the form NoDupPlaces ?sitpn"
  end;
  match goal with
  | [ H: NoDupTranss ?sitpn |- _ ] =>
    rename H into Hnodup_transs
  | _ => idtac "No hypothesis of the form NoDupTranss ?sitpn"
  end;
  match goal with
  | [ H: NoUnknownInPriorityGroups ?sitpn |- _ ] =>
    rename H into Hno_unk_pgroups
  | _ => idtac "No hypothesis of the form NoUnknownInPriorityGroups ?sitpn"
  end;
  match goal with
  | [ H: NoIntersectInPriorityGroups ?sitpn |- _ ] =>
    rename H into Hno_inter
  | _ => idtac "No hypothesis of the form NoIntersectInPriorityGroups ?sitpn"
  end;
  match goal with
  | [ H: AreWellFormedTimeIntervals ?sitpn |- _ ] =>
    rename H into Hwell_formed_itvals
  | _ => idtac "No hypothesis of the form AreWellFormedTimeIntervals ?sitpn"
  end;
  match goal with
  | [ H: NoDupConditions ?sitpn |- _ ] =>
    rename H into Hnodup_cond
  | _ => idtac "No hypothesis of the form NoDupConditions ?sitpn"
  end;
  match goal with
  | [ H: NoDupActions ?sitpn |- _ ] =>
    rename H into Hnodup_ac
  | _ => idtac "No hypothesis of the form NoDupActions ?sitpn"
  end;
  match goal with
  | [ H: NoDupFunctions ?sitpn |- _ ] =>
    rename H into Hnodup_fun
  | _ => idtac "No hypothesis of the form NoDupFunctions ?sitpn"
  end;
  match goal with
  | [ H: NoDupInNeighbours ?sitpn |- _ ] =>
    rename H into Hnodup_neigh
  | _ => idtac "No hypothesis of the form NoDupInNeighbours ?sitpn"
  end;
  match goal with
  | [ H: NoIsolatedPlace ?sitpn |- _ ] =>
    rename H into Hiso_place
  | _ => idtac "No hypothesis of the form NoIsolatedPlace ?sitpn"
  end;
  match goal with
  | [ H: NoUnknownPlaceInNeighbours ?sitpn |- _ ] =>
    rename H into Hunk_pl_neigh
  | _ => idtac "No hypothesis of the form NoUnknownPlaceInNeighbours ?sitpn"
  end;
  match goal with
  | [ H: NoIsolatedTrans ?sitpn |- _ ] =>
    rename H into Hiso_trans
  | _ => idtac "No hypothesis of the form NoIsolatedTrans ?sitpn"
  end;
  match goal with
  | [ H: AreWellDefinedPreEdges ?sitpn |- _ ] =>
    rename H into Hwell_def_pre
  | _ => idtac "No hypothesis of the form AreWellDefinedPreEdges ?sitpn"
  end;
  match goal with
  | [ H: AreWellDefinedTestEdges ?sitpn |- _ ] =>
    rename H into Hwell_def_test
  | _ => idtac "No hypothesis of the form AreWellDefinedTestEdges ?sitpn"
  end;
  match goal with
  | [ H: AreWellDefinedInhibEdges ?sitpn |- _ ] =>
    rename H into Hwell_def_inhib
  | _ => idtac "No hypothesis of the form AreWellDefinedInhibEdges ?sitpn"
  end;
  match goal with
  | [ H: AreWellDefinedPostEdges ?sitpn |- _ ] =>
    rename H into Hwell_def_post
  | _ => idtac "No hypothesis of the form AreWellDefinedPostEdges ?sitpn"
  end.

(** Renames all hypotheses resulting of the decomposition 
    of the IsWelldefinedSitpn predicate. *)

Ltac clear_well_defined_sitpn :=
  match goal with
  | [ H: NoDupPlaces ?sitpn |- _ ] => clear H
  | _ => idtac "No hypothesis of the form NoDupPlaces ?sitpn"
  end;
  match goal with
  | [ H: NoDupTranss ?sitpn |- _ ] => clear H
  | _ => idtac "No hypothesis of the form NoDupTranss ?sitpn"
  end;
  match goal with
  | [ H: NoUnknownInPriorityGroups ?sitpn |- _ ] => clear H
  | _ => idtac "No hypothesis of the form NoUnknownInPriorityGroups ?sitpn"
  end;
  match goal with
  | [ H: NoIntersectInPriorityGroups ?sitpn |- _ ] => clear H
  | _ => idtac "No hypothesis of the form NoIntersectInPriorityGroups ?sitpn"
  end;
  match goal with
  | [ H: AreWellFormedTimeIntervals ?sitpn |- _ ] => clear H
  | _ => idtac "No hypothesis of the form AreWellFormedTimeIntervals ?sitpn"
  end;
  match goal with
  | [ H: NoDupConditions ?sitpn |- _ ] => clear H
  | _ => idtac "No hypothesis of the form NoDupConditions ?sitpn"
  end;
  match goal with
  | [ H: NoDupActions ?sitpn |- _ ] => clear H
  | _ => idtac "No hypothesis of the form NoDupActions ?sitpn"
  end;
  match goal with
  | [ H: NoDupFunctions ?sitpn |- _ ] => clear H
  | _ => idtac "No hypothesis of the form NoDupFunctions ?sitpn"
  end;
  match goal with
  | [ H: NoDupInNeighbours ?sitpn |- _ ] => clear H
  | _ => idtac "No hypothesis of the form NoDupInNeighbours ?sitpn"
  end;
  match goal with
  | [ H: NoIsolatedPlace ?sitpn |- _ ] => clear H
  | _ => idtac "No hypothesis of the form NoIsolatedPlace ?sitpn"
  end;
  match goal with
  | [ H: NoUnknownPlaceInNeighbours ?sitpn |- _ ] => clear H
  | _ => idtac "No hypothesis of the form NoUnknownPlaceInNeighbours ?sitpn"
  end;
  match goal with
  | [ H: NoIsolatedTrans ?sitpn |- _ ] => clear H
  | _ => idtac "No hypothesis of the form NoIsolatedTrans ?sitpn"
  end;
  match goal with
  | [ H: AreWellDefinedPreEdges ?sitpn |- _ ] => clear H
  | _ => idtac "No hypothesis of the form AreWellDefinedPreEdges ?sitpn"
  end;
  match goal with
  | [ H: AreWellDefinedTestEdges ?sitpn |- _ ] => clear H
  | _ => idtac "No hypothesis of the form AreWellDefinedTestEdges ?sitpn"
  end;
  match goal with
  | [ H: AreWellDefinedInhibEdges ?sitpn |- _ ] => clear H
  | _ => idtac "No hypothesis of the form AreWellDefinedInhibEdges ?sitpn"
  end;
  match goal with
  | [ H: AreWellDefinedPostEdges ?sitpn |- _ ] => clear H
  | _ => idtac "No hypothesis of the form AreWellDefinedPostEdges ?sitpn"
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
  | _ => fail "No hypothesis of the form IsWellDefinedSitpn found"
  end.

(** Renames all hypotheses resulting of the decomposition
    of IsWellDefinedSitpnState. *)

Ltac rename_well_defined_sitpn_state :=
  match goal with
  | [ H: incl ?s.(Sitpn.fired) (transs ?sitpn) |- _ ] =>
    rename H into Hincl_state_fired_transs
  | _ => idtac "No hypothesis of the form incl (fired ?s) (transs ?sitpn) found"
  end;
  match goal with
  | [ H: NoDup ?s.(Sitpn.fired) |- _ ] =>
    rename H into Hnodup_state_fired
  | _ => idtac "No hypothesis of the form NoDup (fired ?s) found"
  end;
  match goal with
  | [ H: ?sitpn.(Sitpn.places) = fst (split (Sitpn.marking ?s))
      |- _ ] =>
    rename H into Hwf_state_marking
  | _ => idtac "No hypothesis of the form (places ?sitpn) = fst (split (marking ?s)) found"
  end;
  match goal with
  | [ H: (forall (t : Trans),
             In t ?sitpn.(Sitpn.transs) /\
             (Sitpn.s_intervals ?sitpn t) <> None <->
             In t (fst (split ?s.(Sitpn.d_intervals))))
      |- _ ] =>
    rename H into Hwf_state_ditvals
  | _ => idtac "No hypothesis of the form 't ∈ Ti ⇔ I(t) ≠ ∅' found"
  end;
  match goal with
  | [ H: NoDup (fst (split (Sitpn.d_intervals ?s))) |- _ ] =>
    rename H into Hnodup_state_ditvals
  | _ => idtac "No hypothesis of the form 'NoDup (fst (split (d_intervals s)))' found"
  end;
  match goal with
  | [ H: (forall (t : Trans),
             In t ?sitpn.(Sitpn.transs) /\
             (Sitpn.s_intervals ?sitpn t) <> None <->
             In t (fst (split ?s.(Sitpn.reset))))
      |- _ ] =>
    rename H into Hwf_state_reset
  | _ => idtac "No hypothesis of the form 't ∈ Ti ⇔ t ∈ reset' found"
  end;
  match goal with
  | [ H: NoDup (fst (split (Sitpn.reset ?s))) |- _ ] =>
    rename H into Hnodup_state_reset
  | _ => idtac "No hypothesis of the form 'NoDup (fst (split (reset s)))' found"
  end;
  match goal with
  | [ H: (Sitpn.conditions ?sitpn) = fst (split (Sitpn.cond_values ?s)) |- _ ] =>
    rename H into Hwf_state_condv
  | _ => idtac "No hypothesis of the form 'C = (fst (split (cond_values s)))' found"
  end;
  match goal with
  | [ H: (Sitpn.actions ?sitpn) = fst (split (Sitpn.exec_a ?s)) |- _ ] =>
    rename H into Hwf_state_execa
  | _ => idtac "No hypothesis of the form 'A = (fst (split (exec_a s)))' found"
  end;
  match goal with
  | [ H: (Sitpn.functions ?sitpn) = fst (split (Sitpn.exec_f ?s)) |- _ ] =>
    rename H into Hwf_state_execf
  | _ => idtac "No hypothesis of the form 'A = (fst (split (exec_f s)))' found"
  end.

(** Clears all hypotheses resulting of the decomposition
    of IsWellDefinedSitpnState. *)

Ltac clear_well_defined_sitpn_state :=
  match goal with
  | [ H: incl ?s.(Sitpn.fired) (transs ?sitpn) |- _ ] => clear H
  | _ => idtac "No hypothesis of the form incl (fired ?s) (transs ?sitpn) found"
  end;
  match goal with
  | [ H: NoDup ?s.(Sitpn.fired) |- _ ] => clear H
  | _ => idtac "No hypothesis of the form NoDup (fired ?s) found"
  end;
  match goal with
  | [ H: ?sitpn.(Sitpn.places) = fst (split (Sitpn.marking ?s))
      |- _ ] => clear H
  | _ => idtac "No hypothesis of the form (places ?sitpn) = fst (split (marking ?s)) found"
  end;
  match goal with
  | [ H: (forall (t : Trans),
             In t ?sitpn.(Sitpn.transs) /\
             (Sitpn.s_intervals ?sitpn t) <> None <->
             In t (fst (split ?s.(Sitpn.d_intervals))))
      |- _ ] => clear H
  | _ => idtac "No hypothesis of the form 't ∈ Ti ⇔ I(t) ≠ ∅' found"
  end;
  match goal with
  | [ H: NoDup (fst (split (Sitpn.d_intervals ?s))) |- _ ] => clear H
  | _ => idtac "No hypothesis of the form 'NoDup (fst (split (d_intervals s)))' found"
  end;
  match goal with
  | [ H: (forall (t : Trans),
             In t ?sitpn.(Sitpn.transs) /\
             (Sitpn.s_intervals ?sitpn t) <> None <->
             In t (fst (split ?s.(Sitpn.reset))))
      |- _ ] => clear H
  | _ => idtac "No hypothesis of the form 't ∈ Ti ⇔ t ∈ reset' found"
  end;
  match goal with
  | [ H: NoDup (fst (split (Sitpn.reset ?s))) |- _ ] => clear H
  | _ => idtac "No hypothesis of the form 'NoDup (fst (split (reset s)))' found"
  end;
  match goal with
  | [ H: (Sitpn.conditions ?sitpn) = fst (split (Sitpn.cond_values ?s)) |- _ ] => clear H
  | _ => idtac "No hypothesis of the form 'C = (fst (split (cond_values s)))' found"
  end;
  match goal with
  | [ H: (Sitpn.actions ?sitpn) = fst (split (Sitpn.exec_a ?s)) |- _ ] => clear H
  | _ => idtac "No hypothesis of the form 'A = (fst (split (exec_a s)))' found"
  end;
  match goal with
  | [ H: (Sitpn.functions ?sitpn) = fst (split (Sitpn.exec_f ?s)) |- _ ] => clear H
  | _ => idtac "No hypothesis of the form 'A = (fst (split (exec_f s)))' found"
  end.

Ltac explode_well_defined_sitpn_state Hwell_def_state :=
  lazymatch Hwell_def_state with
  | ?H : IsWellDefinedSitpnState _ _  =>
    assert (H' := H); 
    unfold IsWellDefinedSitpnState in H;
    decompose [and] H;
    rename_well_defined_sitpn_state;
    clear H;
    rename H' into Hwell_def_state
  | _ => fail "Hwell_def_state is not of the form IsWellDefinedSitpnState"
  end.

(** Deduces In t (transs sitpn) from the context:
    
    - IsDecListCons (t :: tl) pgroup
    - In pgroup (priority_groups sitpn) 
    - IsWellDefinedSitpn sitpn

    Produces a hypothesis Hin_t_transs: In t (transs sitpn) in the context. *)

Ltac deduce_in_transs :=
  lazymatch goal with
  | [H: IsDecListCons (?t :: ?tl) ?pgroup |- _ ] =>
    assert (Hin_t_pgroup := H);
    apply is_dec_list_cons_incl in Hin_t_pgroup;
    specialize (Hin_t_pgroup t (in_eq t tl));
    lazymatch goal with
    | [Hin_pg_pgs: In pgroup (priority_groups ?sitpn) |- _ ] =>
      specialize (in_concat t pgroup (priority_groups sitpn) Hin_t_pgroup Hin_pg_pgs);
      intros Hin_t_transs;
      lazymatch goal with
      | [Hwd_sitpn: IsWellDefinedSitpn sitpn |- _] =>
        explode_well_defined_sitpn;
        unfold NoUnknownInPriorityGroups in *;
        lazymatch goal with
        | [Hno_unk_pgroups: Permutation _ _ |- _] =>
          rewrite <- Hno_unk_pgroups in Hin_t_transs;
          clear_well_defined_sitpn;
          clear Hno_unk_pgroups
        | _ => fail "No hypothesis of the form 'Permutation _ _' found"
        end
      | _ => fail "No hypothesis of the form IsWellDefinedSitpn ?sitpn found"
      end
    | _ => fail "No hypothesis of the form 'In ?pgroup  (priority_groups ?sitpn)' found"
    end
  | _ => fail "No hypothesis of the form 'IsDecListCons (?t :: ?tl) ?pgroup' found" 
  end.

(** Deduces NoDup (t :: tl) from the context:
    
    - IsDecListCons (t :: tl) pgroup
    - In pgroup (priority_groups sitpn) 
    - IsWellDefinedSitpn sitpn

    Produces a hypothesis Hnodup_ttail: NoDup (t :: tl) in the context. *)

Ltac deduce_nodup_in_dec_pgroup :=          
  lazymatch goal with
  |  [ Hwd: IsWellDefinedSitpn ?sitpn,
            His_dec: IsDecListCons (?t :: ?tail) ?pgroup,
            Hin_pg_pgs: In ?pgroup (priority_groups ?sitpn)               
       |- _ ] =>
     assert (Hnodup_pg := Hin_pg_pgs);
     assert (Hnodup_ttail' := His_dec);
     explode_well_defined_sitpn;
     lazymatch goal with
     | [ Hno_inter: NoIntersectInPriorityGroups sitpn |- _ ] =>
       apply (nodup_concat_gen (priority_groups sitpn) Hno_inter pgroup) in Hnodup_pg;
       apply (nodup_is_dec_list_cons Hnodup_pg) in Hnodup_ttail';
       assert (Hnodup_ttail := Hnodup_ttail');

       clear_well_defined_sitpn;
       clear Hno_inter;
       clear Hnodup_pg;
       clear Hnodup_ttail'
     | _ => fail "No hypothesis of the form 'NoIntersectInPriorityGroups ?sitpn' found"
     end
  | _ => fail "Mandatory hypotheses are missing in the context:
               IsWellDefinedSitpn ?sitpn or IsDecListCons (?t :: ?tl) ?pgroup or In ?pgroup (priority_groups ?sitpn)"
  end.

(** Deduces NoDup (fst (split (marking s))) from context: 

    - IsWellDefinedSitpn sitpn
    - IsWellDefinedSitpnState sitpn s

 *)

Ltac deduce_nodup_state_marking :=
  lazymatch goal with
  |  [ Hwd: IsWellDefinedSitpn ?sitpn,
       Hwd_state: IsWellDefinedSitpnState ?sitpn ?s
       |- _ ] =>
     explode_well_defined_sitpn;
     explode_well_defined_sitpn_state Hwd_state;
     
     lazymatch goal with
     | [ Hnodup_places: NoDupPlaces _, Hwf_state_marking: (places _) = fst (split (marking _)) |- _ ] =>
       unfold NoDupPlaces in Hnodup_places;
       rewrite Hwf_state_marking in Hnodup_places;
       assert (Hnodup_fs_ms := Hnodup_places);
       clear_well_defined_sitpn;
       clear_well_defined_sitpn_state;
       clear Hnodup_places
     | _ => fail "No Hypotheses of the form 'NoDupPlaces' or '(places _) = fst (split _)'"
     end
  | _ => fail "No Hypotheses of the form 'IsWellDefinedSitpn' or 'IsWellDefinedSitpnState'"
  end.
