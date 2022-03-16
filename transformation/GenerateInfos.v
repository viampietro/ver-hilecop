(** * Generation of informations regarding the elements of an SITPN model *)

Require Import common.CoqLib.
Require Import common.GlobalFacts.
Require Import common.ListPlus.
Require Import sitpn.Sitpn.
Require Import sitpn.SitpnTypes.

Require Import common.ListDep.
Require Import common.GlobalTypes.
Require Import String.
Require Import common.StateAndErrorMonad.
Require Import common.ListMonad.
Require Import transformation.Sitpn2HVhdlTypes.
Require Import FunInd.

Section GenSitpnInfos.

  Variable sitpn : Sitpn.

  (* The instantiated state type is [SitpnInfo sitpn] *)

  Definition CompileTimeState := @Mon (Sitpn2HVhdlState sitpn).

  (** ** Informations about transitions. *)

  Section TransitionInfos.

    (** Returns the list of input places of transition [t].

        Correctness: Correct iff all input places of [t] are in the
        returned list, and the returned list has no duplicates. *)

    Definition get_inputs_of_t (t : T sitpn) : CompileTimeState (list (P sitpn)) :=    
      (* Tests if a place is an input of t. *)
      let is_input_of_t := (fun p => if (pre p t) then true else false) in
      do Plist <- get_lofPs; Ret (filter is_input_of_t Plist).

    (** Returns the list of output places of transition [t].

        Correctness: Correct iff all output places of [p] are in the
        returned list, and the returned list has no duplicates.

        Does not raise an error if the returned list is nil because it
        doesn't mean that [t] is an isolated transition; however [t] is a
        "source" transition (without input). *)

    Definition get_outputs_of_t (t : T sitpn) : CompileTimeState (list (P sitpn)) :=    
      (* Tests if a place is an input of t. *)
      let is_output_of_t := (fun p => if (post t p) then true else false) in
      do Plist <- get_lofPs; Ret (filter is_output_of_t Plist).

    (** Returns the list of conditions associated to transition [t].
    
    Correctness: Correct iff all conditions associated to [t] are in the
    returned list, and the returned has no duplicates.  *)

    Definition get_conds_of_t (t : T sitpn) : CompileTimeState (list (C sitpn)) :=
      (* Tests if a condition is associated to t. *)
      let is_cond_of_t := (fun c => (match has_C t c with one | mone => true | zero => false end)) in
      do Clist <- get_lofCs; Ret (filter is_cond_of_t Clist).
    
    (** Computes the information about transition t, and adds it to
        the current state. *)

    Definition add_tinfo (t : T sitpn) : CompileTimeState unit :=
      do inputs_of_t <- get_inputs_of_t t;
      do outputs_of_t <- get_outputs_of_t t;
      if (inputs_of_t ++ outputs_of_t)%list then
        Err ("add_tinfo: Transition " ++ $$t ++ " is an isolated transition.")
      else
        do conds_of_t <- get_conds_of_t t;
        set_tinfo (t, MkTransInfo _ inputs_of_t conds_of_t).

    (** Calls the function [add_tinfo] for each transition of [sitpn], thus
        modifying the current state. *)

    Definition generate_trans_infos : CompileTimeState unit :=
      do Tlist <- get_lofTs; iter add_tinfo Tlist.

  End TransitionInfos.

  (** ** Informations about places. *)

  Section PlaceInfos.
    
    (** Returns a triplet of lists [(tin, tc, tout)] where [tin] is
        the list of input transitions of [p], [tc] is the list of
        output transitions of [p] that are in conflict, and [tout] is
        the list of output transitions of [p] that are not in
        conflict.

        Correctness: Correct iff all input transitions of [p] are in
        [tin], and [tin] has no duplicate, and all output transitions
        of [p] are in [tc] and [tout], and [tout] and [tc] has no
        duplicate.  *)

    Definition get_neighbors_of_p (p : P sitpn) : CompileTimeState (list (T sitpn) * list (T sitpn) * list (T sitpn)) :=
      
      (* Adds the transition t to the list of input and/or output
         transitions of p. The list of output transitions of p is
         divided between the transitions in conflict [tc], and
         transitions without conflict [tout]. [tc] and [tout] are
         disjoint lists. *)
      
      let get_neighbor_of_p :=
          (fun (tin_tc_tout : (list (T sitpn) * list (T sitpn) * list (T sitpn))) t =>
             let '(tin, tc, tout) := tin_tc_tout in
             match post t p with
             | Some _ =>
               match pre p t with
               | Some (basic, _) => ((tin ++ [t])%list, (tc ++ [t])%list, tout)
               | Some ((inhibitor|test), _) => ((tin ++ [t])%list, tc, (tout ++ [t])%list)
               | None => ((tin ++ [t])%list, tc, tout)
               end
             | None =>
               match pre p t with
               | Some (basic, _) => (tin, (tc ++ [t])%list, tout)
               | Some ((inhibitor|test), _) => (tin, tc, (tout ++ [t])%list)
               | None => (tin, tc, tout)
               end
             end) in

      (* Iterates over the list of transitions, and builds the couple of
         lists (tinputs, touputs) of p along the way by applying
         function [is_neighbor_of_p].  *)
      do Tlist <- get_lofTs;
      match List.fold_left get_neighbor_of_p Tlist (nil, nil, nil) with
      | (nil, nil, nil) => Err ("get_neighbors_of_p: Place " ++ $$p ++ " is an isolated place.")
      | tin_tc_tout => Ret tin_tc_tout 
      end.

    (** Returns the set of actions associated with place [p]. *)

    Definition get_acts_of_p (p : P sitpn) : CompileTimeState (list (A sitpn)) :=
      
      (* Filters the list of actions of [sitpn]. Keeps only the
         actions associated with place [p].  *)
      do Alist <- get_lofAs; Ret (filter (fun a => has_A p a) Alist).
    
    (** Functions to solve conflicts in a given conflict group, i.e, a
        set of transitions. *)
    
    Section ConflictResolution.

      (** Returns [true] if there exists a condition [c] in [conds]
          s.t. [c] is associated [t] and [not c] to [t'], or the other
          way around. Returns [false] otherwise.  *)
      
      Definition exists_ccond (t t' : T sitpn) (conds : list (C sitpn)) : bool :=
        let check_ccond_of_tt' := (fun c => match has_C t c, has_C t' c with
                                              one, mone | mone, one => true
                                            | _, _ => false
                                            end) in
        if (List.find check_ccond_of_tt' conds) then true else false.
      
      (** Returns [true] if there exists a condition [c] in the
          intersection of the list of conditions of [t] and [t'] that
          verify [C(c,t) = 1 and C(c,t') = -1] or [C(c,t) = -1 and
          C(c,t') = 1] (i.e, complementary conditions are associated
          to [t] and [t']). *)

      Definition mutex_by_cconds (t t' : T sitpn) : CompileTimeState bool :=
        do tinfo <- get_tinfo t;
        do tinfo' <- get_tinfo t';
        Ret (exists_ccond t t' (inter P1SigEq (P1SigEqdec Nat.eq_dec) (conds tinfo) (conds tinfo'))).      
      
      (** Returns [true] if there exists a place [p] in [places]
          s.t. there exists a [basic] or [test] arc between [p] and
          [t], and an [inhib] arc between [p] and [t'], or the other
          way around. If such arcs exist, the weight of the inhib arc
          must be lower or equal to the weight of the basic or test
          arc. Returns [false] otherwise. *)

      Definition exists_inhib (t t' : T sitpn) (pls : list (P sitpn)) : bool :=
        let check_inhib_mutex :=
            (fun p => match pre p t, pre p t' with
                      | Some ((basic|test), ω), Some (inhibitor, ω')
                      | Some (inhibitor, ω'), Some ((basic|test), ω) =>
                        ω' <=? ω
                      | _, _ => false
                      end)
        in if (List.find check_inhib_mutex pls) then true else false.

      (** Returns [true] if there exists a place [p] in the
         intersection of the list of input places of [t] and [t']
         that mutually exclude [t] and [t'] by mean of an inhibitor
         arc. *)

      Definition mutex_by_inhib (t t' : T sitpn) : CompileTimeState bool :=
        do tinfo <- get_tinfo t;
        do tinfo' <- get_tinfo t';
        Ret (exists_inhib t t' (inter P1SigEq (P1SigEqdec Nat.eq_dec) (pinputs tinfo) (pinputs tinfo'))).

      (** Returns [true] is there exists no means of mutual exclusion
         between transitions [t] and [t']. Returns [false]
         otherwise.  *)
      
      Definition not_exists_mutex (t t' : T sitpn) : CompileTimeState bool :=
        do mbyinhib <- mutex_by_inhib t t';
        do mbycconds <- mutex_by_cconds t t';
        Ret (negb (mbyinhib || mbycconds)).

      (** Returns [true] if there exists at least one mean of mutual
         exclusion between [t] and all transitions in [cgoft]
         (conflict group of [t]). Returns [false] otherwise.  *)

      Definition all_conflicts_of_t_solved (t : T sitpn) (cgoft : list (T sitpn)) : CompileTimeState bool :=
        do res <- find (not_exists_mutex t) cgoft;
        if res then Ret false else Ret true.

      (** Returns [true] if all conflicts in the conflict group [cg]
          are solved by means of mutual exclusion, or if the conflict
          group is empty and has only one element. Returns [false]
          otherwise.  *)
      
      Definition all_conflicts_solved_by_mutex (cg : list (T sitpn)) : CompileTimeState bool :=
        do bl <- ListMonad.fold_left
                   (fun '(bprod, l) t => do b <- all_conflicts_of_t_solved t (tl l); Ret (bprod && b, (tl l)))
                   cg (true, cg);
        Ret (fst bl).

      Fixpoint all_conflicts_solved_by_mutex_without_foldl (cg : list (T sitpn)) {struct cg} : CompileTimeState bool :=
        match cg with
        | nil => Ret true
        | t :: tl =>
            (* If all conflicts of [t] are solved, then we can safely
           withdraw it from the conflict group. Indeed, it means
           that all the transitions of the tail are not in conflict
           with [t]. Therefore, [t] is not needed anymore. *)
            do b <- all_conflicts_of_t_solved t tl;
            if b then all_conflicts_solved_by_mutex_without_foldl tl else Ret false
        end.      
      
      (** Injects transition [t] in the list [stranss] depending on
          the level of priority of [t] compared to the elements of the
          list [stranss].
    
        Returns the new priority-sorted list where [c] has been
        injected.
      
        Correctness hypotheses: (1) ~In t stranss, (2) NoDup stranss,
        (3) Elements of stranss are ordered by decreasing level of
        priority.

        Correct iff the returned list has no duplicate and its elements
        are ordered by decreasing level of priority. *)

      Fixpoint inject_t (t : T sitpn) (stranss : list (T sitpn)) {struct stranss} :
        CompileTimeState (list (T sitpn)) :=
        match stranss with
        (* If the list of priority-ordered transitions is empty, then
           returns a singleton list where [t] is the element with the
           highest priority. *)
        | [] => Ret [t]

        (* If there is a head element, compares the head element with t
           priority-wise. *)
        | x :: tl =>
            (* If [t] has a higher priority than [x], then puts [t] as the
               head element of [stranss], and returns the list. *)
            if pr_dec t x then Ret (t :: stranss)
            (* If [x] has a higher priority than [t], then tries to
               inject [t] in the list's tail.  *)
            else
                if pr_dec x t then
                  do stranss' <- inject_t t tl; Ret (x :: stranss')
                else
                  (* If [x ⊁ t] and [t ⊁ x] then error because the two
                     elements not comparable, and the priority
                     relation is not a total order over [t ∪ stranss]. *)
                  Err ("inject_t: transitions "
                         ++ $$t ++ " and "
                         ++ $$x ++ " are not comparable with the priority relation.")
        end.
      
      Functional Scheme inject_t_ind := Induction for inject_t Sort Prop.
      
      (** Takes a list of transitions [cgroup] (conflict group), and
          returns a new list of transitions where the elements of the
          confict group are ordered by level of firing priority.

          Raises an error if the priority relation is not a strict
          total order over the elements of [cgroup].  *)

      Definition sort_by_priority (cgroup : list (T sitpn)) :
        CompileTimeState (list (T sitpn)) :=
        (* [scgroup] stands for sorted conflict group *)
        fold_left (fun scgroup t => inject_t t scgroup) cgroup [].

    End ConflictResolution.

    (** Returns a PlaceInfo structure containing the information related
      to place [p], a place of [sitpn].

      Error cases :
      
      - p is an isolated place, i.e it doesn't have neither input nor
        output transitions.

      - the priority relation is not a strict total order over the
        output transitions of t. 
     *)

    Definition add_pinfo (p : P sitpn) : CompileTimeState unit :=

      (* Gets the input, conflicting, and output transitions of place p. 
         Error: p is an isolated place.
       *)
      do tin_tc_tout <- get_neighbors_of_p p;
      
      (* Gets the set of actions associated with [p]. *)
      do acts_of_p <- get_acts_of_p p;

      (* If all conflicts in [tc] are not solved by means of mutual
         exclusion, then transitions in [tc] must be sorted out by
         increasing order of priority before setting the PlaceInfo
         structure for place [p].
         
         Error: the priority relation is not a strict total order over
         the output transitions of p.  *)
      let '(tin, tc, tout) := tin_tc_tout in
      do b <- all_conflicts_solved_by_mutex tc;
      if b then
        set_pinfo (p, MkPlaceInfo _ tin [] (tc ++ tout) acts_of_p)
      else
        do stc <- sort_by_priority tc;
        set_pinfo (p, MkPlaceInfo _ tin stc tout acts_of_p).
    
    (** Computes information for all p ∈ P, and adds the infos to the
        current state. *)
    
    Definition generate_place_infos : CompileTimeState unit :=
      do Plist <- get_lofPs; iter add_pinfo Plist.
    
  End PlaceInfos.
  
  (** ** Informations about conditions, actions and functions *)

  Section InterpretationInfos.

    (** Returns the list of transitions associated to condition [c]. *)

    Definition get_transs_of_c (c : C sitpn) : CompileTimeState (list (T sitpn)) :=
      let is_trans_of_c := (fun t => (match has_C t c with one | mone => true | zero => false end)) in
      do Tlist <- get_lofTs; Ret (filter is_trans_of_c Tlist).

    (** Computes the information about transition c, and adds it to
        the current state. *)

    Definition add_cinfo (c : C sitpn) : CompileTimeState unit :=
      do transs_of_c <- get_transs_of_c c;
      set_cinfo (c, transs_of_c).

    (** Calls the function [add_cinfo] for each condition of [sitpn], thus
        modifying the current state. *)

    Definition generate_cond_infos : CompileTimeState unit :=
      do Clist <- get_lofCs; iter add_cinfo Clist.
    
    (** Returns the list of transitions associated to function [f]. *)

    Definition get_transs_of_f (f : F sitpn) : CompileTimeState (list (T sitpn)) :=
      do Tlist <- get_lofTs; Ret (filter (fun t => has_F t f) Tlist).

    (** Computes the information about function f, and adds it to
        the current state. *)

    Definition add_finfo (f : F sitpn) : CompileTimeState unit :=
      do transs_of_f <- get_transs_of_f f;
      set_finfo (f, transs_of_f).
    
    (** Calls the function [add_finfo] for each function of [sitpn];
        thus modifying the current state. *)
    
    Definition generate_fun_infos : CompileTimeState unit :=
      do Flist <- get_lofFs; iter add_finfo Flist.
    
    (** Returns the list of places associated to action [a]. *)

    Definition get_places_of_a (a : A sitpn) : CompileTimeState (list (P sitpn)) :=
      do Plist <- get_lofPs; Ret (filter (fun p => has_A p a) Plist).    

    (** Computes the information about action a, and adds it to the
        current state. *)

    Definition add_ainfo (a : A sitpn) : CompileTimeState unit :=
      do places_of_a <- get_places_of_a a;
      set_ainfo (a, places_of_a).
    
    (** Calls the function [add_ainfo] for each action of
      [sitpn], thus modifying the current state. *)
    
    Definition generate_action_infos : CompileTimeState unit :=
      do Alist <- get_lofAs; iter add_ainfo Alist.
    
  End InterpretationInfos.

  (** ** Well-definition of an [Sitpn] *)

  Section CheckWellDefinedSitpn.

    (** Mostly checks that the priority relation is a strict
        order. However, now that the property is a part of the Sitpn
        record type, the check_wd_sitpn is no longer useful. Will
        probably delete it in versions to come. *)
    
    (** Assuming that x ≻ y, checks that x ≻ z if y ≻ z.  Returns an
        error if x ≻ y and y ≻ z but x ⊁ z.  *)
    
    Let check_trans (x y z : T sitpn) : CompileTimeState unit :=
      match pr_dec y z, pr_dec x z with
      | left _, right _ => Err ("check_trans: priority relation is not transitive. "
                                  ++ $$x ++ " ≻ " ++ $$y
                                  ++ " and " ++ $$y ++ " ≻ " ++ $$z
                                  ++ " but " ++ $$x ++ " ⊁ " ++ $$z)
      | _, _ => Ret tt
      end.

    (** Assuming that [x ≻ y], checks that if [y ≻ z] then [x ≻ z]
        holds for each [z ∈ trs].  *)
    
    Definition iter_xy_check_trans (x y : T sitpn) (trs : list (T sitpn)) :
      CompileTimeState unit :=
      iter (check_trans x y) trs.

    (** For each transition [y] in [trs], if [x ≻ y] then calls
        [iter_xy_check_trans] on [x], [y] and [trs∖{y}].  *)
    
    Definition foreach_x_check_trans (x : T sitpn) (trs : list (T sitpn)) :
      CompileTimeState unit :=
      let f := fun y trs' =>
                 if pr_dec x y
                 then iter_xy_check_trans x y trs'
                 else Ret tt
      in foreach f trs.

    (** Checks that the priority relation is transitive; returns an
        error if not. *)
    
    Definition check_pr_is_trans :=
      do Tlist <- get_lofTs; foreach foreach_x_check_trans Tlist.

    (** Checks that the priority relation is irreflexive; returns
        an error if not. *)
    
    Definition check_pr_is_irrefl : CompileTimeState unit :=
      let check_irrefl :=
          (fun t =>
             if pr_dec t t
             then Err ("pr_rel_is_strict_order: priority relation is reflexive for transition "
                         ++ $$t ++ ".")
             else Ret tt) in
      do Tlist <- get_lofTs; iter check_irrefl Tlist.

    (** Checks that the priority relation is a strict order, i.e,
        irreflexive and transitive. *)
    
    Definition pr_rel_is_strict_order : CompileTimeState unit :=
      do _ <- check_pr_is_irrefl; check_pr_is_trans.
    
    (** Returns an error if the list of places or transitions of
        [sitpn] are empty, or if the priority relation is not a strict
        order.
        
        This is a partial checking of the well-definition of an SITPN
        model. The other properties of the well-definition will
        checked all along the transformation (e.g. the SITPN model is
        conflict-free during the generation of place infos, etc.). *)
    
    Definition check_wd_sitpn : CompileTimeState unit :=
      (* Raises an error if sitpn has an empty set of places or transitions. *)
      if (places sitpn) then Err ("Found an empty set of places.")
      else
        if (transitions sitpn) then Err ("Found an empty set of transitions.")
        else pr_rel_is_strict_order.

    (** *** Well-definition of an [Sitpn] with nodup lists *)
    
    Definition Innodup2In {A}
               (decA : forall x y : A, {x = y} + {x <> y})
               {l : list A}
               (a : { a : A | In a (nodup decA l) }) : {a : A | In a l}.
      specialize (proj2_sig a) as pf;
        rewrite (nodup_In decA) in pf;
        exact (exist _ (proj1_sig a) pf). 
    Defined.

    Definition pre2nodup (pre : P sitpn -> T sitpn -> option (ArcT * natstar)) := 
      fun p t => pre (Innodup2In Nat.eq_dec p) (Innodup2In Nat.eq_dec t).

    Definition post2nodup (post : T sitpn -> P sitpn -> option natstar) :=
      fun t p => post (Innodup2In Nat.eq_dec t) (Innodup2In Nat.eq_dec p).

    Definition M02nodup (M0 : P sitpn -> nat) :=
      fun p => M0 (Innodup2In Nat.eq_dec p).

    Definition Is2nodup (Is : T sitpn -> option TimeInterval) :=
      fun t => Is (Innodup2In Nat.eq_dec t).

    Definition hasCtonodup (has_C : T sitpn -> C sitpn -> MOneZeroOne) :=
      fun t c => has_C (Innodup2In Nat.eq_dec t) (Innodup2In Nat.eq_dec c).

    Definition hasAtonodup (has_A : P sitpn -> A sitpn -> bool) :=
      fun p a => has_A (Innodup2In Nat.eq_dec p) (Innodup2In Nat.eq_dec a).

    Definition hasFtonodup (has_F : T sitpn -> F sitpn -> bool) :=
      fun t f => has_F (Innodup2In Nat.eq_dec t) (Innodup2In Nat.eq_dec f).

    Definition pr2nodup (pr : T sitpn -> T sitpn -> Prop) :=
      fun x y => pr (Innodup2In Nat.eq_dec x) (Innodup2In Nat.eq_dec y).
    
    (* Definition check_wd_sitpn_nodup : CompileTimeState Sitpn := *)
    (*   (* Raises an error if sitpn has an empty set of places or transitions. *) *)
    (*   if (places sitpn) then Err ("Found an empty set of places.") *)
    (*   else *)
    (*     if (transitions sitpn) then Err ("Found an empty set of transitions.") *)
    (*     else *)
    (*       (* Builds a new [sitpn] where the list of places, transitions, *)
    (*          actions, functions and conditions have no duplicate *)
    (*          element. *) *)
    (*       let sitpn_nodup := *)
    (*           BuildSitpn (nodup Nat.eq_dec (places sitpn)) *)
    (*                      (nodup Nat.eq_dec (transitions sitpn)) *)
    (*                      (pre2nodup (@pre sitpn)) (post2nodup (@post sitpn)) *)
    (*                      (M02nodup (@M0 sitpn)) (Is2nodup (@Is sitpn)) *)
    (*                      (nodup Nat.eq_dec (conditions sitpn)) *)
    (*                      (nodup Nat.eq_dec (actions sitpn)) *)
    (*                      (nodup Nat.eq_dec (functions sitpn)) *)
    (*                      (hasCtonodup (@has_C sitpn)) *)
    (*                      (hasAtonodup (@has_A sitpn)) *)
    (*                      (hasFtonodup (@has_F sitpn)) *)
    (*                      (pr2nodup (@pr sitpn)) *)
    (*       in *)
    (*       (* do _ <- pr_rel_is_strict_order sitpn_nodup; *) *)
    (*       Ret sitpn_nodup. *)
    
  End CheckWellDefinedSitpn.
    
End GenSitpnInfos.

(** ** Informations about an [Sitpn] *)

(** Returns an SitpnInfo instance computed from [sitpn]. *)

Definition generate_sitpn_infos (sitpn : Sitpn) :=

  (* Turns the list of places, transitions, conditions, actions and
     functions of [sitpn], into dependently-typed lists, and sets them
     in the compile-time state. *)
  do Plist <- tmap (fun p s => Ret p s) (places sitpn) nat_to_P;
  do Tlist <- tmap (fun t s => Ret t s) (transitions sitpn) nat_to_T;
  do Clist <- tmap (fun c s => Ret c s) (conditions sitpn) nat_to_C;
  do Alist <- tmap (fun a s => Ret a s) (actions sitpn) nat_to_A;
  do Flist <- tmap (fun f s => Ret f s) (functions sitpn) nat_to_F;
  do _ <- set_lofPs Plist;
  do _ <- set_lofTs Tlist;
  do _ <- set_lofCs Clist;
  do _ <- set_lofAs Alist;
  do _ <- set_lofFs Flist;
  
  (* Call to [generate_trans_infos] must precede the call to
     [generate_place_infos] because the latter uses transition
     informations.  *)
  (* do _ <- check_wd_sitpn sitpn; *)
  do _ <- generate_trans_infos sitpn;
  do _ <- generate_place_infos sitpn;
  do _ <- generate_cond_infos sitpn; 
  do _ <- generate_action_infos sitpn;
  generate_fun_infos sitpn.

