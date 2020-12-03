(** * Types and functions used by the generateInfo function. *)

Require Import common.Coqlib.
Require Import common.GlobalFacts.
Require Import common.ListsPlus.
Require Import dp.Sitpn.
Require Import dp.SitpnTypes.
Require Import dp.SitpnFacts.
Require Import ListsDep.
Require Import InfosTypes.
Require Import GlobalTypes.
Require Import String.
Require Import StateAndErrorMonad.

Local Open Scope string_scope.

Import ErrMonadNotations.

Section GenSitpnInfos.

  Variable sitpn : Sitpn.

  (* Proof of decidability for the priority relation of [sitpn] *)
  
  Variable decpr : forall x y : T sitpn, {x >~ y} + {~x >~ y}.
  
  (* The instantiated state type is [SitpnInfo sitpn] *)

  Definition GenInfosMon := @Mon (SitpnInfo sitpn).

  (** ** Informations about transitions. *)

  Section TransitionInfos.

    (** Returns the list of input places of transition [t].

        Correctness: Correct iff all input places of [p] are in the
        returned list, and the returned has no duplicates.

        Does not raise an error if the returned list is nil because it
        doesn't mean that [t] is an isolated transition; however [t] is a
        "source" transition (without input).
    
     *)

    Definition get_inputs_of_t (t : T sitpn) : GenInfosMon (list (P sitpn)) :=    
      (* Tests if a place is an input of t. *)
      let is_input_of_t := (fun p => if (pre p t) then true else false) in
      Ret (tfilter is_input_of_t (P2List sitpn) nat_to_P).

    (** Returns the list of conditions associated to transition [t].
    
    Correctness: Correct iff all conditions associated to [t] are in the
    returned list, and the returned has no duplicates.  *)

    Definition get_conds_of_t (t : T sitpn) : GenInfosMon (list (C sitpn)) :=
      (* Tests if a condition is associated to t. *)
      let is_cond_of_t := (fun c => (match has_C t c with one | mone => true | zero => false end)) in
      Ret (tfilter is_cond_of_t (C2List sitpn) nat_to_C).
    
    (** Computes the information about transition t, and adds it to
        the current state. *)

    Definition add_tinfo (t : T sitpn) : GenInfosMon unit :=
      do inputs_of_t <- get_inputs_of_t t;
      do conds_of_t <- get_conds_of_t t;
      do sitpninfo <- Get;
      Put (set_tinfo (t, MkTransInfo _ inputs_of_t conds_of_t) sitpninfo).

    (** Calls the function [add_tinfo] for each transition of [sitpn], thus
        modifying the current state. *)

    Definition generate_trans_infos : GenInfosMon unit :=
      titer add_tinfo (T2List sitpn) nat_to_T.
    
  End TransitionInfos.
  
  (** ** Informations about places. *)

  Section PlaceInfos.
    
    (** Returns a couple of lists [(i, o)] where [i] is the list of
        input transitions of [p], and [o] is the list of output
        transitions of [p].

        Correctness: Correct iff all input transitions of [p] are in
        [i], and [i] has no duplicate, and all output transitions of [p]
        are in [o] and [o] has no duplicate.  *)

    Definition get_neighbors_of_p (p : P sitpn) : GenInfosMon (list (T sitpn) * list (T sitpn) * list (T sitpn)) :=
      
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
         function is_neighbor_of_p.  *)
      match tfold_left get_neighbor_of_p (T2List sitpn) (nil, nil, nil) nat_to_T with
      | (nil, nil, nil) => Err ("Place " ++ $$p ++ " is an isolated place.")
      | tin_tc_tout => Ret tin_tc_tout 
      end.

    (** Functions to solve conflicts in a given conflict group, i.e, a
        set of transitions. *)
    
    Section ConflictResolution.

      (** Returns [true] if transition [t] and [t'] are time transitions
          (i.e, they own a time interval) and if their time intervals
          are disjoint (no overlapping). Returns [false], otherwise. *)

      Definition mutex_by_disjoint_itval (t t' : T sitpn) : GenInfosMon bool :=
        match Is t, Is t' with
        | Some i, Some i' => if dec_nooverlap i i' then Ret true else Ret false
        | _, _ => Ret false
        end.

      (*  *)
      
      Definition exists_ccond (t t' : T sitpn) (cconds : list (C sitpn)) : bool :=
        let check_ccond_of_tt' := (fun c => match has_C t c, has_C t' c with
                                              one, mone | mone, one => true
                                            | _, _ => false
                                            end) in
        if (find check_ccond_of_tt' cconds) then true else false.
      
      (** Returns [true] if there exists a condition [c] in the
          intersection of the list of conditions of [t] and [t'] that
          verify [C(c,t) = 1 and C(c,t') = -1] or [C(c,t) = -1 and
          C(c,t') = 1] (i.e, complementary conditions are associated
          to [t] and [t']). *)

      Definition mutex_by_cconds (t t' : T sitpn) : GenInfosMon bool :=
        do sitpninfo <- Get;
        match get_tinfo sitpn t sitpninfo, get_tinfo sitpn t' sitpninfo with
        | Some tinfo, Some tinfo' => Ret (exists_ccond t t' (inter seq (seqdec Nat.eq_dec) (conds tinfo) (conds tinfo')))
        | _, _ => Err ("No information on transition " ++ $$t ++ " or " ++ $$t')
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
        GenInfosMon (list (T sitpn)) :=
        match stranss with
        (* If the list of priority-ordered transitions is empty, then
       returns a singleton list where t is the element with the highest
       priority. *)
        | [] => Ret [t]

        (* If there is a head element, compares the head element with t
           priority-wise. *)
        | x :: tl =>

          (* If t and x are the same, then t has already been injected in
       stranss, then stranss is returned. That case does not happen
       given a proof of [~In t stranss], that is, t is not among 
       the first elements of stranss.

       Otherwise, checks if t has a higher firing priority than x. *)
          if Teqdec t x then Ret stranss
          else
            (* If t is the element with the highest priority, then puts it
           as the head element of stranss, and returns the list.
         
         Otherwise, checks if x has a higher priority than t.  *)
            if decpr t x then Ret (t :: stranss)
            else
              (* If x has a higher priority than t, then tries to inject t
               in the list's tail.  *)
              if decpr x t then
                do stranss' <- inject_t t tl; Ret (x :: stranss')
              else
                (* Error case: t and x are not comparable, the priority
                 relation is ill-formed (i.e, not a total order on
                 group of transitions with a input place in
                 common). *)
                Err ("Transitions " ++ $$t ++ " and " ++ $$x ++ " are not comparable with the priority relation.")
        end.

      (** Injects all transitions of the [transs] list in the list [stranss]
      that contains transitions sorted by level of firing priority.  *)

      Fixpoint sort_by_priority_aux
               (cgroup : list (T sitpn))
               (scgroup : list (T sitpn)) {struct cgroup} :
        GenInfosMon (list (T sitpn)) :=
        match cgroup with
        | [] => Ret scgroup
        | t :: tl =>
          do scgroup' <- inject_t t scgroup;
          sort_by_priority_aux tl scgroup'
        end.

      (** Takes a list of transitions [cgroup] (conflict group), and
          returns a new list of transitions where the elements of the
          confict group are ordered by level of firing priority.

          Raises an error if no strict total ordering can be established
          in relation to the priority order.  *)

      Definition sort_by_priority (cgroup : list (T sitpn)) :
        GenInfosMon (list (T sitpn)) := sort_by_priority_aux cgroup [].

      
    End ConflictResolution.
    

    (** Returns a PlaceInfo structure containing the information related
      to place [p], a place of [sitpn].

      Error cases :
      
      - p is an isolated place, i.e it doesn't have neither input nor
        output transitions.

      - the priority relation is not a strict total order over the
        output transitions of t. 
     *)

    Definition add_pinfo (p : P sitpn) : GenInfosMon unit :=

      (* Gets the input and output transitions list of place p. 
       Error: p is an isolated place.
       *)
      do tin_tc_tout <- get_neighbors_of_p p;
      (* Sorts the output transitions of p by decreasing level of
         firing priority.
         
         Error: the priority relation is not a strict total order over
         the output transitions of p.  *)
      let '(tin, tc, tout) := tin_tc_tout in
      do stc <- sort_by_priority tc;
      do sitpninfo <- Get;
      Put (set_pinfo (p, MkPlaceInfo _ tin stc tout) sitpninfo).
    
    (** Computes information for all p ∈ P, and adds the infos to the
        current state. *)
    
    Definition generate_place_infos : GenInfosMon unit :=
      titer add_pinfo (P2List sitpn) nat_to_P.
    
  End PlaceInfos.

  (** ** Informations about conditions, actions and functions. *)

  Section InterpretationInfos.

    (** Returns the list of transitions associated to condition [c]. *)

    Definition get_transs_of_c (c : C sitpn) : GenInfosMon (list (T sitpn)) :=
      let is_trans_of_c := (fun t => (match has_C t c with one | mone => true | zero => false end)) in
      Ret (tfilter is_trans_of_c (T2List sitpn) nat_to_T).

    (** Computes the information about transition c, and adds it to
        the current state. *)

    Definition add_cinfo (c : C sitpn) : GenInfosMon unit :=
      do transs_of_c <- get_transs_of_c c;
      do sitpninfo <- Get;
      Put (set_cinfo (c, transs_of_c) sitpninfo).

    (** Calls the function [add_cinfo] for each condition of [sitpn], thus
        modifying the current state. *)

    Definition generate_cond_infos : GenInfosMon unit :=
      titer add_cinfo (C2List sitpn) nat_to_C.
    
    (** Returns the list of transitions associated to function [f]. *)

    Definition get_transs_of_f (f : F sitpn) : GenInfosMon (list (T sitpn)) :=
      Ret (tfilter (fun t => has_F t f) (T2List sitpn) nat_to_T).

    (** Computes the information about function f, and adds it to
        the current state. *)

    Definition add_finfo (f : F sitpn) : GenInfosMon unit :=
      do transs_of_f <- get_transs_of_f f;
      do sitpninfo <- Get;
      Put (set_finfo (f, transs_of_f) sitpninfo).
    
    (** Calls the function [add_finfo] for each function of [sitpn];
        thus modifying the current state. *)
    
    Definition generate_fun_infos : GenInfosMon unit :=
      titer add_finfo (F2List sitpn) nat_to_F.
    
    (** Returns the list of places associated to action [a]. *)

    Definition get_places_of_a (a : A sitpn) : GenInfosMon (list (P sitpn)) :=
      Ret (tfilter (fun p => has_A p a) (P2List sitpn) nat_to_P).    

    (** Computes the information about action a, and adds it to the
        current state. *)

    Definition add_ainfo (a : A sitpn) : GenInfosMon unit :=
      do places_of_a <- get_places_of_a a;
      do sitpninfo <- Get;
      Put (set_ainfo (a, places_of_a) sitpninfo).
    
    (** Calls the function [add_ainfo] for each action of
      [sitpn], thus modifying the current state. *)
    
    Definition generate_action_infos : GenInfosMon unit :=
      titer add_ainfo (A2List sitpn) nat_to_A.
    
  End InterpretationInfos.

  (** ** Informations about an Sitpn. *)

  (** Returns an SitpnInfo instance computed from [sitpn]. *)
  
  Definition generate_sitpn_infos : GenInfosMon (SitpnInfo sitpn) := 
  
    (* Raises an error if sitpn has an empty set of places or transitions. *)
    if (places sitpn) then Err "Found an empty set of places."
    else
      if (transitions sitpn) then Err "Found an empty set of transitions."
      else
        (* Otherwise, generates information about sitpn. *)
        
        do _ <- generate_place_infos;
        do _ <- generate_trans_infos;
        do _ <- generate_cond_infos; 
        do _ <- generate_action_infos;
        do _ <- generate_fun_infos;
        Get.
  
End GenSitpnInfos.

