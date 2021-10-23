(** * Utilitary functions for the HILECOP transformation function *)

Require Import common.CoqLib.
Require Import common.GlobalTypes.
Require Import common.ListPlus.
Require Import common.ListDep.
Require Import common.StateAndErrorMonad.

Require Import String.

Require Import sitpn.dp.Sitpn.
Require Import hvhdl.HVhdlCoreLib.
Require Import hvhdl.HVhdlHilecopLib.
Require Import sitpn2hvhdl.Sitpn2HVhdlTypes.

Section Sitpn2HVhdlUtils.

  Variable sitpn : Sitpn.
  
  (* Alias for the state-and-error monad instantiated with the
     compile-time state.  *)

  Definition CompileTimeState := @Mon (Sitpn2HVhdlState sitpn).

  (** Looks up and returns the maximal index [j] such that [id(j)] is
      in a formal part in the input port map [m].
      
      Returns [None] if there is no [j] such that [id(j)] is in a
      formal part in the input port map [m].

   *)
  
  Definition get_max_index_imap (m : inputmap) (id : ident) : CompileTimeState (option nat) :=
    let check_max_index :=
      fun currmax ai =>
        match ai with
        (* If we have found an association of the form (id'(j), _),
           then tests if [id = id']. *)
        | (associp_ (n_xid id' (e_nat j)) _) =>
            if id =? id' then
              match currmax with
              | None => Ret (Some j)
              | Some k => if k <? j then Ret (Some j) else Ret currmax
              end
            else Ret currmax
        | _ => Ret currmax
        end
    in ListMonad.fold_left check_max_index m None.

  (** Adds a new association [(id(i),e)] at the end of input port map
      [m] where [i] is computed based on the maximal index [j] such
      that [id(j)] is a formal part in [m]. *)
  
  Definition cassoc_imap (m : inputmap) (id : ident) (e : expr) :
    CompileTimeState inputmap :=
    do optj <- get_max_index_imap m id;
    match optj with
    | None => Ret (m ++ [(associp_ (n_xid id (e_nat 0)) e)])
    | Some j => Ret (m ++ [(associp_ (n_xid id (e_nat (j + 1))) e)])
    end.

  (** Looks up and returns the maximal index [j] such that [id(j)] is
      in a formal part in the output port map [m].
      
      Returns [None] if there is no [j] such that [id(j)] is in a
      formal part in the output port map [m].

   *)
  
  Definition get_max_index_omap (m : outputmap) (id : ident) : CompileTimeState (option nat) :=
    let check_max_index :=
      fun currmax ao =>
        match ao with
        (* If we have found an association of the form (id'(j), _);
           then, checks that [id = id'] *)
        | (assocop_idx id' (e_nat j) _) =>
            if id =? id' then
              match currmax with
              | None => Ret (Some j)
              | Some k => if k <? j then Ret (Some j) else Ret currmax
              end
            else Ret currmax
        | _ => Ret currmax
        end
    in ListMonad.fold_left check_max_index m None.

  (** Adds a new association [(id(i),e)] at the end of output port map
      [m] where [i] is computed based on the maximal index [j] such
      that [id(j)] is a formal part in [m]. *)
  
  Definition cassoc_omap (m : outputmap) (id : ident) (n : name) :
    CompileTimeState outputmap :=
    do optj <- get_max_index_omap m id;
    match optj with
    | None => Ret (m ++ [(assocop_idx id (e_nat 0) n)])
    | Some j => Ret (m ++ [(assocop_idx id (e_nat (j + 1)) n)])
    end.

  (** Returns [a] if [(assocop_simpl id a)] is in the output map [m].

      Raises an error if [id] is not a formal part in [m].
      
      As [id] is a simple identifier the actual part associated with
      [id] in [m] is of type [option name]. *)

  Fixpoint actual (id : ident) (m : outputmap) {struct m} : CompileTimeState (option name) :=
    match m with
    | nil => Err ("actual: found no actual part matching the given identifier")
    | (assocop_simpl id' a) :: m' => if id =? id' then Ret a else actual id m'
    | _ :: m' => actual id m'
    end.
  
  (** The [get_comp_aux] function looks up [cstmt] for a component
      instantiation statement labelled with [id__c] as a component
      instance identifier, and returns the component instantiation
      statement when found.

      The [get_comp_aux] function throws an error there exist multiple
      component instantiation statements with identifier [id__c] in
      [cstmt].

      The [get_comp_aux] function returns [None] (does not throw an
      error) if no component instantitation statement with [id__c] is
      found in [cstmt]. *)

  Definition cistmt (id__c id__e : ident) (g : genmap) (i : inputmap) (o : outputmap) :
    { ci : cs | exists id__e g i o, ci = cs_comp id__c id__e g i o }.
    refine (exist _ (cs_comp id__c id__e g i o) _).
    exists id__e, g, i, o; reflexivity.
  Defined.

  Fixpoint get_comp_aux (id__c : ident) (cstmt : cs) {struct cstmt} :
    CompileTimeState (option { ci : cs | exists id__e g i o, ci = cs_comp id__c id__e g i o}) :=
    match cstmt with
    | cs_comp id__c' id__e g i o =>
        if id__c =? id__c' then Ret (Some (cistmt id__c id__e g i o)) else Ret None
    | cs_par cstmt' cstmt'' =>
        do optcomp' <- get_comp_aux id__c cstmt';
        do optcomp'' <- get_comp_aux id__c cstmt'';
        match optcomp', optcomp'' with
        | Some _, Some _ =>
            Err ("get_comp_aux: found two component instances with the same identifier.")
        | None, Some _ => Ret optcomp''
        | Some _, None => Ret optcomp'
        | _, _ => Ret None
        end
    | _ => Ret None 
    end.

  (** Calls the [get_comp_aux] function, and returns a [cs] (i.e. the
      component instance with identifier [id__c]) if [get_comp_aux]
      returns [Some cs].

      Raises an error if [get_comp_aux] returns [None] (i.e. no
      component instance with identifier [id__c] exists in [cstmt]). *)

  Definition get_comp (id__c : ident) (cstmt : cs) : CompileTimeState { ci : cs | exists id__e g i o, ci = cs_comp id__c id__e g i o } :=
    do optcomp <- get_comp_aux id__c cstmt;
    match optcomp with
      Some cstmt => Ret cstmt
    | _ => Err ("get_comp: no component instance found") end.

  (** The [put_comp] function looks up in [cstmt] for a component
      instantiation statement with identifier [id__c], and replaces the
      statement with [cistmt] in [cstmt]. If no CIS with identifier
      [id__c] exists in [cstmt], then [cistmt] is directly composed with
      [cstmt] with the || operator. The [put_comp] function throws an
      error if multiple CIS with identifier [id__c] exist in [cstmt]. *)

  Fixpoint put_comp
           (id__c : ident)
           (cistmt : { ci : cs | exists id__e g i o, ci = cs_comp id__c id__e g i o})
           (cstmt : cs) {struct cstmt} : CompileTimeState cs :=
  match cstmt with
  | cs_comp id__c' _ _ _ _ =>
      if id__c =? id__c' then Ret (proj1_sig cistmt)
      else Ret (cstmt // proj1_sig cistmt)
  | cstmt1 // cstmt2 =>
      do optcomp <- get_comp_aux id__c cstmt1;
      if optcomp then
        (* If there exists a component instance with identifier [id__c]
           in [cstmt1], then put [cistmt] in [cstmt1]. *)
        do cstmt3 <- put_comp id__c cistmt cstmt1;
        Ret (cstmt3 // cstmt2)
      else
        (* Else put [cistmt] in [cstmt2]. *)
        do cstmt3 <- put_comp id__c cistmt cstmt2;
        Ret (cstmt1 // cstmt3)
  | _ => Ret (cstmt // proj1_sig cistmt)
  end.
  
End Sitpn2HVhdlUtils.

(** ** Unit testing *)

Require Import test.sitpn.dp.WellDefinedSitpns.

(** ** Unit tests over [cassoc_imap] and [cassoc_omap] *)

Definition imap : inputmap :=
  [(associp_ (n_xid 0 (e_nat 0)) (e_bool true));
   (associp_ (n_xid 0 (e_nat 1)) (e_bool false))
  ].

Eval vm_compute in (RedV ((cassoc_imap sitpn_simpl imap 0 (e_bool true)) (InitS2HState sitpn_simpl 10))).
Eval vm_compute in (RedV
                      ((do imap1 <- cassoc_imap sitpn_simpl imap 0 (e_bool true);
                        do imap2 <- cassoc_imap sitpn_simpl imap1 3 (e_nat 3);
                        do imap3 <- cassoc_imap sitpn_simpl imap2 0 (e_bool true);
                        cassoc_imap sitpn_simpl imap3 0 (e_bool true))
                         (InitS2HState sitpn_simpl 10))).

Eval vm_compute in (RedV
                      ((do imap1 <- cassoc_imap sitpn_simpl [] 0 (e_bool true);
                        do imap2 <- cassoc_imap sitpn_simpl imap1 0 (e_bool true);
                        do imap3 <- cassoc_imap sitpn_simpl imap2 0 (e_bool true);
                        cassoc_imap sitpn_simpl imap3 0 (e_bool true))
                         (InitS2HState sitpn_simpl 10))).

Definition omap : outputmap :=
  [(assocop_simpl 0 None);
   (assocop_idx 0 (e_nat 0) (n_id 10));
   (assocop_idx 0 (e_nat 1) (n_id 10));
   (assocop_idx 0 (e_nat 2) (n_id 10))
  ].

Eval vm_compute in (RedV ((cassoc_omap sitpn_simpl omap 0 (n_id 12)) (InitS2HState sitpn_simpl 10))).
Eval vm_compute in (RedV
                      ((do omap1 <- cassoc_omap sitpn_simpl omap 0 (n_id 0);
                        do omap2 <- cassoc_omap sitpn_simpl omap1 3 (n_id 3);
                        do omap3 <- cassoc_omap sitpn_simpl omap2 0 (n_id 4);
                        cassoc_omap sitpn_simpl omap3 0 (n_id 5))
                         (InitS2HState sitpn_simpl 10))).

(** ** Unit tests over [actual] *)

Definition omap1 := (omap ++ [assocop_simpl 0 (Some (n_id 0))])%list.

Eval vm_compute in (RedV ((actual sitpn_simpl 0 omap1) (InitS2HState sitpn_simpl 10))).
Eval vm_compute in (RedV ((actual sitpn_simpl 1 omap1) (InitS2HState sitpn_simpl 10))).

(** ** Unit tests over [get_comp] *)

Include HVhdlCsNotations.

Definition cstmt1 : cs := cs_comp 0 place_entid [] [] [].
Definition cstmt2 : cs := ((cs_comp 0 place_entid [] [] []) // (cs_comp 1 place_entid [] [] []))
                            // (cs_comp 0 place_entid [] [] []).

Eval vm_compute in (RedV
                      ((get_comp sitpn_simpl 0 cstmt1)
                         (InitS2HState sitpn_simpl 10))).

Eval vm_compute in (RedV
                      ((get_comp sitpn_simpl 3 cstmt2)
                         (InitS2HState sitpn_simpl 10))).

(** ** Unit tests over [put_comp] *)

Definition ci0 := cistmt 0 transition_entid [] [] [].
Definition ci1 := cistmt 1 place_entid [] [] [].

Definition cstmt : cs := ((cs_comp 0 place_entid [] [] []) // (cs_comp 0 place_entid [] [] []))
                           // (cs_comp 2 place_entid [] [] []).

Eval vm_compute in (RedV
                      ((put_comp sitpn_simpl 0 ci0 cstmt)
                         (InitS2HState sitpn_simpl 10))).
