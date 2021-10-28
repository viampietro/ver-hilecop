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

  (** Generates a new internal signal identifier [id__s], declares [id__s]
      as a Boolean signal in the compile-time state; then, adds the
      association [(id__o(idx), id__s)] in output port map [o], and [(id__i(j),
      id__s)] in input port map [i] (where index [j] is computed by
      the cassoc function). Finally, returns the modified output port
      map [o] and input port map [i]. *)

  Definition connect (o : outputmap) (i : inputmap)
             (id__o : ident)
             (idx : nat)
             (id__i : ident) :
    CompileTimeState (outputmap * inputmap) :=
    do id__s <- get_nextid;
    do _ <- add_sig_decl (sdecl_ id__s tind_boolean);
    do i' <- cassoc_imap i id__i (#id__s);
    Ret ((o ++ [assocop_idx id__o idx ($id__s)]), i').
  
  (** The [get_comp_aux] function looks up [cstmt] for a component
      instantiation statement labelled with [id__c] as a component
      instance identifier, and returns a tuple composed of the
      component instantiation statement's entity identifier, generic
      map, input port and output port map when found.

      The [get_comp_aux] function throws an error there exist multiple
      component instantiation statements with identifier [id__c] in
      [cstmt].

      The [get_comp_aux] function returns [None] (does not throw an
      error) if no component instantitation statement with identifier
      [id__c] is found in [cstmt]. *)

  Fixpoint get_comp_aux (id__c : ident) (cstmt : cs) {struct cstmt} :
    CompileTimeState (option (ident * genmap * inputmap * outputmap)) :=
    match cstmt with
    | cs_comp id__c' id__e g i o =>
        if id__c =? id__c' then Ret (Some (id__e, g, i, o)) else Ret None
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

  (** Calls the [get_comp_aux] function with the compile-time state's
      behavior passed as second input, and returns a [cs] (i.e. the
      component instance with identifier [id__c]) if [get_comp_aux]
      returns [Some cs].

      Raises an error if [get_comp_aux] returns [None] (i.e. no
      component instance with identifier [id__c] exists in [cstmt]). *)

  Definition get_comp (id__c : ident) : CompileTimeState (ident * genmap * inputmap * outputmap) :=
    do b <- get_beh;
    do optcomp <- get_comp_aux id__c b;
    match optcomp with
      Some comp => Ret comp
    | _ => Err ("get_comp: no component instance found")
    end.

  (** The [put_comp_aux] function looks up in [cstmt] for a component
      instantiation statement with identifier [id__c], and replaces the
      statement with [cistmt] in [cstmt]. If no CIS with identifier
      [id__c] exists in [cstmt], then [cistmt] is directly composed with
      [cstmt] with the || operator. The [put_comp] function throws an
      error if multiple CIS with identifier [id__c] exist in [cstmt]. *)

  Fixpoint put_comp_aux
           (id__c id__e : ident)
           (g : genmap) (i : inputmap) (o : outputmap)
           (cstmt : cs) {struct cstmt} : CompileTimeState cs :=
  match cstmt with
  | cs_comp id__c' _ _ _ _ =>
      if id__c =? id__c' then Ret (cs_comp id__c id__e g i o)
      else Ret (cstmt // (cs_comp id__c id__e g i o))
  | cstmt1 // cstmt2 =>
      do optcomp <- get_comp_aux id__c cstmt1;
      if optcomp then
        (* If there exists a component instance with identifier [id__c]
           in [cstmt1], then put comp in [cstmt1], and returns the
           parallel composition of modified [cstmt1] and [cstmt2]. *)
        do cstmt3 <- put_comp_aux id__c id__e g i o cstmt1;
        Ret (cstmt3 // cstmt2)
      else
        (* Else put comp in [cstmt2]. *)
        do cstmt3 <- put_comp_aux id__c id__e g i o cstmt2;
        Ret (cstmt1 // cstmt3)
  (* In all other cases, appends the ci at the end of [cstmt]. *)
  | _ => Ret (cstmt // (cs_comp id__c id__e g i o))
  end.

  (** Retrieves the behavior [b] from the compile-time state, and puts
      [cistmt] in the retrieved behavior by calling the [put_comp_aux]
      function. Finally, sets the modified behavior as the new
      behavior in the compile-time state. *)
  
  Definition put_comp (id__c id__e : ident) (g : genmap) (i : inputmap) (o : outputmap) :
    CompileTimeState unit :=
    do b <- get_beh;
    do newb <- put_comp_aux id__c id__e g i o b;
    set_beh newb.

  (** Returns sig type composed of a [cs] statement and a proof that
      this [cs] statement is a component instantiation statement. *)

  Definition to_ci (id__c id__e : ident) (g : genmap) (i : inputmap) (o : outputmap) :
    { ci : cs | exists id__e g i o, ci = cs_comp id__c id__e g i o}.
    refine (exist _ (cs_comp id__c id__e g i o) _); exists id__e, g, i, o; reflexivity.
  Defined.
  
End Sitpn2HVhdlUtils.

Arguments get_comp {sitpn}.
Arguments put_comp {sitpn}.
Arguments actual {sitpn}.
Arguments connect {sitpn}.
Arguments cassoc_imap {sitpn}.
Arguments cassoc_omap {sitpn}.
