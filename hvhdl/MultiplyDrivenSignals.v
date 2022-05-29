(** * Detection of multiply-driven signals *)

(** This module gathers functions and relations that aim at the static
    detection of multiply-driven signals in the behavior of a H-VHDL
    design.

    The no "multiply-driven signal" check is a part of the elaboration
    of a given H-VHDL design.

    Note that our definition of multiply-driven signal is much more
    restrictive than the one the VHDL reference manual. For instance,
    if id(0) <= e0 appears in a process p0's body and id(1) <= e1 in a
    process p1's body, where p0 and p1 are part of the same design
    behavior, then signal id will be considered as multiply-driven.

    This enforces the fact that, in the semantics of H-VHDL, at most
    one process can drive the value of a given signal, may it be of scalar
    or composite type. *)

Require Import common.CoqLib.
Require Import common.GlobalTypes.

Require Import hvhdl.HVhdlTypes.
Require Import hvhdl.AbstractSyntax.
Require Import hvhdl.Environment.

(** ** Signal assignment look-up *)

(** Specification of signal assignment look-up in sequential
    statement *)

Fixpoint AssignedInSS (id : ident) (stmt : ss) :=
  match stmt with
  | ss_sig ((n_id id__s) | (n_xid id__s _)) _ => id = id__s
  | (ss_loop _ _ _ stmt1 | ss_falling stmt1 | ss_rising stmt1) =>
    AssignedInSS id stmt1
  | (ss_ifelse _ stmt1 stmt2 | ss_rst stmt1 stmt2 | ss_seq stmt1 stmt2) =>
    AssignedInSS id stmt1 \/ AssignedInSS id stmt2
  | _ => False
  end.

(** Returns true if the signal identifier [id] is assigned in the
    sequential statement [ss], i.e. if [id] appears in the left part
    of a signal assignment statement.  *)

Fixpoint is_assgd_in_ss (stmt : ss) (id : ident) {struct stmt} : bool :=
  match stmt with
  | ss_sig ((n_id id') | (n_xid id' _)) _ => Nat.eqb id id'
  | (ss_loop _ _ _ stmt | ss_falling stmt | ss_rising stmt) =>
      is_assgd_in_ss stmt id
  | (ss_ifelse _ stmt1 stmt2 | ss_rst stmt1 stmt2 | ss_seq stmt1 stmt2) =>
      is_assgd_in_ss stmt1 id || is_assgd_in_ss stmt2 id
  | _ => false
  end.

(** Specification of signal assignment look-up in output port map *)

Definition IsAssgdInOPA (opa : opassoc) (id : ident) :=
  match opa with
  | (opa_simpl _ (Some (n_id id__a)) | opa_idx _ _ (n_id id__a)) => id__a = id
  | _ => False
  end.

Definition IsAssgdInOMap (o : outputmap) (id : ident) :=
  exists opa, In opa o /\ IsAssgdInOPA opa id.
  
(** Returns true if the signal identifier [id] is an actual part
    (i.e. the right part of an association) in the output port map
    [o].

    Note that if a subelement of [id] appears as an actual part of an
    association in [o], it is not considered as an assignment of [id].
    For instance, if [na ⇒ id(0) ∈ o] and it is the only association
    where [id] appears, then [is_assgd_in_omap o id] returns [false].
    
    This definition is sufficient in our case because we are
    generating output port map with no indexed identifier in the
    actual parts of associations.

 *)

Definition is_assgd_in_opa (opa : opassoc) (id : ident) :=
  match opa with
  | (opa_simpl _ (Some (n_id id__a)) | opa_idx _ _ (n_id id__a)) => Nat.eqb id__a id
  | _ => false
  end.

Fixpoint is_assgd_in_omap (o : outputmap) (id : ident) :=
  match o with
  | [] => false
  | opa :: tl => is_assgd_in_opa opa id || is_assgd_in_omap tl id
  end.

(** Specification of signal assignment look-up in concurrent statement *)
                 
Fixpoint AssignedInCs (id : ident) (cstmt : cs) :=
  match cstmt with
  | cs_comp id__c id__e gm ipm opm => IsAssgdInOMap opm id
  | cs_ps id__p vars body => AssignedInSS id body
  | cs_null => False
  | cs_par cstmt' cstmt'' =>
    AssignedInCs id cstmt' \/ AssignedInCs id cstmt''
  end.

(** Returns true if [id] is assigned in the output port map of a
    design instance or in the body of process that are parts of the
    [cstmt] concurrent statement. *)

Fixpoint is_assgd_in_cs (cstmt : cs) (id : ident) := 
  match cstmt with
  | cs_comp id__c id__e g i o => is_assgd_in_omap o id
  | cs_ps id__p vars body => is_assgd_in_ss body id
  | cs_par cstmt1 cstmt2 =>
      is_assgd_in_cs cstmt1 id || is_assgd_in_cs cstmt2 id
  | cs_null => false
  end.

(** Specification of multiply-driven signal look-up in an output port
    map.

    A signal [id] is multiply-driven in output port map [o] if there
    exists to different association in [o] having [id] as actual part.
 *)

Definition IsMdInOMap (o : outputmap) (id : ident) :=
  exists opa1 opa2,
    In opa1 o
    /\ In opa2 o
    /\ opa1 <> opa2
    /\ IsAssgdInOPA opa1 id /\ IsAssgdInOPA opa2 id.

(** Returns true if the signal [id] is multiply-driven in output port
    map [o], i.e. if there exists to different association in [o]
    having [id] as actual part. *)

Fixpoint is_md_in_omap (o : outputmap) (id : ident) :=
  match o with
  | opa :: tl => if is_assgd_in_opa opa id then
                   is_assgd_in_omap tl id
                 else is_md_in_omap tl id
  | _ => false
  end.

(** Specification of multiply-driven signal look-up in an concurrent
    statement.

    A signal [id] is multiply-driven in the concurrent statement
    [cstmt] if it is multiply-driven in the output port map of a
    design instance, or if it is assigned in two different concurrent
    statements which parallel composition happens in [cstmt]. *)

(** Returns true is signal [id] is multiply-driven in [cstmt]; false
    otherwise. *)

Fixpoint is_md_in_cs (cstmt : cs) (id : ident) :=
  match cstmt with
  | cs_comp _ _ _ _ o => is_md_in_omap o id
  | cs_par cstmt1 cstmt2 =>
      is_md_in_cs cstmt1 id
      || is_md_in_cs cstmt2 id
      || (is_assgd_in_cs cstmt1 id && is_assgd_in_cs cstmt2 id)
  | _ => false
  end.

(** No multiply-driven signal check *)

Definition NoMDInCS (Δ : ElDesign) (cstmt : cs) :=
  forall id, InternalOf Δ id \/ OutputOf Δ id -> is_md_in_cs cstmt id = false.
