(*!============================!*)
(** *  Abstract syntax of H-VHDL    *)
(*!============================!*)

Require Import Coqlib.
Require Import Arrays.
Require Import GlobalTypes.

(** Set of binary operators. *)

Inductive binop : Set :=
  bo_and | bo_or | bo_eq | bo_neq |
  bo_lt | bo_le | bo_gt | bo_ge |
  bo_add | bo_sub.

(** ** Expressions: *)

(** An expression is either: 
    - a natural constant
    - a boolean constant
    - an arc_t constant (basic, test or inhib)
    - a transition_t constant (not_temporal, temporal_a_a, temporal_a_b, temporal_a_inf)
    - an identifier
    - an identifier with index (e.g "myvar(3)")
    - an aggregate, i.e list of expressions
    - e op e'    
    - not e   
 *)

Inductive expr : Type :=
| e_nat : nat -> expr (** Natural constant *)
| e_bool : bool -> expr (** Boolean constant *)
| e_name : name -> expr (** Name constant *)
| e_arc : arc_t -> expr (** [arc_t] constant *)
| e_trans : transition_t -> expr (** [transition_t] constant *)
| e_aggreg : list expr -> expr (** Aggregate of expressions *)
| e_binop : binop -> expr -> expr -> expr (** Binary operator expression *)
| e_not : expr -> expr (** Not expression *)

(** Names *)
with name : Type :=
| n_id : ident -> name  
| n_xid : ident -> expr -> name.

(** Subtype indications and type definitions. *)

Inductive tind : Type :=
| tind_boolean                         (** Boolean type indication. *)
| tind_natural (rconstr : expr * expr) (** Natural with range constraint. *)
| tind_arc_t                           (** arc_t type indication. *)
| tind_transition_t                    (** transition_t type indication. *)
| tind_array (t : tind) (iconstr : expr * expr). (** Array of [t] with index constraint. *)

(** ** Sequential statements. *)

Inductive ss : Type :=
| ss_sig (signame : name) (e : expr)                      (** Signal assignment statement. *)
| ss_var (varname : name) (e : expr)                      (** Variable assignment statement. *)
| ss_if (e : expr) (stmt : ss)                            (** If statement. *)
| ss_ifelse (e : expr) (stmt : ss) (stmt' : ss)           (** If then else statement. *)
| ss_loop (id : ident) (e : expr) (e' : expr) (stmt : ss) (** Loop statement. *)
| ss_falling (stmt : ss)                                  (** Falling edge block statement. *)
| ss_rising (stmt : ss)                                   (** Rising edge block statement. *)
| ss_seq (stmt : ss) (stmt' : ss).                        (** Composition of seq. statements. *)

Notation "stmt ;; stmt'" := (ss_seq stmt stmt') (at level 100).

(** ** Concurrent statements. *)

Inductive cs : Type :=

(** Process statement. *)
| cs_ps (pid : ident)                (** Process id *)
        (sl : list ident)            (** Sensitivity list *)
        (vars : list (ident * tind)) (** Variable declaration list *)
        (stmt : ss)                  (** Sequential statement block *)
      
(** Component instantiation statement. *)
| cs_comp (compid : ident)                     (** Component id *)
          (entid : ident)                      (** Entity label *)
          (gmap : list (ident * expr))         (** Generic map *)
          (ipmap : list (name * expr))         (** In port map *)
          (opmap : list (name * option name))  (** Out port map, 'n => None' ≡ 'n => open' *)

(** Composition of concurrent statements. *)
| cs_par (cstmt : cs) (cstmt' : cs).

Notation "cstmt // cstmt'" := (cs_par cstmt cstmt') (at level 0).

(** ** Design declaration. *)

(** Generic constant declaration. *)

Inductive gdecl : Type :=
| gdecl_ (genid : ident) (t : tind) (e : expr)
| gdecl_seq : gdecl -> gdecl -> gdecl.
                                   
(** Port declarations. *)

Inductive pdecl : Type :=
| pdecl_in (portid : ident) (t : tind)  (** Declaration of port in "in" mode. *)
| pdecl_out (portid : ident) (t : tind) (** Declaration of port in "out" mode. *)
| pdecl_seq : pdecl -> pdecl -> pdecl.  (** Sequence of port declaration. *)
            
(** Architecture declarations. *)

Inductive adecl : Type :=
| adecl_sig (sigid : ident) (t : tind)                (** Signal declaration. *)
| adecl_const (constid : ident) (t : tind) (v : expr) (** Constant declaration. *)
| adecl_seq : adecl -> adecl -> adecl.                (** Sequence of architecture declaration *)

(** Design declaration. *)

Inductive design : Type :=
  design_ (entid    : ident) (** Entity id *)
          (archid   : ident) (** Architecture id *)
          (gens     : gdecl) (** Generic constant list *)
          (ports    : pdecl) (** Port list *)
          (adecls   : adecl) (** Architecture declarative part *)
          (behavior : cs).   (** Concurrent statement part *)
