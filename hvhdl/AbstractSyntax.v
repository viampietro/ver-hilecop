(*!============================!*)
(** *  Abstract syntax of H-VHDL    *)
(*!============================!*)

Require Import Coqlib.
Require Import Arrays.
Require Import GlobalTypes.

Declare Scope ast_scope.

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

    - a transition_t constant (not_temporal, temporal_a_a, 
      temporal_a_b, temporal_a_inf)

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

(** Notations for names. *)

Notation " $ x " := (n_id x) (at level 100) : ast_scope.

(** Notations for expressions. *)

Notation " # x " := (e_name (n_id x)) (at level 99) : ast_scope.
Notation " x [[ i ]] " := (e_name (n_xid x i)) (at level 100) : ast_scope. 

Notation " x @&& y " := (e_binop bo_and x y) (at level 100) : ast_scope.
Notation " x @|| y " := (e_binop bo_and x y) (at level 100) : ast_scope.
Notation " x @= y "  := (e_binop bo_eq x y) (at level 100)  : ast_scope.
Notation " x @/= y " := (e_binop bo_neq x y) (at level 100) : ast_scope.
Notation " x @< y "  := (e_binop bo_lt x y) (at level 100)  : ast_scope.
Notation " x @<= y " := (e_binop bo_le x y) (at level 100)  : ast_scope.
Notation " x @> y "  := (e_binop bo_gt x y) (at level 100)  : ast_scope.
Notation " x @>= y " := (e_binop bo_ge x y) (at level 100)  : ast_scope.
Notation " x @+ y "  := (e_binop bo_add x y) (at level 100) : ast_scope.
Notation " x @- y "  := (e_binop bo_sub x y) (at level 100) : ast_scope.

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

(** Notations for sequential statements. *)

Infix "@<==" := ss_sig (at level 100) : ast_scope.
Infix "@:=" := ss_var (at level 100) : ast_scope.

Notation "'If' c 'Then' e " :=
  (ss_if c e)
    (at level 200, right associativity,
     format "'[v   ' 'If'  c '/' '[' 'Then'  e  ']' ']'") : ast_scope.

Notation "'For' i 'From' l 'To' u 'Do' x " :=
  (ss_loop i l u x)
    (at level 200, format "'[v' 'For'  i  'From'  l  'To'  u  'Do' '/' '['   x ']' ']'") : ast_scope.

Notation " x ;; y ;; .. ;; z " := (ss_seq .. (ss_seq x y) .. z) (at level 100) : ast_scope.

(** ** Concurrent statements. *)

(** Process local environment declarations. *)

Inductive vdecl : Type :=
  vdecl_ (vid : ident) (t : tind).

(** Generic map clause. *)

Inductive assocg : Type :=
  assocg_ (id : ident) (e : expr).

(** Port map entry ("in" mode port). *)

Inductive associp : Type :=
  associp_ (n : name) (e : expr).

(** Port map entry ("out" mode port). *)

Inductive assocop : Type :=
  (** None for the "open" keyword. *)
  assocop_ (n : name) (n' : option name). 

(** Concurrent statement. *)

Inductive cs : Type :=

(** Process statement. *)
| cs_ps (pid : ident)       (** Process id *)
        (sl : IdSet)        (** Sensitivity list *)
        (vars : list vdecl) (** Variable declaration list *)
        (stmt : ss)         (** Sequential statement block *)
      
(** Component instantiation statement. *)
| cs_comp (compid : ident)       (** Component id *)
          (entid : ident)        (** Entity label *)
          (gmap : list assocg)   (** Generic map *)
          (ipmap : list associp) (** In port map *)
          (opmap : list assocop) (** Out port map *)

(** Composition of concurrent statements. *)
| cs_par (cstmt : cs) (cstmt' : cs).

Notation "cstmt // cstmt'" := (cs_par cstmt cstmt') (at level 0).

(** ** Design declaration. *)

(** Generic constant declaration. *)

Inductive gdecl : Type :=
  gdecl_ (genid : ident) (t : tind) (e : expr).
                                   
(** Port declarations. *)

Inductive pdecl : Type :=
| pdecl_in (portid : ident) (t : tind)  (** Declaration of port in "in" mode. *)
| pdecl_out (portid : ident) (t : tind). (** Declaration of port in "out" mode. *)
            
(** Architecture declarations. *)

Inductive adecl : Type :=
| adecl_sig (sigid : ident) (t : tind)                (** Signal declaration. *)
| adecl_const (constid : ident) (t : tind) (v : expr). (** Constant declaration. *)

(** Design declaration. *)

Inductive design : Type :=
  design_ (entid    : ident)      (** Entity id *)
          (archid   : ident)      (** Architecture id *)
          (gens     : list gdecl) (** Generic constant clause *)
          (ports    : list pdecl) (** Port clause *)
          (adecls   : list adecl) (** Architecture declarative part *)
          (behavior : cs).        (** Concurrent statement part *)
