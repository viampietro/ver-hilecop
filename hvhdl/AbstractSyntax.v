(*!============================!*)
(** *  Abstract syntax of H-VHDL    *)
(*!============================!*)

Require Import Coqlib.
Require Import GlobalTypes.
Require Import HVhdlTypes.

(** Declares the scope of notations for the H-VHDL abstract syntax. *)

Declare Scope abss_scope.
Open Scope abss_scope.

(** Set of binary operators. *)

Inductive binop : Set :=
  bo_and | bo_or | bo_eq | bo_neq |
  bo_lt | bo_le | bo_gt | bo_ge |
  bo_add | bo_sub.

(** ** Expressions: *)

(** An expression is either: 

    - a natural constant
    - a boolean constant
    - an identifier
    - an identifier with index (e.g "myvar(3)")
    - an aggregate, i.e a non-empty list of expressions
    - e op e'    
    - not e   
 *)

Inductive expr : Type :=
| e_nat : nat-> expr (** Natural constant *)
| e_bool : bool -> expr (** Boolean constant *)
| e_name : name -> expr (** Name constant *)
| e_aggreg : agofexprs -> expr (** Aggregate of expressions *)
| e_binop : binop -> expr -> expr -> expr (** Binary operator expression *)
| e_not : expr -> expr (** Not expression *)

(** Aggregate of expressions (non-empty list of expressions) *)

with agofexprs : Type :=
| agofe_one : expr -> agofexprs
| agofe_cons : expr -> agofexprs -> agofexprs
                    
(** Names *)
                    
with name : Type :=
| n_id : ident -> name  
| n_xid : ident -> expr -> name.

Module HVhdlExprNotations.

  
End HVhdlExprNotations.

(** Notations and coercions for names. *)

Notation " '$' x " := (n_id x) (at level 100) : abss_scope.
Notation " x $[[ i ]] " := (n_xid x i) (at level 100) : abss_scope.

Coercion n_id : ident >-> name.

(** Notations and coercions for expressions. *)

Notation " # x " := (e_name (n_id x)) (at level 99) : abss_scope.
Notation " x [[ i ]] " := (e_name (n_xid x i)) (at level 100) : abss_scope. 

Notation " x @&& y " := (e_binop bo_and x y) (at level 100) : abss_scope.
Notation " x @|| y " := (e_binop bo_or x y) (at level 100) : abss_scope.
Notation " x @= y "  := (e_binop bo_eq x y) (at level 100)  : abss_scope.
Notation " x @/= y " := (e_binop bo_neq x y) (at level 100) : abss_scope.
Notation " x @< y "  := (e_binop bo_lt x y) (at level 100)  : abss_scope.
Notation " x @<= y " := (e_binop bo_le x y) (at level 100)  : abss_scope.
Notation " x @> y "  := (e_binop bo_gt x y) (at level 100)  : abss_scope.
Notation " x @>= y " := (e_binop bo_ge x y) (at level 100)  : abss_scope.
Notation " x @+ y "  := (e_binop bo_add x y) (at level 100) : abss_scope.
Notation " x @- y "  := (e_binop bo_sub x y) (at level 100) : abss_scope.

Notation " x @|| y @|| .. @|| z " := (e_binop bo_or .. (e_binop bo_or x y) .. z) (at level 100) : abss_scope.
Notation " x @&& y @&& .. @&& z " := (e_binop bo_and .. (e_binop bo_and x y) .. z) (at level 100) : abss_scope.

Coercion e_nat : nat >-> expr.
Coercion e_bool : bool >-> expr.

(** Converts an aggregate of expressions into a list. *)

Fixpoint agofe2list (ag : agofexprs) {struct ag} : list expr :=
  match ag with
  | agofe_one e => [e]
  | agofe_cons e ag' => e :: agofe2list ag'
  end.

Coercion agofe2list : agofexprs >-> list.

(** Subtype indications.

    Subtype indications are used in the declarative parts of a H-VHDL
    design; e.g:

    signal s : natural(0,255); constant c : boolean := false; *)

Inductive tind : Type :=
| tind_boolean                                           (** Boolean type indication. *)
| tind_natural (rlower : expr) (rupper : expr)           (** Natural with range constraint. *)
| tind_array (t : tind) (ilower : expr) (iupper : expr). (** Array of [t] with index constraint. *)

(** ** Sequential statements. *)

Inductive ss : Type :=
| ss_sig (signame : name) (e : expr)                      (** Signal assignment statement. *)
| ss_var (varname : name) (e : expr)                      (** Variable assignment statement. *)
| ss_if (e : expr) (stmt : ss)                            (** If statement. *)
| ss_ifelse (e : expr) (stmt : ss) (stmt' : ss)           (** If then else statement. *)
| ss_loop (id : ident) (e : expr) (e' : expr) (stmt : ss) (** Loop statement. *)
| ss_falling (stmt : ss)                                  (** Falling edge block statement. *)
| ss_rising (stmt : ss)                                   (** Rising edge block statement. *)
| ss_seq (stmt : ss) (stmt' : ss)                         (** Composition of seq. statements. *)
| ss_null.                                                (** Null statement. *)

(** Notations for sequential statements. *)

Infix "@<==" := ss_sig (at level 100) : abss_scope.
Infix "@:=" := ss_var (at level 100) : abss_scope.

Notation "'If' c 'Then' e " :=
  (ss_if c e)
    (at level 200, right associativity,
     format "'[v' 'If'  c '//' 'Then'  e ']'") : abss_scope.

Notation "'If' c 'Then' x 'Else' y" :=
  (ss_ifelse c x y)
    (at level 200, right associativity,
     format "'[v' 'If'  c '//' 'Then'  x '//' 'Else'  y ']'") : abss_scope.

Notation "'For' i 'In' l 'To' u 'Loop' x " :=
  (ss_loop i l u x)
    (at level 200, format "'[v' 'For'  i  'In'  l  'To'  u  'Loop' '/' '['   x ']' ']'") : abss_scope.

Notation "'Rising' stmt" := (ss_rising stmt) (at level 200) : abss_scope.
Notation "'Falling' stmt" := (ss_falling stmt) (at level 200) : abss_scope.

Notation " x ;; y ;; .. ;; z " := (ss_seq .. (ss_seq x y) .. z) (at level 100) : abss_scope.

(** ** Concurrent statements. *)

(** Process local variable declaration; e.g:
    
    - Concrete syntax = "variable v : natural(0,255);"
    - Abstract syntax = "vdecl_ v (tind_natural (0,255))"

 *)

Inductive vdecl : Type :=
  vdecl_ (vid : ident) (t : tind).

(** Generic map entry; e.g:

    - Concrete syntax = "g ⇒ 1"
    - Abstract syntax = "assocg_ g (e_nat 1)"
 *)

Inductive assocg : Type :=
  assocg_ (id : ident) (e : expr).

(** Type of generic map. *)

Definition genmap := list assocg.

(** Port map entry ("in" mode port). *)

Inductive associp : Type :=
  associp_ (n : name) (e : expr).

(** Type of input port map. *)

Definition inputmap := list associp.

(** Port map entry ("out" mode port). 
    [None] represents the [open] port keyword
    in the actual part of the output port association.

    We forbid the association of an indexed formal part
    with the open keyword, i.e:
    "myport(0) ⇒ open"
 *)

Inductive assocop : Type :=
| assocop_simpl :  ident -> option name -> assocop
| assocop_idx   : ident -> expr -> name -> assocop. 

(** Type of output port map. *)

Definition outputmap := list assocop.

(** Concurrent statement. *)

Inductive cs : Type :=

(** Process statement. *)
| cs_ps (pid : ident)       (** Process id *)
        (sl : IdSet)        (** Sensitivity list *)
        (vars : list vdecl) (** Variable declaration list *)
        (stmt : ss)         (** Sequential statement block *)
      
(** Component instantiation statement. *)
| cs_comp (compid : ident) (** Component id *)
          (entid : ident)  (** Entity label *)
          (gmap : genmap)  (** Generic map *)
          (ipmap : inputmap)  (** In port map *)
          (opmap : outputmap) (** Out port map *)

(** Composition of concurrent statements. *)
| cs_par (cstmt : cs) (cstmt' : cs)

(** Null statement *)
| cs_null.

Module HVhdlCsNotations.

  Notation " x // y // .. // z " := (cs_par .. (cs_par x y) .. z) (at level 100) : abss_scope.
  Notation "pid ':' 'Process' sl vars 'Begin' stmt" :=
    (cs_ps pid sl vars stmt)
      (at level 200(* , *)
       (* format "'[v' pid  ':'  'Process'  sl '/' '['   vars ']' '/' 'Begin' '/' '['   stmt ']' ']'" *)) : abss_scope.

  Notation "pid ':' 'Process' sl 'Begin' stmt" :=
    (cs_ps pid sl [] stmt)
      (at level 200(* , *)
       (* format "'[v' pid  ':'  'Process'  sl '/' 'Begin' '/' '['   stmt ']' ']'" *)) : abss_scope.
  
End HVhdlCsNotations.

Import HVhdlCsNotations.

(** ** Design declaration. *)

(** Generic constant declaration. *)

Inductive gdecl : Type :=
  gdecl_ (genid : ident) (t : tind) (e : expr).
                                   
(** Port declarations. *)

Inductive pdecl : Type :=
| pdecl_in (portid : ident) (t : tind)  (** Declaration of port in "in" mode. *)
| pdecl_out (portid : ident) (t : tind). (** Declaration of port in "out" mode. *)
            
(** Signal declaration. *)

Inductive sdecl : Type :=
  sdecl_ (sigid : ident) (t : tind).

(** Design declaration, i.e the entity-architecture couple; e.g:
    
    - Concrete syntax =

    "entity [entid] is [gens]; [ports]; end [entid];
    
     architecture [archid] of [entid] is 
       [sigs]; 
     begin 
       [behavior] 
     end [archid];" 

   - Abstract syntax = "[design_ entid archid gens ports sigs behavior]"

*)

Record design : Type :=
  design_ {
      entid    : ident;      (** Entity id *)
      archid   : ident;      (** Architecture id *)
      gens     : list gdecl; (** Generic constant clause *)
      ports    : list pdecl; (** Port clause *)
      sigs   : list sdecl; (** Architecture declarative part *)
      behavior : cs
    }.

(** ** Misc. Definitions for the H-VHDL Abstract Syntax *)

(** Relation between a concurrent statement and its list
    representation.  For a given [cstmt] and a list [l] of [cs],
    [FlattenCs ctsmt l] states that l is the flattened version of
    [cstmt].  *)

Inductive FlattenCs : cs -> list cs -> Prop :=
| FlattenCs_null_singl : FlattenCs cs_null nil
| FlattenCs_null_hd :
    forall cstmt l,
      FlattenCs cstmt l ->
      FlattenCs (cs_null // cstmt) l
| FlattenCs_ps_singl :
    forall id__p sl vars body,
      FlattenCs (cs_ps id__p sl vars body) [cs_ps id__p sl vars body]
| FlattenCs_ps_hd :
    forall id__p sl vars body cstmt l,
      FlattenCs cstmt l ->
      FlattenCs ((cs_ps id__p sl vars body) // cstmt) ((cs_ps id__p sl vars body) :: l)
| FlattenCs_comp_singl :
    forall id__c id__e gm ipm opm,
      FlattenCs (cs_comp id__c id__e gm ipm opm) [cs_comp id__c id__e gm ipm opm]
| FlattenCs_comp_hd :
    forall id__c id__e gm ipm opm cstmt l,
      FlattenCs cstmt l ->
      FlattenCs ((cs_comp id__c id__e gm ipm opm) // cstmt) ((cs_comp id__c id__e gm ipm opm) :: l)
|FlattenCs_cons :
   forall cstmt cstmt' l l',
     FlattenCs cstmt l -> FlattenCs cstmt' l' -> FlattenCs (cstmt // cstmt') (l ++ l').

Hint Constructors FlattenCs.
