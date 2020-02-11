(*!============================!*)
(** *  Abstract syntax of H-VHDL    *)
(*!============================!*)

Require Import Coqlib.
Require Import GlobalTypes.

(** Set of binary operators. *)

Inductive binop : Set :=
and | or | eq | neq | lt | le | gt | ge | add | sub.

(** ** Expressions: *)

(** An expression is either: 
    - a natural constant
    - a boolean constant
    - an identifier
    - an identifier with index (e.g "myvar(3)")
    - an aggregate, i.e list of expressions
    - e op e'    
 *)

Inductive expr : Type :=
| Enat : nat -> expr (** Natural constant *)
| Ebool : bool -> expr (** Boolean constant *)
| Ename : name -> expr (** Name constant *)
| Eaggreg : list expr -> expr (** Aggregate of expressions *)
| Ebinop : binop -> expr -> expr -> expr (** Binary operator expression *)
| Enot : expr -> expr (** Not expression *)

(** Names *)
with name : Type :=
| Nid : ident -> name  
| Nxid : ident -> expr -> name.

(** Subtype indications and type definitions. *)

Inductive tind : Type :=
| Tid (id : ident) (** Simple subtype indication. *)
| Tcid (id : ident) (constr : expr * expr). (** Subtype indication with constraint. *)

Inductive tdef : Type :=

(** Unconstrained array definition. *)
| Tarray (eltt : tind)
         
(** Constrained array definition. *)
| Tcarray (eltt : tind) (constr : expr * expr)
          
(** Type definition as an enumeration of idents with at least one element. 
    [lme] is the left-most element.
 *)
| Tenum (lme : ident) (enum : list ident).    

(** ** Sequential statements. *)

Inductive ss : Type :=
| Ssig (signame : name) (e : expr)                      (** Signal assignment statement. *)
| Svar (varname : name) (e : expr)                      (** Variable assignment statement. *)
| Sif (e : expr) (stmt : ss)                            (** If statement. *)
| Sifelse (e : expr) (stmt : ss) (stmt' : ss)           (** If then else statement. *)
| Sloop (id : ident) (e : expr) (e' : expr) (stmt : ss) (** Loop statement. *)
| Sfalling (stmt : ss)                                  (** Falling edge block statement. *)
| Srising (stmt : ss)                                   (** Rising edge block statement. *)
| Sseq (stmt : ss) (stmt' : ss).                        (** Composition of seq. statements. *)

Notation "stmt ;; stmt'" := (Sseq stmt stmt') (at level 100).

(** ** Concurrent statements. *)

Inductive cs : Type :=

(** Process statement. *)
| Cps (pid : ident)                (** Process id *)
      (sl : list ident)            (** Sensitivity list *)
      (vars : list (ident * tind)) (** Variable declaration list *)
      (stmt : ss)                  (** Sequential statement block *)
      
(** Component instantiation statement. *)
| Ccomp (compid : ident)                     (** Component id *)
        (entid : ident)                      (** Entity label *)
        (gmap : list (ident * expr))         (** Generic map *)
        (ipmap : list (name * expr))         (** In port map *)
        (opmap : list (name * option name))  (** Out port map, 'n => None' ≡ 'n => open' *)

(** Composition of concurrent statements. *)
| Cpar (cstmt : cs) (cstmt' : cs).

Notation "cstmt // cstmt'" := (Cpar cstmt cstmt') (at level 0).

(** ** Design declaration. *)

(** Generic constant declaration. *)

Inductive gdecl : Type :=
  Gen (genid : ident) (t : tind) (e : expr).

(** Architecture declarations. *)

Inductive adecl : Type :=
| Atdef (tid : ident) (t : tdef)                  (** Type definition declaration. *)
| Atind (tid : ident) (t : tind)                  (** Subtype indication declaration. *)
| Asig (sigid : ident) (t : tind)                 (** Signal declaration. *)
| Aconst (constid : ident) (t : tind) (v : expr). (** Constant declaration. *)

(** Port declarations. *)

Inductive pdecl : Type :=
| Pin (portid : ident) (t : tind)
| Pout (portid : ident) (t : tind).

(** Design declaration. *)

Inductive design : Type :=
  Design (entid : ident)       (** Entity id *)
         (archid : ident)      (** Architecture id *)
         (gens : list gdecl)   (** Generic constant list *)
         (ports : list pdecl)  (** Port list *)
         (adecls : list adecl) (** Architecture declarative part *)
         (cstmt : cs).         (** Concurrent statement part *)

Example design0 :=
  Design 0 1
         [(Gen 2 (Tid 3) (Enat 2)); (Gen 3 (Tid 3) (Enat 2))]
         [(Pin 8 (Tid 3)); (Pin 9 (Tcid 3 ((Enat 4), (Enat 9))))]
         []
         ((Cps 5 [] [] ((Ssig (Nid 0) (Enat 4));;(Ssig (Nid 0) (Enat 4))))
            // (Cps 6 [] [] (Ssig (Nid 0) (Enat 4)))
            // (Cps 7 [] [] (Ssig (Nid 0) (Enat 4)))).
