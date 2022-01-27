(*!============================!*)
(** *  Abstract syntax of H-VHDL    *)
(*!============================!*)

Require Import CoqLib.
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
| ss_rst (stmt : ss) (stmt' : ss)                         (** Reset blocks *)
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
Notation "'Rst' stmt1 'Else' stmt2" := (ss_rst stmt1 stmt2) (at level 200) : abss_scope.

Notation " x ;; y ;; .. ;; z " := (ss_seq .. (ss_seq x y) .. z) (at level 100) : abss_scope.

(** ** Concurrent statements. *)

(** Process local variable declaration; e.g:
    
    - Concrete syntax = "variable v : natural(0,255);"
    - Abstract syntax = "vdecl_ v (tind_natural (0,255))"

 *)

Inductive vdecl : Type :=
  vdecl_ (vid : ident) (τ : tind).

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
| cs_ps (id__p : ident)       (** Process id *)
        (sl : IdSet)        (** Sensitivity list *)
        (vars : list vdecl) (** Variable declaration list *)
        (stmt : ss)         (** Sequential statement block *)
      
(** Component instantiation statement. *)
| cs_comp (id__c : ident)   (** Component id *)
          (id__e : ident)   (** Instantiated design label *)
          (g : genmap)    (** Generic map *)
          (i : inputmap)  (** In port map *)
          (o : outputmap) (** Out port map *)

(** Composition of concurrent statements. *)
| cs_par (cstmt : cs) (cstmt' : cs)

(** Null statement *)
| cs_null.

Module HVhdlCsNotations.

  Notation " x // y // .. // z " := (cs_par .. (cs_par x y) .. z)
                                      (right associativity, at level 100) : abss_scope.
  Notation "id__p ':' 'Process' sl vars 'Begin' stmt" :=
    (cs_ps id__p sl vars stmt)
      (at level 200(* , *)
       (* format "'[v' id__p  ':'  'Process'  sl '/' '['   vars ']' '/' 'Begin' '/' '['   stmt ']' ']'" *)) : abss_scope.

  Notation "id__p ':' 'Process' sl 'Begin' stmt" :=
    (cs_ps id__p sl [] stmt)
      (at level 200(* , *)
       (* format "'[v' id__p  ':'  'Process'  sl '/' 'Begin' '/' '['   stmt ']' ']'" *)) : abss_scope.
  
End HVhdlCsNotations.

Import HVhdlCsNotations.

(** ** Design declaration. *)

(** Generic constant declaration. *)

Inductive gdecl : Type :=
  gdecl_ (genid : ident) (τ : tind) (e : expr).
                                   
(** Port declarations. *)

Inductive pdecl : Type :=
| pdecl_in (portid : ident) (τ : tind)  (** Declaration of port in "in" mode. *)
| pdecl_out (portid : ident) (τ : tind). (** Declaration of port in "out" mode. *)
            
(** Signal declaration. *)

Inductive sdecl : Type :=
  sdecl_ (sigid : ident) (τ : tind).

(** Design declaration, i.e the entity-architecture couple; e.g:
    
    - Concrete syntax =

    "entity [id__e] is [gens]; [ports]; end [id__e];
    
     architecture [id__a] of [id__e] is 
       [sigs]; 
     begin 
       [behavior] 
     end [id__a];" 

   - Abstract syntax = "[design_ id__e id__a gens ports sigs behavior]"

*)

Record design : Type :=
  design_ {
      id__e      : ident;      (** Entity id *)
      id__a      : ident;      (** Architecture id *)
      gens     : list gdecl; (** Generic constant clause *)
      ports    : list pdecl; (** Port clause *)
      sigs     : list sdecl; (** Architecture declarative part *)
      behavior : cs
    }.

(** ** Misc. Definitions for the H-VHDL Abstract Syntax *)

(** CS version of the [FoldL] relation.  *)

Inductive FoldLCs {A : Type} (f : A -> cs -> A) : cs -> A -> A -> Prop :=
| FoldLCs_null : forall a, FoldLCs f cs_null a (f a cs_null)
| FoldLCs_ps :
  forall id__p sl vars body a,
    FoldLCs f (cs_ps id__p sl vars body) a (f a (cs_ps id__p sl vars body))
| FoldLCs_comp :
  forall id__c id__e gm ipm opm a,
    FoldLCs f (cs_comp id__c id__e gm ipm opm) a (f a (cs_comp id__c id__e gm ipm opm))
|FoldLCs_par :
  forall cstmt cstmt' a a' a'' ,
    FoldLCs f cstmt a a' -> FoldLCs f cstmt' a' a'' -> FoldLCs f (cstmt // cstmt') a a''.

#[export] Hint Constructors FoldLCs : core.

Fixpoint foldl_cs {A : Type} (f : A -> cs -> A) (cstmt : cs) (acc : A) {struct cstmt} : A :=
  match cstmt with
  | cstmt0 // cstmt1 => foldl_cs f cstmt1 (foldl_cs f cstmt0 acc) 
  | _ => f acc cstmt
  end.

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
| FlattenCs_cons :
   forall cstmt cstmt' l l',
     FlattenCs cstmt l -> FlattenCs cstmt' l' -> FlattenCs (cstmt // cstmt') (l ++ l').

#[export] Hint Constructors FlattenCs : core.

Fixpoint cs_to_list (cstmt : cs) {struct cstmt} : list cs :=
  let add_to_list := fun (l :list cs) (cstmt0 : cs) => l ++ [cstmt0] in
  foldl_cs add_to_list cstmt [].

(** States that a given simple [cs] (i.e, not [cs_par]) is a part of a another [cs]. *)

Fixpoint InCs (cstmt cstmt' : cs) {struct cstmt'} : Prop :=
  match cstmt' with
  | cs_null | cs_ps _ _ _ _ | cs_comp _ _ _ _ _ => cstmt = cstmt'
  | cstmt1 // cstmt2 =>
    InCs cstmt cstmt1 \/ InCs cstmt cstmt2
  end.

(** ** Signal Assignment Look-up *)

Fixpoint AssignedInOPM (id : ident) (opm : outputmap) :=
  match opm with
  | [] => False
  | (assocop_simpl _ (Some (n_id id__a | n_xid id__a _)) | assocop_idx _ _ (n_id id__a | n_xid id__a _)) :: tl =>
    id = id__a \/ AssignedInOPM id tl
  | (assocop_simpl _ None) :: tl => AssignedInOPM id tl
  end.

Fixpoint AssignedInSS (id : ident) (stmt : ss) :=
  match stmt with
  | ss_sig ((n_id id__s) | (n_xid id__s _)) _ => id = id__s
  | (ss_if _ stmt1 | ss_loop _ _ _ stmt1 | ss_falling stmt1 | ss_rising stmt1) =>
    AssignedInSS id stmt1
  | (ss_ifelse _ stmt1 stmt2 | ss_rst stmt1 stmt2 | ss_seq stmt1 stmt2) =>
    AssignedInSS id stmt1 \/ AssignedInSS id stmt2
  | _ => False
  end.

Fixpoint AssignedInCs (id : ident) (cstmt : cs) :=
  match cstmt with
  | cs_comp id__c id__e gm ipm opm => AssignedInOPM id opm
  | cs_ps id__p sl vars body => AssignedInSS id body
  | cs_null => False
  | cs_par cstmt' cstmt'' =>
    AssignedInCs id cstmt' \/ AssignedInCs id cstmt''
  end.
