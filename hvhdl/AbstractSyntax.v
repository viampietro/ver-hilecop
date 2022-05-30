(*!============================!*)
(** *  Abstract syntax of H-VHDL    *)
(*!============================!*)

Require Import common.CoqLib.
Require Import common.GlobalTypes.
Require Import common.ListPlus.

Require Import hvhdl.HVhdlTypes.

(** Declares the scope of notations for the H-VHDL abstract syntax. *)

Declare Scope abss_scope.
Local Open Scope abss_scope.

(** Set of binary operators. *)

Inductive binop : Set :=
  bo_and | bo_or | bo_eq | bo_neq |
  bo_lt | bo_le | bo_gt | bo_ge |
  bo_add | bo_sub.

(** Set of unary operators. *)

Inductive uop : Set := uo_not.

(** ** Expressions: *)

(** An expression is either: 

    - a natural constant
    - a boolean constant
    - an identifier
    - an identifier with index (e.g "myvar(3)")
    - an aggregate, i.e a non-empty list of expressions
    - e1 binop e2
    - uop e   
 *)

Inductive expr : Type :=
| e_name : name -> expr (** Read a signal, a local variable or a
                            generic constant value *)
| e_nat : N -> expr (** Natural constant *)
| e_bool : bool -> expr (** Boolean constant *)
| e_binop : binop -> expr -> expr -> expr (** Binary operation *)
| e_uop : uop -> expr -> expr (** Unary operation *)
| e_aggreg : agofexprs -> expr (** Aggregate expression *)

(** Aggregate of expressions (non-empty list of expressions) *)

with agofexprs : Type :=
| agofe_one : expr -> agofexprs
| agofe_cons : expr -> agofexprs -> agofexprs
                    
(** Names *)
                    
with name : Type :=
| n_id : ident -> name  
| n_xid : ident -> expr -> name.

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

Coercion e_nat : N >-> expr.
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
| tind_boolean                                           (** Boolean type indication *)
| tind_natural (rlower : expr) (rupper : expr)           (** Natural with range constraint *)
| tind_array (t : tind) (ilower : expr) (iupper : expr). (** Array of [t] with index constraint *)

(** ** Sequential statements. *)

Inductive ss : Type :=
| ss_sig (signame : name) (e : expr)              (** Assignment to a signal *)
| ss_var (varname : name) (e : expr)              (** Assignment to a local variable *)
| ss_ifelse (e : expr) (stmt1 : ss) (stmt2 : ss)  (** Conditional *)
| ss_loop (id : ident) (e1 e2 : expr) (stmt : ss) (** Range loop *)
| ss_falling (stmt : ss)                          (** Falling edge block *)
| ss_rising (stmt : ss)                           (** Rising edge block *)
| ss_rst (stmt1 stmt2 : ss)                       (** Reset conditional *)
| ss_seq (stmt1 stmt2 : ss)                       (** Sequence *)
| ss_null.                                        (** No operation *)

(** Notations for sequential statements. *)

Module HVhdlSsNotations.

  Infix "@<==" := ss_sig (at level 100) : abss_scope.
  Infix "@:=" := ss_var (at level 100) : abss_scope.

  Notation "'If' c 'Then' x 'Else' y" :=
    (ss_ifelse c x y)
      (at level 200, right associativity,
        format "'[v' 'If'  c '//' 'Then'  x '//' 'Else'  y ']'") : abss_scope.

  Notation "'For' i 'InR' l 'To' u 'Loop' x " :=
    (ss_loop i l u x)
      (at level 200, format "'[v' 'For'  i  'InR'  l  'To'  u  'Loop' '/' '['   x ']' ']'") : abss_scope.

  Notation "'Rising' stmt" := (ss_rising stmt) (at level 200) : abss_scope.
  Notation "'Falling' stmt" := (ss_falling stmt) (at level 200) : abss_scope.
  Notation "'Rst' stmt1 'Else' stmt2" := (ss_rst stmt1 stmt2) (at level 200) : abss_scope.

  Notation " x ;; y ;; .. ;; z " := (ss_seq .. (ss_seq x y) .. z) (at level 100) : abss_scope.

End HVhdlSsNotations.

Import HVhdlSsNotations.

(** ** Concurrent statements. *)

(** Process local variable declaration; e.g:
    
    - Concrete syntax = "variable v : natural(0,255);"
    - Abstract syntax = "vdecl_ v (tind_natural (0,255))"

 *)

Inductive vdecl : Type :=
  vdecl_ (vid : ident) (τ : tind).

(** Generic constant association; e.g:

    - Concrete syntax = "g ⇒ 1"
    - Abstract syntax = "assocg_ g (e_nat 1)"
 *)

Inductive assocg : Type :=
  assocg_ (id : ident) (e : expr).

(** A generic map is a list of generic constant associations. *)

Definition genmap := list assocg.

(** Input port association. *)

Inductive ipassoc : Type :=
  ipa_ (n : name) (e : expr).

(** An input port map is a list of input port associations. *)

Definition inputmap := list ipassoc.

(** Output port association.

    [None] represents the [open] port keyword in the actual part of
    the output port association.

    We forbid the association of an indexed formal part with the open
    keyword, i.e: "myport(0) ⇒ open" *)

Inductive opassoc : Type :=
| opa_simpl :  ident -> option name -> opassoc
| opa_idx   : ident -> expr -> name -> opassoc. 

(** Type of output port map. *)

Definition outputmap := list opassoc.

(** Concurrent statement. *)

Inductive cs : Type :=

(** Process statement *)
| cs_ps (id__p : ident)       (** Process identifier *)
        (vars : list vdecl) (** Variable declaration list *)
        (body : ss)         (** Sequential statement block *)
      
(** Design instantiation statement *)
| cs_comp (id__c : ident)   (** Design instance identifier *)
          (id__e : ident)   (** Design entity identifier *)
          (g : genmap)    (** Generic map *)
          (i : inputmap)  (** Input port map *)
          (o : outputmap) (** Output port map *)

(** Parallel composition *)
| cs_par (cstmt1 cstmt2 : cs)

(** No operation *)
| cs_null.

Module HVhdlCsNotations.

  Notation " x // y // .. // z " := (cs_par .. (cs_par x y) .. z)
                                      (right associativity, at level 100) : abss_scope.
  Notation "id__p ':' 'Process' vars 'Begin' stmt" :=
    (cs_ps id__p vars stmt)
      (at level 200(* , *)
       (* format "'[v' id__p  ':'  'Process'  sl '/' '['   vars ']' '/' 'Begin' '/' '['   stmt ']' ']'" *)) : abss_scope.

  Notation "id__p ':' 'Process' 'Begin' stmt" :=
    (cs_ps id__p [] stmt)
      (at level 200(* , *)
       (* format "'[v' id__p  ':'  'Process'  sl '/' 'Begin' '/' '['   stmt ']' ']'" *)) : abss_scope.
  
End HVhdlCsNotations.

Import HVhdlCsNotations.

(** ** Design declaration. *)

(** Generic constant declaration *)

Inductive gdecl : Type :=
  gdecl_ (id : ident) (τ : tind) (e : expr).
                                   
(** Port declarations *)

Inductive pdecl : Type :=
| pdecl_in (id : ident) (τ : tind)  (** Declaration of an input port *)
| pdecl_out (id : ident) (τ : tind). (** Declaration of an output port *)
            
(** Internal signal declaration *)

Inductive sdecl : Type :=
  sdecl_ (id : ident) (τ : tind).

(** Design declaration, i.e the entity-architecture couple; e.g:
    
    - Concrete syntax =

    "entity [id__e] is [gens]; [ports]; end [id__e];
    
     architecture [id__a] of [id__e] is 
       [sigs]; 
     begin 
       [behavior] 
     end [id__a];" 

   - Abstract syntax = "[design_ gens ports sigs behavior]"

*)

Record design : Type :=
  design_ {
      gens  : list gdecl; (** Generic constants *)
      ports : list pdecl; (** Input and output ports *)
      sigs  : list sdecl; (** Internal signals *)
      beh   : cs          (** Design behavior *)
    }.

(** ** Misc. Definitions for the H-VHDL Abstract Syntax *)

(** CS version of the [FoldL] relation.  *)

Inductive FoldLCs {A : Type} (f : A -> cs -> A) : cs -> A -> A -> Prop :=
| FoldLCs_null : forall a, FoldLCs f cs_null a (f a cs_null)
| FoldLCs_ps :
  forall id__p vars body a,
    FoldLCs f (cs_ps id__p vars body) a (f a (cs_ps id__p vars body))
| FoldLCs_comp :
  forall id__c id__e gm ipm opm a,
    FoldLCs f (cs_comp id__c id__e gm ipm opm) a (f a (cs_comp id__c id__e gm ipm opm))
|FoldLCs_par :
  forall cstmt cstmt' a a' a'' ,
    FoldLCs f cstmt a a' -> FoldLCs f cstmt' a' a'' -> FoldLCs f (cstmt // cstmt') a a''.

#[export]
Hint Constructors FoldLCs : core.

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
    forall id__p vars body,
      FlattenCs (cs_ps id__p vars body) [cs_ps id__p vars body]
| FlattenCs_ps_hd :
    forall id__p vars body cstmt l,
      FlattenCs cstmt l ->
      FlattenCs ((cs_ps id__p vars body) // cstmt) ((cs_ps id__p vars body) :: l)
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

#[export]
Hint Constructors FlattenCs : core.

Definition cs_to_list (cstmt : cs) : list cs :=
  let add_to_list := fun (l :list cs) (cstmt0 : cs) => l ++ [cstmt0] in
  foldl_cs add_to_list cstmt [].

(** States that a given simple [cs] (i.e, not [cs_par]) is a part of a another [cs]. *)

Fixpoint InCs (cstmt cstmt' : cs) {struct cstmt'} : Prop :=
  match cstmt' with
  | cs_null | cs_ps _ _ _ | cs_comp _ _ _ _ _ => cstmt = cstmt'
  | cstmt1 // cstmt2 =>
    InCs cstmt cstmt1 \/ InCs cstmt cstmt2
  end.

(** ** H-VHDL Design Declarative Part Identifiers *)

Definition AreGenIds (gens : list gdecl) (genids : list ident) : Prop :=
  let gdecl2id := (fun gd : gdecl => let '(gdecl_ id τ e) := gd in id) in
  Map gdecl2id gens genids.

Definition ArePortIds (ports : list pdecl) (portids : list ident) : Prop :=
  let pdecl2id := fun pd => match pd with pdecl_in id _ | pdecl_out id _ => id end in
  Map pdecl2id ports portids.

Definition AreSigIds (sigs : list sdecl) (sigids : list ident) : Prop :=
  Map (fun sd : sdecl => let '(sdecl_ id _) := sd in id) sigs sigids.

(** ** H-VHDL Design Behavioral Part Identifiers *)

Definition AreCsCompIds (cstmt : cs) (compids : list ident) : Prop :=
  let comp2id := fun cids cstmt => match cstmt with cs_comp id _ _ _ _ => cids ++ [id] | _ => cids end in
  FoldLCs comp2id cstmt [] compids.

Definition get_cids (cstmt : cs) : list ident :=
  let comp2id := fun cids cstmt => match cstmt with cs_comp id _ _ _ _ => cids ++ [id] | _ => cids end in
  foldl_cs comp2id cstmt [].

Definition AreCsPIds (cstmt : cs) (pids : list ident) : Prop :=
  let ps2id := fun psids cstmt => match cstmt with cs_ps id _ _ => psids ++ [id] | _ => psids end in
  FoldLCs ps2id cstmt [] pids.

Definition AreDeclPartIds (d : design) (genids portids sigids : list ident) : Prop :=
  AreGenIds (gens d) genids
  /\ ArePortIds (ports d) portids
  /\ AreSigIds (sigs d) sigids.

Definition AreBehPartIds (d : design) (compids pids : list ident) : Prop :=
  AreCsCompIds (beh d) compids /\ AreCsPIds (beh d) pids.

Definition AreVarIds (vars : list vdecl) (varids : list ident) : Prop :=
  let var2id := (fun vd : vdecl => let '(vdecl_ id _) := vd in id) in
  Map var2id vars varids.



