Require Import Arith.
Require Import Ascii.
Require Import Nat.
Require Import Bool.
Require Import Coq.Strings.Byte.
Require Import Strings.String.
Scheme Equality for string.
Local Open Scope string_scope.
 

(* Tipul de date Nat *)
 
Inductive Nat : Type :=
| TypeNat : nat -> Nat
| ErrorNat : Nat. 

Scheme Equality for Nat.


(* Tipul de date Bool *)

Inductive Bool : Type :=
| TypeBool : bool -> Bool
| ErrorBool : Bool.




(* Tipul de date String *)

Inductive String : Type :=
| TypeString : string -> String
| ErrorString : String.




Coercion TypeNat : nat >-> Nat.
Coercion TypeBool : bool >-> Bool.
Coercion TypeString : string >->String.




(* Tipul list *)

Inductive list (T : Type) : Type :=
| nil
| cons (t : T) (l : list T).


Check cons Nat 4 (cons Nat 3 (nil Nat)).
Check cons Bool false (cons Bool true (nil Bool)).


Arguments nil {T}.
Notation "[]" := nil.
Notation "{ X , .. , Y }" := (cons Nat X .. (cons Nat Y []) ..).
Notation "{ X ; .. ; Y }" := (cons Bool X .. (cons Bool Y []) ..).
Notation "{ X ;;; .. ;;; Y }" := (cons String X .. (cons String Y []) ..).


Check {1, 2, 3}.
Check {false; true; true; false}.

Definition list1nat := {1, 3, 5, 7, 9}.
Definition list2nat := {2, 4, 6, 8, 10, 12, 14}.
Definition list3nat := {10, 20}.
Definition list1bool := {true; false; true; false; false}.
Definition list2bool := {true; false; true; false; false; true; false}.
Definition list1string := { "ioan" ;;; "ioana" ;;; "dan"}.
Definition list2string := { "baiat" ;;; "fata" ;;; "baiat" }.




(* Tipul array *)

Inductive Array : Type :=
| NatArray : list Nat -> Array
| BoolArray : list Bool -> Array
| StringArray : list String -> Array
| Matrix : list Array -> Array.


Check NatArray list1nat.
Check BoolArray list1bool.


Notation "{ X & .. & Y }" := (cons Array X .. (cons Array Y []) ..).
Notation "'[Natural]' = L " := (NatArray L) (at level 80).
Notation "'[Boolean]' = L " := (BoolArray L) (at level 80).
Notation "'[String]' = L " := (StringArray L) (at level 80).
Notation "'[[Matrix]]' = L" := (Matrix L) (at level 20).

Check Matrix { (NatArray list1nat) & (NatArray list2nat) }.

Definition vector_nat := [Natural] = list1nat.
Definition vector_bool := [Boolean] = list1bool.
Definition vector_string := [String] = list1string.
Definition matrix_both := [[Matrix]] = { vector_nat & vector_bool }.


Compute vector_nat.
Compute vector_bool.
Compute vector_string.




(* Tipuri acceptate pentru struct *)

Inductive types_allowed : Type :=
| natural (n : Nat)
| boolean (b : Bool)
| stringg (s : String)
| arr (v : Array)
| inexistent.


Coercion  natural : Nat >-> types_allowed.
Coercion boolean : Bool >-> types_allowed.
Coercion arr : Array >-> types_allowed.
Coercion stringg : String >-> types_allowed.

Check 7 : types_allowed.
Check false : types_allowed.




(* Perechi pentru struct *)

Inductive pair_struct : Type :=
| pair (first : string) (second : types_allowed). 

Notation "( N , V )" := (pair N V).
Notation "{ P1 ;; .. ;; P2 }" := (cons pair_struct P1 .. (cons pair_struct P2 []) ..). 


(* Tipul struct *)

Inductive Struct : Type :=
| struct_cons ( struct_pairs : list pair_struct).




(* Tipul map *)


Inductive MapTypes :=
| natstring (kn : list Nat) (vs : list String)
| stringnat (ks : list String) (vn : list Nat)
| natnat (kn : list Nat) (vn : list Nat)
| stringstring (ks : list String) (vs : list String).

Definition map1 := natnat list1nat list1nat.
Definition map2 := natstring list3nat list1string.





(* Tipurile de date *)

Inductive Types : Type := 
| Nats (n : Nat)
| Bools (b : Bool)
| Strings (s: String)
| undeclared : Types
| unassignedNat : Types
| unassignedBool : Types
| unassignedString : Types
| unassignedArray : Types
| unassignedStruct : Types
| unassignedMap : Types
| Arrays (v : Array)
| Structs (s : Struct)
| Maps (m : MapTypes)
| Error.




Definition Env := string -> Types.
Coercion Nats : Nat >-> Types.
Coercion Bools : Bool >-> Types.
Coercion Strings : String >-> Types.
Coercion Arrays : Array >-> Types.
Coercion Maps : MapTypes >-> Types.


(* Expresiile aritmetice si boolene *)

Inductive Exp :=
| anum : Nat -> Exp
| avar : string -> Exp
| str : String -> Exp
| aplus : Exp -> Exp -> Exp
| aminus : Exp -> Exp -> Exp
| amul : Exp -> Exp -> Exp
| adiv : Exp -> Exp -> Exp
| amod : Exp -> Exp -> Exp
| btrue : Exp
| bfalse : Exp
| not' : Exp -> Exp
| and' : Exp -> Exp -> Exp
| or' : Exp -> Exp -> Exp
| less : Exp -> Exp -> Exp
| lessequal : Exp -> Exp -> Exp
| greater : Exp -> Exp -> Exp
| greaterequal : Exp -> Exp -> Exp
| equal : Exp -> Exp -> Exp
| notequal : Exp -> Exp -> Exp.


Coercion anum : Nat >-> Exp.
Coercion avar : string >-> Exp.


(* Notatii pentru Exp *)

Notation "A +' B" := (aplus A B) (at level 60, right associativity).
Notation "A -' B" := (aminus A B) (at level 58, left associativity).
Notation "A *' B" := (amul A B) (at level 58, left associativity).
Notation "A /' B" := (adiv A B) (at level 58, left associativity).
Notation "A %' B" := (amod A B) (at level 58, left associativity).
Notation "! A" := (not' A) (at level 75, right associativity).
Notation "A &&' B" := (and' A B) (at level 40, left associativity).
Notation "A ||' B" := (or' A B) (at level 50, left associativity).
Notation "A <' B" := (less A B) (at level 70, no associativity).
Notation "A <=' B" := (lessequal A B) (at level 70, no associativity).
Notation "A >' B" := (greater A B) (at level 70, no associativity).
Notation "A >=' B" := (greaterequal A B) (at level 70, no associativity).
Notation "A ==' B" := (equal A B) (at level 70, no associativity).
Notation "A !=' B" := (notequal A B) (at level 70, no associativity).


Check 2 +' 2.
Check 2 +' btrue.
Check (and' 2 2).




(* Statement-urile *)

Inductive Stmt : Type :=
| declareNat :  string -> Stmt
| declareBool :  string -> Stmt
| declareString :  string -> Stmt

| assignmentNat : string -> Exp -> Stmt
| assignmentBool : string -> Exp -> Stmt
| assignmentString : string -> Exp -> Stmt

| initializeNat : string -> Exp -> Stmt
| initializeBool : string -> Exp -> Stmt
| initializeString : string -> Exp -> Stmt

| sequence : Stmt -> Stmt -> Stmt
| ifthenelse : Exp -> Stmt -> Stmt -> Stmt
| ifthen : Exp -> Stmt -> Stmt 
| while_loop : Exp -> Stmt -> Stmt 
| for_loop : Stmt -> Exp -> Stmt -> Stmt -> Stmt
| empty : Stmt
| switch_case : Exp -> list pairs -> Stmt

(*for Array*)
| declareArrayNat : string -> Stmt
| declareArrayBool : string -> Stmt
| declareArrayString : string -> Stmt
| declareMatrix : string -> Stmt

| initializeArrayNat : string -> Array -> Stmt
| initializeArrayBool : string -> Array -> Stmt
| initializeArrayString : string -> Array -> Stmt
| initializeMatrix : string -> Array -> Stmt

| setElemArrayNat : string -> nat -> Nat -> Stmt
| setElemArrayBool : string -> nat -> Bool -> Stmt
| setElemArrayString : string -> nat -> String -> Stmt
| setElemMatrix : string -> nat -> Array -> Stmt

| pushNat : string -> Nat -> Stmt
| pushBool : string -> Bool -> Stmt
| pushString : string -> String -> Stmt
| pushMatrix : string -> Array -> Stmt 

(*for Struct*)
| declareStruct : string -> Struct -> Stmt
| set_element_struct : string -> string -> types_allowed -> Stmt

(*for Map*)
| declareMap_nn : string -> MapTypes -> Stmt
| declareMap_ns : string -> MapTypes -> Stmt
| declareMap_sn : string -> MapTypes -> Stmt
| declareMap_ss : string -> MapTypes -> Stmt
| addToMap_nn : string -> Nat -> Nat -> Stmt
| addToMap_ns : string -> Nat -> String -> Stmt
| addToMap_sn : string -> String -> Nat -> Stmt
| addToMap_ss : string -> String -> String -> Stmt

with pairs : Type :=
| pair_default : Stmt -> pairs (*cazul implicit al switch-ului*)
| pair_other : Nat -> Stmt -> pairs.



(* Notatii pentru Stmt *)
 
Notation "'natural' S" := (declareNat S) (at level 79).
Notation "'boolean' S" := (declareBool S) (at level 79).
Notation "'char' S" := (declareString S) (at level 79).

Notation "S :n= E" := (assignmentNat S E) (at level 80).
Notation "S :b= E" := (assignmentBool S E) (at level 80).
Notation "S :s= E" := (assignmentString S E) (at level 80).

Notation "'Natural' S ::= E" := (initializeNat S E) (at level 79).
Notation "'Boolean' S ::= E" := (initializeBool S E) (at level 79).
Notation "'Char' S ::= E" := (initializeString S E) (at level 79).

Notation "S1 ;s; S2" := (sequence S1 S2 ) (at level 90).
Notation "'If' ( B ) 'Then' ( S1 ) 'Else' ( S2 ) 'EndIte'" := (ifthenelse B S1 S2) (at level 55).
Notation "'If' ( B ) 'Then' [ S ] 'EndI'" := (ifthen B S ) (at level 50).
Notation "'While' ( B ) [ S ] 'EndW'" := (while_loop B S) (at level 50).
Notation "'For' '(/' S1 ';f;' B ';f;' S2 '\)' '{/' S3 '\}'  'EndF'" := (for_loop S1 B S2 S3) (at level 50).

Notation "'default:{' S };" := (pair_default S) (at level 96).
Notation "'case(' E ):{ S };" := (pair_other E S) (at level 96).
Notation "switch( E ){ P1 ;sw; .. ;sw; Pn '}end'" := (switch_case E (cons pairs P1 .. (cons pairs Pn []) ..)) (at level 97).

Notation "[Natural] V" := (declareArrayNat V) (at level 79).
Notation "[Boolean] V" := (declareArrayBool V) (at level 79).
Notation "[String] V" := (declareArrayString V) (at level 79).
Notation "[[Matrix]] V" := (declareMatrix V) (at level 79).

Notation "[Natural_I] V :in:= L" := (initializeArrayNat V L) (at level 77).
Notation "[Boolean_I] V :ib:= L" := (initializeArrayBool V L) (at level 77).
Notation "[String_I] V :is:= L" := (initializeArrayString V L) (at level 77).
Notation "[[Matrix_I]] V :im:= L" := (initializeMatrix V L) (at level 77).

Notation "V [ P ] :n= L" := (setElemArrayNat V P L) (at level 78). 
Notation "V [ P ] :b= L" := (setElemArrayBool V P L) (at level 78). 
Notation "V [ P ] :s= L" := (setElemArrayString V P L) (at level 78). 
Notation "V [ P ] :m= L" := (setElemMatrix V P L) (at level 78). 

Notation "push_n( V ) X" := (pushNat V X) (at level 79).
Notation "push_b( V ) X" := (pushBool V X) (at level 79).
Notation "push_s( V ) X" := (pushString V X) (at level 79).
Notation "push_m( V ) X" := (pushMatrix V X) (at level 79).

Notation "struct( N ) L" := (declareStruct N L) (at level 79).
Notation "'setS' N '[(' F ')]' := V" := (set_element_struct N F V) (at level 79).

Notation "'Map' M :nn= L" := (declareMap_nn M L) (at level 79).
Notation "'Map' M :ns= L" := (declareMap_ns M L) (at level 79).
Notation "'Map' M :sn= L" := (declareMap_sn M L) (at level 79).
Notation "'Map' M :ss= L" := (declareMap_ss M L) (at level 79).
Notation "'add_nn' M '<-' K ':|:' V " := (addToMap_nn M K V) (at level 79).
Notation "'add_ns' M '<-' K ':|:' V" := (addToMap_ns M K V) (at level 79).
Notation "'add_sn' M '<-' K ':|:' V" := (addToMap_sn M K V) (at level 79).
Notation "'add_ss' M '<-' K ':|:' V" := (addToMap_ss M K V) (at level 79).




Notation "{ P1 ;sw; .. ;sw; Pn }" := (cons pairs P1 .. (cons pairs Pn []) ..).


(* Definirea unor enviroment-uri *)


Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.
  
Definition update (env : Env)
           (x : string) (v : Types) : Env :=
  fun y => if (eqb_string y x)
           then v
           else (env y).
           
Definition all (x : Types) : Env :=
  (fun _ => x).

Definition default := all undeclared.

Definition default_zero (s : string) := update default s 0.
Check false. 
Definition default_false (s : string) := update default s false.
  
Definition env1 := update default "v1" 1.
Definition env2 := update default "v2" true.

Check "v1".
Compute env2 "v2" .




(* Definirea operatiilor pentru elemente de tipul Types *)


Definition types_plus (x y : Types) :=
match x, y with
| TypeNat x, TypeNat y => TypeNat(x + y)
| TypeBool x, TypeBool y => match x, y with
                    | true, true => TypeNat 2
                    | false, false => TypeNat 0
                    | _, _ => TypeNat 1
                    end
| TypeNat x, TypeBool y => match y with
                   | true => TypeNat (x + 1)
                   | false => TypeNat (x + 0)
                   end
| TypeBool x, TypeNat y => match x with
                   | true => TypeNat (1 + y)
                   | false => TypeNat (0 + y)
                   end 
| _, _ => ErrorNat
end. 


(* plus *)
(*
Definition types_plus (x y : Types) : Types :=
  match x, y with
    | Nats (TypeNat a), Nats (TypeNat b) => Nats (TypeNat (a + b))
    | _, _ => Nats (ErrorNat)
  end.

Compute (types_plus (Nats 8) (Nats 8)).*)

(* minus *)

Definition types_minus (x y : Types) :=
match x, y with
| TypeNat x, TypeNat y => TypeNat(x - y)
| TypeBool x, TypeBool y => match x, y with
                    | true, false => TypeNat 1
                    | _, _ => TypeNat 0
                    end
| TypeNat x, TypeBool y => match y with
                   | true => TypeNat (x - 1)
                   | false => TypeNat x
                   end
| TypeBool x, TypeNat y => match x with
                   | true => TypeNat (1 - y)
                   | false => TypeNat (0 - y)
                   end 
| _, _ => ErrorNat
end. 

Check (types_minus true false).
Compute (types_minus true true).
Compute (types_minus 8 false).
Compute (types_minus 8 true).
Compute (types_minus 10 8).
Compute (types_minus false 2).
Compute (types_minus true 0).




(* inmultire *)

Definition types_mul (x y : Types) :=
match x, y with
| TypeNat x, TypeNat y => TypeNat(x * y)
| TypeBool x, TypeBool y => match x, y with
                    | true, true => TypeNat 1
                    | _, _ => TypeNat 0
                    end
| TypeNat x, TypeBool y => match y with
                   | true => TypeNat x
                   | false => TypeNat 0
                   end
| TypeBool x, TypeNat y => match x with
                   | true => TypeNat y
                   | false => TypeNat 0
                   end 
| _, _ => ErrorNat
end.

Compute (types_mul 4 2).
Compute (types_mul 4 true). 
Compute (types_mul 4 false).
Compute (types_mul true true).
Compute (types_mul false true).




(* impartire *)

Definition types_div (x y : Types) :=
match x, y with
| TypeNat x, TypeNat y => match y with
                          | 0 => ErrorNat
                          | _ => TypeNat(div x y)
                          end
| TypeBool x, TypeBool y => match x, y with
                            | true, true => TypeNat 1
                            | false, true => TypeNat 0
                            | _, _ => ErrorNat
                            end
| TypeNat x, TypeBool y => match y with
                           | true => TypeNat x
                           | false => ErrorNat
                           end
| TypeBool x, TypeNat y => match x, y with
                           | _, 0 => ErrorNat
                           | true, _ => TypeNat (div 1 y)
                           | false, _ => TypeNat 0
                           end 
| _, _ => ErrorNat
end.

Compute (types_div 8 4).
Compute (types_div 8 0).
Compute (types_div 8 true).
Compute (types_div 8 false).
Compute (types_div true true).
Compute (types_div false true).




(* mod *)

Definition types_mod (x y : Types) :=
match x, y with
| TypeNat x, TypeNat y => match y with
                          | 0 => ErrorNat
                          | _ => TypeNat(modulo x y)
                          end
| TypeBool x, TypeBool y => match x, y with
                            | true, true => TypeNat 0
                            | false, true => TypeNat 0
                            | _, _ => ErrorNat
                            end
| TypeNat x, TypeBool y => match y with
                           | true => TypeNat 0
                           | false => ErrorNat
                           end
| TypeBool x, TypeNat y => match x, y with
                           | _, 0 => ErrorNat
                           | true, _ => TypeNat (modulo 1 y)
                           | false, _ => TypeNat 0
                           end 
| _, _ => ErrorNat
end.

Compute (types_mod 8 4).
Compute (types_mod 8 3).
Compute (types_mod 8 false).
Compute (types_mod 8 true).
Compute (types_mod true 4).




(*not*)

Definition types_not (x : Types) :=
match x with
| TypeNat x => match x with
               | 0 => TypeBool true
               | _ => TypeBool false
               end
| TypeBool x => match x with
               | true => TypeBool false
               | false => TypeBool true
               end
| _ => ErrorBool
end.

Compute(types_not true).
Compute(types_not false).
Compute(types_not 5).
Compute(types_not 0).




(* and *)

Definition types_and (x y : Types) :=
match x, y with
| TypeNat x, TypeNat y => match x, y with
                          | _, 0 => TypeBool false
                          | 0, _ => TypeBool false
                          | _, _ => TypeBool true
                          end
| TypeBool x, TypeBool y => match x, y with
                            | _, false => TypeBool false
                            | false, _ => TypeBool false
                            | _, _ => TypeBool true
                            end
| TypeNat x, TypeBool y => match x, y with
                           | 0, _ => TypeBool false
                           | _, false => TypeBool false
                           | _, _ => TypeBool true
                           end
| TypeBool x, TypeNat y => match x, y with
                           | false, _ => TypeBool false
                           | _, 0 => TypeBool false
                           | _, _ => TypeBool true
                           end 
| _, _ => ErrorBool
end.

Compute (types_and 3 5).
Compute (types_and true false).
Compute (types_and 0 true).
Compute (types_and true true).




(* or *)

Definition types_or (x y : Types) :=
match x, y with
| TypeNat x, TypeNat y => match x, y with
                          | 0, 0 => TypeBool false
                          | _, _ => TypeBool true
                          end
| TypeBool x, TypeBool y => match x, y with
                            | false, false => TypeBool false
                            | _, _ => TypeBool true
                            end
| TypeNat x, TypeBool y => match x, y with
                           | 0, false => TypeBool false
                           | _, _ => TypeBool true
                           end
| TypeBool x, TypeNat y => match x, y with
                           | false, 0 => TypeBool false
                           | _, _ => TypeBool true
                           end 
| _, _ => ErrorBool
end.

Compute (types_or true 8).
Compute (types_or 0 false).
Compute (types_or 6 0).
Compute (types_or true false).




(* mai mic < *)

Definition types_less (x y : Types) :=
match x, y with
| TypeNat x, TypeNat y => TypeBool (ltb x y)
| TypeBool x, TypeBool y => match x, y with
                            | false, true => TypeBool true
                            | _, _ => TypeBool false
                            end
| TypeNat x, TypeBool y => match x, y with
                           | 0, true => TypeBool true
                           | _, _ => TypeBool false
                           end
| TypeBool x, TypeNat y => match x, y with
                           | false, 0 => TypeBool false
                           | true, 0 => TypeBool false
                           | true, 1 => TypeBool false
                           | _, _ => TypeBool true
                           end 
| _, _ => ErrorBool
end.

Compute (types_less 4 7).
Compute (types_less 4 3).
Compute (types_less true 7). 
Compute (types_less 4 true).
Compute (types_less false true).
Compute (types_less true true).




(* mai mic egal <= *)

Definition types_lessequal (x y : Types) :=
match x, y with
| TypeNat x, TypeNat y => TypeBool (Nat.leb x y)
| TypeBool x, TypeBool y => match x, y with
                            | false, _ => TypeBool true
                            | true, true => TypeBool true
                            | _, _ => TypeBool false
                            end
| TypeNat x, TypeBool y => match x, y with
                           | 0, _ => TypeBool true
                           | 1, true => TypeBool true
                           | _, _ => TypeBool false
                           end
| TypeBool x, TypeNat y => match x, y with
                           | true, 0 => TypeBool false
                           | _, _ => TypeBool true
                           end 
| _, _ => ErrorBool
end.

Compute (types_lessequal 4 7).
Compute (types_lessequal 4 3).
Compute (types_lessequal true 7). 
Compute (types_lessequal 4 true).
Compute (types_lessequal false true).
Compute (types_lessequal true true).




(* mai mare > *)

Definition types_greater (x y : Types) := types_not (types_lessequal x y). 

Compute (types_greater 6 4).
Compute (types_greater 4 6).




(* mai mare egal >= *)

Definition types_greaterequal (x y : Types) := types_not (types_less x y). 

Compute (types_greaterequal 6 4).
Compute (types_greaterequal 4 4).




(* egal = *)

Definition types_equal (x y : Types) :=
match x, y with
| TypeNat x, TypeNat y => TypeBool (Nat.eqb x y)
| TypeBool x, TypeBool y => match x, y with
                            | false, false => TypeBool true
                            | true, true => TypeBool true
                            | _, _ => TypeBool false
                            end
| TypeNat x, TypeBool y => match x, y with
                           | 0, false => TypeBool true
                           | 1, true => TypeBool true
                           | _, _ => TypeBool false
                           end
| TypeBool x, TypeNat y => match x, y with
                           | true, 1 => TypeBool true
                           | false, 0 => TypeBool true
                           | _, _ => TypeBool false
                           end
| TypeString x, TypeString y => TypeBool (string_beq x y) 
| _, _ => ErrorBool
end.

Compute (types_equal 5 5).
Compute (types_equal true true).
Compute (types_equal true false).
Compute (types_equal true 1).
Compute (types_equal true 5).




(* inegal !=*)

Definition types_notequal (x y : Types) := types_not (types_equal x y). 

Compute (types_notequal true true).
Compute (types_notequal true false).
Compute (types_notequal true 1).
Compute (types_notequal true 5).




Definition isTrue (b: Bool) : bool :=
match b with
| TypeBool true => true
| TypeBool false => false
| ErrorBool => false
end.

Definition verify (e: Types) : bool :=
match e with
| Bools b => match b with
             | TypeBool b' => isTrue(b')
             | _ => false
             end
| _ => false
end.




Fixpoint Eval (exp : Exp) (env : Env) : Types :=
match exp with
| anum x => x
| avar x => env x
| str x => x
| aplus x y => types_plus (Eval x env) (Eval y env)
| aminus x y => types_minus (Eval x env) (Eval y env)
| amul x y => types_mul (Eval x env) (Eval y env)
| adiv x y => types_div (Eval x env) (Eval y env)
| amod x y => types_mod (Eval x env) (Eval y env)
| btrue => true
| bfalse => false
| not' x => types_not (Eval x env)
| and' x y => types_and (Eval x env) (Eval y env)
| or' x y => types_or (Eval x env) (Eval y env) 
| less x y => types_less (Eval x env) (Eval y env)
| lessequal x y => types_lessequal (Eval x env) (Eval y env)
| greater x y => types_greater (Eval x env) (Eval y env)
| greaterequal x y => types_greaterequal (Eval x env) (Eval y env)
| equal x y => types_equal (Eval x env) (Eval y env)
| notequal x y => types_notequal (Eval x env) (Eval y env)
end.


Compute (Eval (equal (anum 9) (anum 1)) env1).

(* Functii pentru liste *)


(* lungimea unei liste *)

Fixpoint get_list_length {T : Type} (l : list T) :=
match l with 
| nil => 0
| cons _ val l2 => 1 + get_list_length l2
end.

Compute get_list_length list1nat.
Compute get_list_length list2bool.




(* get element dintr-o lista *)

Fixpoint get_element_list_nat (l : list Nat) ( poz : nat ) :=
match l with
| nil => Error
| cons _ val l2 => if(Nat.eqb poz 0)
                   then val
                    else
                    get_element_list_nat l2 (poz-1)
end.


Fixpoint get_element_list_bool (l : list Bool) (poz : nat) :=
match l with
| nil => Error
| cons _ val l2 => if(Nat.eqb poz 0)
                   then val
                    else
                    get_element_list_bool l2 (poz-1)
end.


Fixpoint get_element_list_string (l : list String) (poz : nat) :=
match l with
| nil => Error
| cons _ val l2 => if(Nat.eqb poz 0)
                   then val
                    else
                    get_element_list_string l2 (poz-1)
end.


Fixpoint get_element_list_array (l : list Array) (poz : nat) :=
match l with
| nil => Error
| cons _ val l2 => if(Nat.eqb poz 0)
                   then val
                    else
                    get_element_list_array l2 (poz-1)
end.

Compute get_element_list_nat list1nat 1.
Compute get_element_list_bool list1bool 3.




(* set element intr-o lista *)

Fixpoint set_element_list_nat (l : list Nat) (poz : nat) (val : Nat) :=
match l with
| nil => if (Nat.eqb poz 0)
         then (cons _ val [])
         else nil
| cons _ v l2 => if ( Nat.eqb poz 0 )
                    then (cons _ val l2)
                    else cons _ v (set_element_list_nat l2 (poz-1) val)
end.

Compute set_element_list_nat {1,2,3,4} 4 5.


Fixpoint set_element_list_bool (l : list Bool) (poz : nat) (val : Bool) :=
match l with
| nil => if (Nat.eqb poz 0)
         then (cons _ val [])
         else nil
| cons _ v l2 => if ( Nat.eqb poz 0 )
                    then (cons _ val l2)
                    else cons _ v (set_element_list_bool l2 (poz-1) val)
end.


Fixpoint set_element_list_string (l : list String) (poz : nat) (val : String) :=
match l with
| nil => if (Nat.eqb poz 0)
         then (cons _ val [])
         else nil
| cons _ v l2 => if ( Nat.eqb poz 0 )
                    then (cons _ val l2)
                    else cons _ v (set_element_list_string l2 (poz-1) val)
end.


Fixpoint set_element_list_array (l : list Array) (poz : nat) (val : Array) :=
match l with
| nil => if (Nat.eqb poz 0)
         then (cons _ val [])
         else nil
| cons _ v l2 => if ( Nat.eqb poz 0 )
                    then (cons _ val l2)
                    else cons _ v (set_element_list_array l2 (poz-1) val)
end.




(* pop dintr-o lista*)

Fixpoint pop_List {T: Type} (l: list T) :=
match l with
| cons _ l' [] => []
| cons _ v l' => cons _ v (pop_List l')
| [] => [] 
end. 




(* Functii pentru vectori *)


(* lungimea unui vector *)

Definition get_array_length (v : Array) :=
match v with
| NatArray l => get_list_length l 
| BoolArray l => get_list_length l
| StringArray l => get_list_length l
| Matrix l => get_list_length l
end.

Compute get_array_length vector_nat.




(* get pentru vector*)

Definition get_element_array (v : Array)(poz : nat) :=
match v with
| NatArray l => get_element_list_nat l poz
| BoolArray l => get_element_list_bool l poz
| StringArray l => get_element_list_string l poz
| Matrix l => get_element_list_array l poz
end.

Compute get_element_list_nat list1nat 1.
Compute get_element_array vector_nat 1.
Compute get_element_array vector_bool 2.




(* set pentru vector*)

Definition set_element_array_nat (v : Array) (poz : nat) (val : Nat) :=
match v with
| NatArray l => NatArray( set_element_list_nat l poz val )
| _ => v
end.
 
Definition set_element_array_bool (v : Array) (poz : nat) (val : Bool) :=
match v with
| BoolArray l => BoolArray ( set_element_list_bool l poz val )
| _ => v
end.

Definition set_element_array_string (v : Array) (poz : nat) (val : String) :=
match v with
| StringArray l => StringArray ( set_element_list_string l poz val )
| _ => v
end.

Definition set_element_matrix (v : Array) (poz : nat) (val : Array) :=
match v with
| Matrix l => Matrix ( set_element_list_array l poz val )
| _ => v
end.

Definition vector_nat2 := set_element_array_nat vector_nat 2 10.
Compute vector_nat2.
Definition vector_bool2 := set_element_array_bool vector_bool 1 true.
Compute vector_bool2.




(* push intr-un vector *)

Definition pushToNat (v : Array) (val : Nat) :=
match v with
| NatArray l => NatArray(set_element_list_nat l (get_list_length l) val)
| _ => v
end.

Definition pushToBool (v : Array) (val : Bool) :=
match v with
| BoolArray l => BoolArray (set_element_list_bool l (get_list_length l) val)
| _ => v
end.

Definition pushToString (v : Array) (val : String) :=
match v with
| StringArray l => StringArray (set_element_list_string l (get_list_length l) val)
| _ => v
end.

Definition pushToMatrix (v : Array) (val : Array) :=
match v with
| Matrix l => Matrix (set_element_list_array l (get_list_length l) val)
| _ => v
end.

Compute vector_nat.
Compute vector_bool.
Compute pushToNat vector_nat 50.
Compute pushToBool vector_bool true.




(* pop dintr-un vector*)

Definition popArray (v : Array) :=
match v with
| NatArray l => NatArray (pop_List l)
| BoolArray l => BoolArray (pop_List l)
| StringArray l => StringArray (pop_List l)
| Matrix l => Matrix (pop_List l)
end.

Compute vector_nat.
Compute popArray vector_nat.

Notation "pop( V )" := (popArray V) (at level 79).
Notation "length( V )" := (get_array_length V) (at level 79).

Notation "V [ P ]" := (get_element_array V P)(at level 78).
Compute vector_nat.
Compute vector_nat[2].


(* Functii pentru switch*)

Definition get_pairStmt (P : pairs) : Stmt :=
match P with
| default:{ s }; => s
| case( _ ):{ s }; => s
end.

Definition checkPair (P : pairs ) (n : Types) : bool :=
match P with
| default:{ _ }; => true
| case( a ):{ _ }; => verify (types_equal a n)
end. 

Fixpoint get_switch_case (n : Types) (l : list pairs) : Stmt :=
match n with
| TypeNat n' => match l with 
              | nil => empty
              | cons _ x l2 => if (checkPair x n) then (get_pairStmt x) else (get_switch_case n l2)
              end
| _ => empty
end.


Definition switch1 := (
      natural "x" ;s; "x" :n= 5 ;s; boolean "y" ;s;
      switch( "x" ){ 
        case( 1 ):{ empty }; ;sw;
        case( 3 ):{ "x" :n= 100 }; ;sw;
        case( 5 ):{ "x" :n= 50 }; ;sw;
        case( 7 ):{  "y" :b= btrue}; ;sw;
        default:{ "x" :n= 0 };
     }end
  
).

Definition list_switch := ( { case( 1 ):{ empty }; ;sw;
                              case( 3 ):{ "x" :n= 100 }; ;sw;
                              case( 5 ):{ "x" :n= 50 }; ;sw;
                              case( 7 ):{  "y" :b= btrue}; ;sw;
                              default:{ "x" :n= 0 };
                              } ). 
Compute get_switch_case 3 list_switch.



(* Functii pentru struct *)


(* get first dintr-o pereche de struct *)

Definition pair_get_first (p : pair_struct) :=
match p with
| pair first second => first
end.




(* get second dintr-o pereche de struct *)

Definition pair_get_second (p : pair_struct) :=
match p with
| pair first second => second
end.




(* get second dintr-o lista de perechi de struct *)
Fixpoint get_element_pairlist (l : list pair_struct) (f : string) :=
match l with
| nil => inexistent
| cons _ field l2 => if ( eqb_string f ( pair_get_first field ))
                     then pair_get_second field
                     else get_element_pairlist l2 f
end.




(* set second intr-o lista de perechi de struct pe baza first *)

Fixpoint set_element_pairlist (l : list pair_struct) (f : string) (val : types_allowed) :=
match l with
| nil => nil
| cons _ field l2 => if ( eqb_string f (pair_get_first field) )
                      then cons _ (pair (pair_get_first field) val) l2
                      else cons _ field (set_element_pairlist l2 f val)
end.




(* get pentru struct *)

Definition get_element_for_struct (str : Struct) (field : string) :=
match str with
| struct_cons list_pair => get_element_pairlist list_pair field
end.




(* set pentru struct *)

Definition set_element_for_struct (str : Struct) (field : string) (val : types_allowed) :=
match str with 
| struct_cons list_pair => struct_cons (set_element_pairlist list_pair field val)
end.

Definition struct1 := struct_cons { ("Varsta" , 5 ) ;; ( "Rasa" , "Bichon" ) ;; ( "Culoare" , "Alb" ) } .

Compute get_element_for_struct struct1 "Varsta".
Compute set_element_for_struct struct1 "Varsta" 6.

Definition struct2 := set_element_for_struct struct1 "Rasa" "Bulldog".
Compute struct2.

Notation "'getS' N '[(' F ')]'" := (get_element_for_struct N F) (at level 79).

Compute struct1. 
Compute getS struct1 [("Rasa")].



(* Functii pentru map*)


(* lungimea unui map *)

Definition get_map_length (m : MapTypes) :=
match m with
| natstring k v => get_list_length k
| stringnat k v => get_list_length k
| natnat k v => get_list_length k
| stringstring k v => get_list_length k
end.

Compute get_map_length map1.
Compute get_map_length map2.




(* gasirea pozitiei unei chei intr-o lista de numere Nat*)

Fixpoint find_position_nat (l : list Nat) (val : nat) :=
match l with
| nil => 1
| cons _ v l2 => if( Nat_beq val v )
                then 0
                else 1 + (find_position_nat l2 val)
end.

Compute list1nat.
Compute find_position_nat list1nat 90.




(* gasirea pozitiei unei chei intr-o lista de numere String*)

Fixpoint find_position_string (l : list String) (val : string) :=
match l with
| nil => 1
| cons _ v l2 =>  if isTrue ( types_equal val v )
                     then 0
                     else 1 + (find_position_string l2 val)

end.

Compute list1string.
Compute find_position_string list1string "ioana".




(* get pentru map pe baza unei chei *)

Definition get_map_value_nat (m : MapTypes) (k : nat) :=
match m with
| natnat l1 l2 => get_element_list_nat l2 (find_position_nat l1 k) 
| natstring l1 l2 => get_element_list_string l2 (find_position_nat l1 k) 
| _ => Error
end.

Compute map1.
Compute get_map_value_nat map1 14.
Compute get_map_value_nat map1 5.




Definition get_map_value_string (m : MapTypes) (k : string) :=
match m with
| stringnat l1 l2 => get_element_list_nat l2 (find_position_string l1 k)
| stringstring l1 l2 => get_element_list_string l2 (find_position_string l1 k)
| _ => Error
end.

Notation "'get_mapn' M :|: K " := (get_map_value_nat M K) (at level 79).
Notation "'get_maps' M :|: K " := (get_map_value_string M K) (at level 79).

Compute list1string.
Definition map3 := stringstring list1string list2string.
Compute map3.
Compute get_map_value_string map3 "ioana".




(* functie care verifica daca o cheie exista in map *)

Definition exists_nat (l : list Nat) (k : nat) :=
match l with 
| nil => false
| _ => if ( Nat.leb (get_list_length l) (find_position_nat l k) )
            then false
            else true
end.

Compute list1nat.
Compute exists_nat list1nat 5.
Compute exists_nat list1nat 10.
            



Definition exists_string (l : list String) (k : string) :=
match l with
| nil => false
| _ => if ( Nat.leb (get_list_length l) (find_position_string l k) )
            then false
            else true
end.

Compute list1string.
Compute exists_string list1string "ioana".
Compute exists_string list1string "george".




Definition insert_element_nat (l : list Nat) (k : Nat) :=
match l with
| nil => set_element_list_nat l 0 k
| _ => set_element_list_nat l (get_list_length l) k
end.

Compute list1nat.
Compute insert_element_nat list1nat 10.
Definition list4nat := cons Nat 0 nil.
Compute list4nat.
Definition list5nat := pop_List list4nat.
Compute list5nat.
Compute insert_element_nat list5nat 5.


Definition insert_element_string (l : list String) (k : String) :=
match l with
| nil => set_element_list_string l 0 k
| _ => set_element_list_string l (get_list_length l) k
end.

Compute list1string.
Compute insert_element_string list1string "maria".



Definition insert_map_key_nat (m : MapTypes) (k : Nat) :=
match m with
| natnat l1 l2 => natnat (insert_element_nat l1 k) l2
| natstring l1 l2 => natstring (insert_element_nat l1 k) l2
| _ => m
end.


Definition insert_map_key_string (m : MapTypes) (k : String) :=
match m with
| stringstring l1 l2 => stringstring (insert_element_string l1 k) l2
| stringnat l1 l2 => stringnat (insert_element_string l1 k) l2
| _ => m
end.


Definition insert_map_value_nat (m : MapTypes) (k : Nat) :=
match m with
| natnat l1 l2 => natnat l1 (insert_element_nat l2 k)
| stringnat l1 l2 => stringnat l1 (insert_element_nat l2 k)
| _ => m
end.



Definition insert_map_value_string (m : MapTypes) (k : String) :=
match m with
| stringstring l1 l2 => stringstring l1 (insert_element_string l2 k)
| natstring l1 l2 => natstring l1 (insert_element_string l2 k)
| _ => m
end.




(* set pentru un map *)

Definition set_map_value_natnat (m : MapTypes) (k : nat) (v : Nat) :=
match m with
| natnat l1 l2 => if ( exists_nat l1 k )
                      then natnat l1 (set_element_list_nat l2 (find_position_nat l1 k) v)
                      else
                      insert_map_value_nat (insert_map_key_nat m k) v
| _ => m
end.

         
         
Definition set_map_value_natstring (m : MapTypes) (k : nat) (v : String) :=
match m with
| natstring l1 l2 => if ( exists_nat l1 k )
                      then natstring l1 (set_element_list_string l2 (find_position_nat l1 k) v)
                      else
                      insert_map_value_string (insert_map_key_nat m k) v
| _ => m
end.


Definition set_map_value_stringnat (m : MapTypes) (k : string) (v : Nat) :=
match m with
| stringnat l1 l2 => if ( exists_string l1 k )
                      then stringnat l1 (set_element_list_nat l2 (find_position_string l1 k) v)
                      else
                      insert_map_value_nat (insert_map_key_string m k) v
| _ => m
end.


Definition set_map_value_stringstring (m : MapTypes) (k : string) (v : String) :=
match m with
| stringstring l1 l2 => if ( exists_string l1 k )
                      then stringstring l1 (set_element_list_string l2 (find_position_string l1 k) v)
                      else
                      insert_map_value_string (insert_map_key_string m k) v
| _ => m
end.



Compute map1.
Compute set_map_value_natnat map1 3 10.
Compute set_map_value_natnat map1 6 10.



Notation "'get_mapn' M :|: K " := (get_map_value_nat M K) (at level 79).
Notation "'get_maps' M :|: K " := (get_map_value_string M K) (at level 79).

Compute map1. 
Compute get_mapn map1 :|: 5.






Reserved Notation "E =[ S ]=> E'" (at level 60).

Reserved Notation "A =[ S ]=> N" (at level 60).
Inductive eval_exp : Exp -> Env -> Types -> Prop :=
| const : forall n sigma, anum n =[ sigma ]=> n 
| var : forall v sigma, avar v =[ sigma ]=> (sigma v)
| add : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (types_plus i1 i2) ->
    (a1 +' a2) =[ sigma ]=> n
| minus : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (types_minus i1 i2) ->
    (a1 -' a2) =[ sigma ]=> n
| mul : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (types_mul i1 i2) ->
    (a1 *' a2) =[ sigma ]=> n
| div : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (types_div i1 i2) ->
    (a1 /' a2) =[ sigma ]=> n
| modul : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (types_mod i1 i2) ->
    (a1 %' a2) =[ sigma ]=> n
| b_true : forall sigma,
    btrue =[ sigma ]=> true
| b_false : forall sigma,
    bfalse =[ sigma ]=> false
| not : forall a i sigma n,
    a =[ sigma ]=> i ->
    n = (types_not i) ->
    (! a) =[ sigma ]=> n
| and : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (types_and i1 i2) ->
    (a1 &&' a2) =[ sigma ]=> n
| or : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (types_or i1 i2) ->
    (a1 ||' a2) =[ sigma ]=> n
| lessthan : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (types_less i1 i2) ->
    (a1 <' a2) =[ sigma ]=> n
| lessequalthan : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (types_lessequal i1 i2) ->
    (a1 <=' a2) =[ sigma ]=> n
| greaterthan : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (types_greater i1 i2) ->
    (a1 >' a2) =[ sigma ]=> n
| greaterthanequal : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (types_greaterequal i1 i2) ->
    (a1 >=' a2) =[ sigma ]=> n
| are_equal : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (types_equal i1 i2) ->
    (a1 ==' a2) =[ sigma ]=> n
| not_equal : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (types_notequal i1 i2) ->
    (a1 !=' a2) =[ sigma ]=> n
where "a =[ sigma ]=> n" := (eval_exp a sigma n).



Example true_operation : (1 +' 6 <=' 9 -' 2) =[ env1 ]=> true.
Proof.
 eapply lessequalthan.
 eapply add.
 eapply const.
 eapply const.
 simpl. reflexivity.
 eapply minus.
 eapply const.
 eapply const.
 simpl. reflexivity. 
 reflexivity.
Qed.

Example errorNat_operation : (10 /' 0) =[ env1 ]=> ErrorNat.
Proof.
 eapply div.
 eapply const.
 eapply const.
 simpl. reflexivity.
Qed.

Example errorBool_operation : (7 %' 0 <' 7) =[ env1 ]=> ErrorBool.
Proof.
 eapply lessthan.
 eapply modul.
 eapply const.
 eapply const.
 simpl. reflexivity.
 eapply const.
 simpl. reflexivity.
Qed.

Definition env3 := update default "x" 15.

Example equal_operation : ("x" *' 4 ==' 60) =[ env3 ]=> true. 
Proof.
 eapply are_equal.
 eapply mul.
 eapply var.
 eapply const.
 simpl. reflexivity.
 eapply const.
 simpl. reflexivity.
Qed.






Reserved Notation "S -{ Sigma }-> Sigma'" (at level 60).

Inductive eval_stmt : Stmt -> Env -> Env -> Prop :=
| declare_nat : forall a sigma sigma',
    sigma' = (update sigma a unassignedNat) ->
    (natural a) -{ sigma }-> sigma' 
| declare_bool : forall a sigma sigma',
    sigma' = (update sigma a unassignedBool) ->
    (boolean a) -{ sigma }-> sigma' 
| declare_string : forall a sigma sigma',
    sigma' = (update sigma a unassignedString) ->
    (char a) -{ sigma }-> sigma' 
 
| assignment_nat : forall a (i : Nat) x sigma sigma',
    a =[ sigma ]=> i ->
    sigma' = (update sigma x i) ->
    (x :n= a) -{ sigma }-> sigma'
| assignment_bool : forall a (i : Bool) x sigma sigma',
    a =[ sigma ]=> i ->
    sigma' = (update sigma x i) ->
    (x :b= a) -{ sigma }-> sigma'
| assignment_string : forall a (i : String) x sigma sigma',
    a =[ sigma ]=> i ->
    sigma' = (update sigma x i) ->
    (x :s= a) -{ sigma }-> sigma'
    
| initialize_nat : forall a (i : Nat) x sigma sigma',
    a =[ sigma ]=> i ->
    sigma' = (update sigma x (Nats i)) ->
    (Natural x ::= a) -{ sigma }-> sigma'
| initialize_bool : forall a (i : Bool) x sigma sigma',
    a =[ sigma ]=> i ->
    sigma' = (update sigma x (Bools i)) ->
    (Boolean x ::= a) -{ sigma }-> sigma'
| initialize_string : forall a (i : String) x sigma sigma',
    a =[ sigma ]=> i ->
    sigma' = (update sigma x (Strings i)) ->
    (Char x ::= a) -{ sigma }-> sigma'

| e_seq : forall s1 s2 sigma sigma1 sigma2,
    s1 -{ sigma }-> sigma1 ->
    s2 -{ sigma1 }-> sigma2 ->
    (s1 ;s; s2) -{ sigma }-> sigma2
    
| e_iftrue : forall b s1 s2 sigma sigma',
    b =[ sigma ]=> true ->
    s1 -{ sigma }-> sigma' ->
    ifthenelse b s1 s2 -{ sigma }-> sigma'
| e_iffalse : forall b s1 s2 sigma sigma',
    b =[ sigma ]=> false ->
    s2 -{ sigma }-> sigma' ->
    ifthenelse b s1 s2 -{ sigma }-> sigma' 
| e_ifthen_true : forall b s sigma sigma',
    b =[ sigma ]=> true ->
    s -{ sigma }-> sigma' ->
    ifthen b s -{ sigma }-> sigma' 
| e_ifthen_false : forall b s sigma,
    b =[ sigma ]=> false ->
    ifthen b s -{ sigma }-> sigma 

| e_whilefalse : forall b s sigma,
    b =[ sigma ]=> false ->
    while_loop b s -{ sigma }-> sigma
| e_whiletrue : forall b s sigma sigma1,
    b =[ sigma ]=> true ->
    (s ;s; while_loop b s) -{ sigma }-> sigma1 ->
    while_loop b s -{ sigma }-> sigma1

| e_fortrue: forall s1 x s2 s3 sigma sigma1 sigma2,
  s1 -{ sigma }-> sigma1 ->
  x =[ sigma1 ]=> true ->
  ( while_loop x ( s3 ;s; s2 ) ) -{ sigma1 }-> sigma2 ->
  for_loop s1 x s2 s3 -{ sigma }-> sigma2

| e_forfalse: forall s1 x s2 s3 sigma sigma1,
  s1 -{ sigma }-> sigma1 ->
  x =[ sigma ]=> false ->
  (for_loop s1 x s2 s3) -{ sigma }-> sigma1

| e_switch : forall a l sigma n v sigma',
    a =[ sigma ]=> n ->
    v = (get_switch_case n l) ->
    v -{ sigma }-> sigma' ->
    switch_case a l -{ sigma }-> sigma'
| declare_array_nat : forall a sigma sigma',
    sigma' = (update sigma a unassignedArray) ->
    ([Natural] a) -{ sigma }-> sigma' 
| declare_array_bool : forall a sigma sigma',
    sigma' = (update sigma a unassignedArray) ->
    ([Boolean] a) -{ sigma }-> sigma' 
| declare_array_string : forall a sigma sigma',
    sigma' = (update sigma a unassignedArray) ->
    ([String] a) -{ sigma }-> sigma' 
| declare_matrix : forall a sigma sigma',
    sigma' = (update sigma a unassignedArray) ->
    ([[Matrix]] a) -{ sigma }-> sigma'

| initialize_array_nat : forall (a : Array) x sigma sigma',
    sigma' = (update sigma x a) ->
    ([Natural_I] x :in:= a) -{ sigma }-> sigma'
| initialize_array_bool : forall (a : Array) x sigma sigma',
    sigma' = (update sigma x a) ->
    ([Boolean_I] x :ib:= a) -{ sigma }-> sigma'
| initialize_array_string : forall (a : Array) x sigma sigma',
    sigma' = (update sigma x a) ->
    ([String_I] x :is:= a) -{ sigma }-> sigma'
| initialize_matrix : forall (a : Array) x sigma sigma',
    sigma' = (update sigma x a) ->
    ([[Matrix_I]] x :im:= a) -{ sigma }-> sigma'

| set_array_nat : forall a poz (val : Nat) sigma sigma',
    sigma' = match sigma a with
             | Arrays a' => update sigma a (set_element_array_nat a' poz val)
             | _ => sigma
             end ->
    (a [ poz ] :n= val) -{ sigma }-> sigma'
     
| set_array_bool : forall a poz (val : Bool) sigma sigma',
    sigma' = match sigma a with
             | Arrays a' => update sigma a (set_element_array_bool a' poz val)
             | _ => sigma
             end ->
    (a [ poz ] :b= val) -{ sigma }-> sigma'
    
| set_array_string : forall a poz (val : String) sigma sigma',
    sigma' = match sigma a with
             | Arrays a' => update sigma a (set_element_array_string a' poz val)
             | _ => sigma
             end ->
    (a [ poz ] :s= val) -{ sigma }-> sigma'

| set_matrix : forall a poz (val : Array) sigma sigma',
    sigma' = match sigma a with
             | Arrays a' => update sigma a (set_element_matrix a' poz val)
             | _ => sigma
             end ->
    (a [ poz ] :m= val) -{ sigma }-> sigma'
     
| push_nat : forall a (val : Nat) sigma sigma',
  sigma' = match sigma a with
             | Arrays a' => update sigma a (pushToNat a' val)
             | unassignedArray => update sigma a ( NatArray ( set_element_list_nat [] 0 val ) )
             | _ => sigma
             end ->
    (push_n( a ) val) -{ sigma }-> sigma'

| push_bool : forall a (val : Bool) sigma sigma',
  sigma' = match sigma a with
             | Arrays a' => update sigma a (pushToBool a' val)
             | unassignedArray => update sigma a ( BoolArray ( set_element_list_bool [] 0 val ) )
             | _ => sigma
             end ->
    (push_b( a ) val) -{ sigma }-> sigma'

| push_string : forall a (val : String) sigma sigma',
  sigma' = match sigma a with
             | Arrays a' => update sigma a (pushToString a' val)
             | unassignedArray => update sigma a ( StringArray ( set_element_list_string [] 0 val ) )
             | _ => sigma
             end ->
    (push_s( a ) val) -{ sigma }-> sigma'

| push_matrix : forall a (val : Array) sigma sigma',
  sigma' = match sigma a with
             | Arrays a' => update sigma a (pushToMatrix a' val)
             | unassignedArray => update sigma a ( Matrix ( set_element_list_array [] 0 val ) )
             | _ => sigma
             end ->
    (push_m( a ) val) -{ sigma }-> sigma'

| declare_struct : forall x (s : Struct) sigma sigma',
  sigma' = update sigma x (Structs s) ->
  (struct(x) s) -{ sigma }-> sigma'

| set_struct : forall s (val : types_allowed) field sigma sigma',
  sigma' = match sigma s with
           | Structs s' => update sigma s ( Structs (set_element_for_struct s' field val) )
           | _ => sigma
           end ->
   (setS s [( field )] := val ) -{ sigma }-> sigma'


| declare_map_nn : forall x m sigma sigma',
  sigma' = match m with
           | natnat m1 m2 => update sigma x m
           | _ => sigma
           end ->
  (Map x :nn= m) -{sigma}-> sigma'

| declare_map_ns : forall x m sigma sigma',
  sigma' = match m with
           | natstring m1 m2 => update sigma x m
           | _ => sigma
           end ->
  (Map x :ns= m) -{sigma}-> sigma'
  
| declare_map_sn : forall x m sigma sigma',
  sigma' = match m with
           | stringnat m1 m2 => update sigma x m
           | _ => sigma
           end ->
  (Map x :sn= m) -{ sigma}-> sigma'
  
| declare_map_ss : forall x m sigma sigma',
  sigma' = match m with
           | stringstring m1 m2 => update sigma x m 
           | _ => sigma
           end ->
  (Map x :ss= m) -{ sigma }-> sigma'

| add_map_nn : forall m k v  sigma sigma',
  sigma' = match sigma m with
          | Maps m' => update sigma m (set_map_value_natnat m' k v)
          | _ => sigma
          end ->
  (add_nn m <- k :|: v ) -{ sigma }-> sigma'
  
| add_map_ns : forall m k v  sigma sigma',
  sigma' = match sigma m with
          | Maps m' => update sigma m (set_map_value_natstring m' k v)
          | _ => sigma
          end ->
  (add_ns m <- k :|: v ) -{ sigma }-> sigma'
  
| add_map_sn : forall m k v  sigma sigma',
  sigma' = match sigma m with
          | Maps m' => update sigma m (set_map_value_stringnat m' k v)
          | _ => sigma
          end ->
  (add_sn m <- k :|: v ) -{ sigma }-> sigma'
  
| add_map_ss : forall m k v  sigma sigma',
  sigma' = match sigma m with
          | Maps m' => update sigma m (set_map_value_stringstring m' k v)
          | _ => sigma
          end ->
  (add_ss m <- k :|: v ) -{ sigma }-> sigma'
  

where "s -{ sigma }-> sigma'" := (eval_stmt s sigma sigma').



Definition env4 := update default "x" 5.
Definition env5 := update env4 "contor" 0.
Definition env6 := update default "contor" 1.

Definition ex :=
While ("x" <' 6) 
[ "contor" :n= ( "contor" +' 1 ) ;s;
  "x" :n= ( "x" +' 1 ) ]
EndW .

Example operation :  exists sigma0, ex -{ env5 }-> sigma0 /\ sigma0 "contor" = 1. 
Proof.
  eexists. split. unfold ex.
 eapply e_whiletrue.
 eapply lessthan.
 eapply var. 
 eapply const. simpl. reflexivity. 
 repeat eapply e_seq.
 eapply assignment_nat. eapply add. 
 eapply var. eapply const. simpl. reflexivity. reflexivity. 
 eapply assignment_nat. eapply add. eapply var. 
 eapply const. simpl. reflexivity. reflexivity.
-repeat eapply e_seq.
eapply e_whilefalse. 
eapply lessthan. eapply var. eapply const. simpl. reflexivity.
-reflexivity.
Qed.

Definition env7 := update (update default "x" 5) "x" 50.
Example switch_operation : 
      switch( "x" ){ 
        case( 1 ):{ empty }; ;sw;
        case( 3 ):{ "x" :n= 30 }; ;sw;
        case( 5 ):{ "x" :n= 50 }; ;sw;
        case( 7 ):{ "y" :b= bfalse}; ;sw;
        default:{ "x" :n= 0 };
     }end  -{ env4 }-> env7.
     
Proof.
-eapply e_switch.
 eapply var. simpl. reflexivity. 
 eapply assignment_nat.
 eapply const.
 reflexivity.
Qed.

Definition program1 :=
switch( "x" ){ 
        case( 1 ):{ empty }; ;sw;
        case( 3 ):{ "x" :n= 30 }; ;sw;
        case( 5 ):{ "x" :n= 50 }; ;sw;
        case( 7 ):{ "y" :b= bfalse}; ;sw;
        default:{ "x" :n= 0 };
     }end
.

Example prog1: exists sigma0, program1 -{ env4 }-> sigma0 /\ sigma0 "x" = 50.
Proof.
  eexists. split. unfold program1.
  eapply e_switch.
  eapply var. simpl. reflexivity.
  eapply assignment_nat. eapply const.
  reflexivity. eauto.
Qed.


Definition program2 := 
natural "x" ;s; "x" :n= 2 ;s;
boolean "y" ;s; "y" :b= btrue ;s;
Natural "z" ::= 3 ;s;
"z" :n= ( "z" *' ( "x" +' "y" ) ).

Example prog2 : exists sigma0, program2 -{ default }-> sigma0 /\ sigma0 "z" = 9.
Proof.
  eexists. split. unfold program2.
  repeat eapply e_seq.
  eapply declare_nat. reflexivity.
  eapply assignment_nat. eapply const. reflexivity.
  eapply declare_bool. reflexivity.
  eapply assignment_bool. eapply b_true. reflexivity.
  eapply initialize_nat. eapply const. reflexivity.
  eapply assignment_nat. eapply mul. eapply var. eapply add. eapply var. eapply var.
  reflexivity. reflexivity. reflexivity. reflexivity.
Qed. 

Definition program3 :=
Natural "sum" ::= 0 ;s; (
For (/ ( natural "i" ) ;s; ( "i" :n= 0 ) ;f; ( "i" <=' 2 ) ;f; ( "i" :n= "i" +' 1 ) \) {/ 
    If ( "i" %' 2 ==' 0 ) Then ( "sum" :n= "sum" +' 1 ) Else ( "sum" :n= "sum" +' 2 ) EndIte
    \}
    EndF ).
    
Example prog3 : exists sigma0, program3 -{ default }-> sigma0 /\ sigma0 "sum" = 4.
Proof.
 eexists. split. unfold program3.
 repeat eapply e_seq.
 eapply initialize_nat. eapply const. reflexivity.
 eapply e_fortrue.
 repeat eapply e_seq.
 eapply declare_nat. reflexivity.
 eapply assignment_nat. eapply const. reflexivity.
 eapply lessequalthan. eapply var. eapply const. simpl. 
 repeat eapply e_seq.
 reflexivity.
 eapply e_whiletrue.
 eapply lessequalthan. eapply var. eapply const. reflexivity.
 repeat eapply e_seq.
 eapply e_iftrue. eapply are_equal. eapply modul. eapply var. eapply const. reflexivity. eapply const.
 simpl. reflexivity.
 eapply assignment_nat. eapply add. eapply var. eapply const. reflexivity. reflexivity.
 eapply assignment_nat. eapply add. eapply var. eapply const. reflexivity. reflexivity.
 eapply e_whiletrue.
 eapply lessequalthan. eapply var. eapply const. reflexivity.
 repeat eapply e_seq.
 eapply e_iffalse. eapply are_equal. eapply modul. eapply var. eapply const. reflexivity. eapply const.
 simpl. reflexivity.
 eapply assignment_nat. eapply add. eapply var. eapply const. reflexivity. reflexivity.
 eapply assignment_nat. eapply add. eapply var. eapply const. reflexivity. reflexivity.
 eapply e_whiletrue.
 eapply lessequalthan. eapply var. eapply const. reflexivity.
 repeat eapply e_seq.
 eapply e_iftrue. eapply are_equal. eapply modul. eapply var. eapply const. reflexivity. eapply const.
 simpl. reflexivity.
 eapply assignment_nat. eapply add. eapply var. eapply const. reflexivity. reflexivity.
 eapply assignment_nat. eapply add. eapply var. eapply const. reflexivity. reflexivity.
 eapply e_whilefalse.
 eapply lessequalthan. eapply var. eapply const. reflexivity. simpl. reflexivity.
Qed.
 
 

    
Definition program4 := 
[Natural] "v" ;s; 
push_n( "v" ) 4 ;s;
push_n( "v" ) 3 ;s;
push_n( "v" ) 2 ;s;
push_n( "v" ) 1 .


Example prog4 : exists sigma0, program4 -{ default }-> sigma0 /\ sigma0 "v" = ( [Natural] = {4, 3, 2, 1} ).
Proof.
 eexists. split. unfold program4.
 repeat eapply e_seq.
 eapply declare_array_nat. reflexivity.
 eapply push_nat. reflexivity. 
 eapply push_nat. reflexivity.
 eapply push_nat. reflexivity.
 eapply push_nat. reflexivity. 
 simpl. reflexivity. 
Qed. 

Definition struct3 := struct_cons { ("Varsta" , 5 ) ;; ( "Nume" , "Ioana" ) ;; ( "Zodie" , "Berbec" ) } .

Definition program5 :=
struct( "x" ) struct3 ;s;
setS "x" [( "Nume" )] := "Pelin".


Example prog5 : exists sigma0, program5 -{ default }-> sigma0 /\ sigma0 "x" = Structs ( struct_cons { ("Varsta" , 5 ) ;; ( "Nume" , "Pelin" ) ;; ( "Zodie" , "Berbec" ) } ).
Proof. 
 eexists. split. unfold program5. 
 repeat eapply e_seq.
 eapply declare_struct. reflexivity.
 eapply set_struct. reflexivity. simpl. reflexivity.
Qed.   

Compute map1.

Definition program6 :=
Map "map" :nn= natnat {1, 3, 5, 7, 9} {1, 3, 5, 7, 9} ;s;
add_nn "map" <- 5 :|: 10 ;s;
add_nn "map" <- 7 :|: 11.



Example prog6 : exists sigma0, program6 -{ default }-> sigma0 /\ sigma0 "map" = natnat {1, 3, 5, 7, 9} {1, 3, 10, 11, 9}.
Proof.
 eexists. split. unfold program6.
 repeat eapply e_seq.
 eapply declare_map_nn. reflexivity.
 eapply add_map_nn. reflexivity. 
 eapply add_map_nn. reflexivity. reflexivity.
 Qed.

Definition program7 :=
Natural "sum" ::= 0 ;s; natural "d" ;s; "d" :n= 1 ;s;
 
While ( "d" *' "d" <=' 8 )
    [  If ( (8 %' "d") ==' 0 )
      Then 
          ( ( "sum" :n= "sum" +' "d" )  ;s; ( "sum" :n= "sum" +' ( 8 /' "d" ) ) )
      Else
       ( "sum" :n= "sum" +' 0 )
      EndIte  ;s;
      "d" :n= "d" +' 1  
     ]
EndW.

Example prog7 : exists sigma0, program7 -{ default }-> sigma0 /\ sigma0 "sum" = 15.
Proof.
  eexists. split. unfold program7.
  repeat eapply e_seq.
  eapply initialize_nat. eapply const. reflexivity.
  eapply declare_nat. reflexivity.
  eapply assignment_nat. eapply const. reflexivity.
  eapply e_whiletrue. eapply lessequalthan. eapply mul. eapply var. eapply var. reflexivity. eapply const. reflexivity.
  repeat eapply e_seq.
  eapply e_iftrue. eapply are_equal. eapply modul. eapply const. eapply var. reflexivity.
  eapply const. reflexivity.
  repeat eapply e_seq.
  eapply assignment_nat. eapply add. eapply var. eapply var. reflexivity. reflexivity.
  eapply assignment_nat. eapply add. eapply var. eapply div. eapply const. eapply var. reflexivity. reflexivity. reflexivity.
  eapply assignment_nat. eapply add. eapply var. eapply const. reflexivity. reflexivity.
  eapply e_whiletrue. eapply lessequalthan. eapply mul. eapply var. eapply var. reflexivity. eapply const. reflexivity.
  repeat eapply e_seq.
  eapply e_iftrue. eapply are_equal. eapply modul. eapply const. eapply var. reflexivity.
  eapply const. reflexivity.
  repeat eapply e_seq.
  eapply assignment_nat. eapply add. eapply var. eapply var. reflexivity. reflexivity.
  eapply assignment_nat. eapply add. eapply var. eapply div. eapply const. eapply var. reflexivity. reflexivity. reflexivity.
  eapply assignment_nat. eapply add. eapply var. eapply const. reflexivity. reflexivity.
  eapply e_whilefalse. eapply lessequalthan. eapply mul. eapply var. eapply var. reflexivity. eapply const. reflexivity. reflexivity.
Qed.
  
  



