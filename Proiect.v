Require Import Arith.
Require Import Ascii.
Require Import Nat.
Require Import Bool.
Require Import Coq.Strings.Byte.
Require Import Strings.String.
Scheme Equality for string.
Local Open Scope string_scope.


Inductive Nat : Type :=
| TypeNat : nat -> Nat
| ErrorNat : Nat. 

Inductive Bool : Type :=
| TypeBool : bool -> Bool
| ErrorBool : Bool.

Inductive String : Type :=
| TypeString : string -> String
| ErrorString : String.

Coercion TypeNat : nat >-> Nat.
Coercion TypeBool : bool >-> Bool.
Coercion TypeString : string >->String.

Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.

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

Definition list1nat := {2, 4, 6, 8, 10, 12, 14}.
Definition list2nat := {1, 3, 5, 7, 9}.
Definition list1bool := {true; false; true; false; false}.
Definition list1string := { "ioan" ;;; "ioana" }.

Inductive Array : Type :=
| NatArray : list Nat -> Array
| BoolArray : list Bool -> Array
| StringArray : list String -> Array
| Matrix : list Array -> Array.


Check NatArray list1nat.
Check BoolArray list1bool.

Notation "{ X & .. & Y }" := (cons Array X .. (cons Array Y []) ..).
Check Matrix { (NatArray list1nat) & (NatArray list2nat) }.

Notation "'[Natural]' = L " := (NatArray L) (at level 20).
Notation "'[Boolean]' = L " := (BoolArray L) (at level 20).
Notation "'[String]' = L " := (StringArray L) (at level 20).
Notation "'[[Matrix]]' = L" := (Matrix L) (at level 20).


Definition vector_nat := [Natural] = list1nat.
Definition vector_bool := [Boolean] = list1bool.
Definition vector_string := [String] = list1string.
Definition matrix_both := [[Matrix]] = { vector_nat & vector_bool }.


Compute vector_nat.
Compute vector_bool.
Compute vector_string.


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

Inductive pair_struct : Type :=
| pair (first : string) (second : types_allowed). 

Notation "( N , V )" := (pair N V).
Notation "{ P1 ;; .. ;; P2 }" := (cons pair_struct P1 .. (cons pair_struct P2 []) ..). 

Inductive Struct : Type :=
| struct (s : string) ( struct_pairs : list pair_struct).

Definition pair_get_first (p : pair_struct) :=
match p with
| pair first second => first
end.
 

Definition pair_get_second (p : pair_struct) :=
match p with
| pair first second => second
end.

Fixpoint get_element_pairlist (l : list pair_struct) (f : string) :=
match l with
| nil => inexistent
| cons _ field l2 => if ( eqb_string f ( pair_get_first field ))
                     then pair_get_second field
                     else get_element_pairlist l2 f
end.

Definition get_element_struct (str : Struct) (field : string) :=
match str with
| struct name list_pair => get_element_pairlist list_pair field
end.


Definition struct1 := struct "Animale" { ("Varsta" , 5 ) ;; ( "Rasa" , "Bichon" ) ;; ( "Culoare" , "Alb" ) } .

Compute get_element_struct struct1 "Varsta".

Inductive pair_map (T1 T2 : Type) : Type :=
| pairr (first : T1) (second : T2). 

Inductive Map (T1 T2 : Type): Type :=
| map (s : string) ( map_pair : list (pair_map T1 T2)).

Inductive Types : Type := 
| Nats (n : Nat)
| Bools (b : Bool)
| undeclared : Types
| Arrays (v : Array)
| Structs (s : Struct)
| Error.


Definition Env := string -> Types.
Coercion Nats : Nat >-> Types.
Coercion Bools : Bool >-> Types.



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


Inductive Exp :=
| anum : Nat -> Exp
| avar : string -> Exp
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


Compute (types_plus true true).
Compute (types_plus false true).
Compute (types_plus 9 true).

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

Compute (types_minus true false).
Compute (types_minus true true).
Compute (types_minus 8 false).
Compute (types_minus 8 true).
Compute (types_minus 10 8).
Compute (types_minus false 2).
Compute (types_minus true 0).

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

Definition types_greater (x y : Types) := types_not (types_lessequal x y). 

Compute (types_greater 6 4).
Compute (types_greater 4 6).

Definition types_greaterequal (x y : Types) := types_not (types_less x y). 

Compute (types_greaterequal 6 4).
Compute (types_greaterequal 4 4).

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
| _, _ => ErrorBool
end.

Compute (types_equal 5 5).
Compute (types_equal true true).
Compute (types_equal true false).
Compute (types_equal true 1).
Compute (types_equal true 5).

Definition types_notequal (x y : Types) := types_not (types_equal x y). 

Compute (types_notequal true true).
Compute (types_notequal true false).
Compute (types_notequal true 1).
Compute (types_notequal true 5).

Fixpoint Eval (exp : Exp) (env : Env) : Types :=
match exp with
| anum x => x
| avar x => env x
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



Inductive Stmt : Type :=
| declare : string -> string -> Stmt
| assignment : string -> Exp -> Stmt
| initialize : string -> string -> Exp -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| ifthenelse : Exp -> Stmt -> Stmt -> Stmt
| ifthen : Exp -> Stmt -> Stmt 
| while_loop : Exp -> Stmt -> Stmt 
| for_loop : Stmt -> Exp -> Stmt -> Stmt -> Stmt
| switch_case : string -> list (pair_map Nat Stmt) -> Stmt
| break : Stmt
| continue : Stmt
| declareArray : string -> string -> Stmt
| initializeArray : string -> string -> list Types -> Stmt
| getElemArray : string -> nat -> Stmt
| setElemArrayNat : string -> nat -> Nat -> Stmt
| setElemArrayBool : string -> nat -> Bool -> Stmt
| setElemArrayString : string -> nat -> String -> Stmt
| setElemArrayMatrix : string -> nat -> Array -> Stmt
| pushNat : string -> Nat -> Stmt
| pushBool : string -> Bool -> Stmt
| pushString : string -> String -> Stmt
| pushMatrix : string -> Array -> Stmt 
| pop : string -> Stmt
| declareStruct : string -> list pair_struct -> Stmt
| get_element_from_struct : string -> string -> Stmt
| set_element_struct : string -> string -> types_allowed -> Stmt
| declareMap : string -> list (pair_map types_allowed types_allowed) -> Stmt
| addToMap : string -> pair_map types_allowed types_allowed -> Stmt
| getValue : string -> types_allowed -> Stmt.



Notation "X ::= A" := (assignment X A) (at level 80).
Notation "'Let' T S" := (declare T S) (at level 79).
Notation "S1 ;; S2" := (sequence S1 S2 ) (at level 98, left associativity).
Notation "'If' ( B ) 'Then' ( S1 ) 'Else' ( S2 ) 'EndIte'" := (ifthenelse B S1 S2) (at level 97).
Notation "'If' ( B ) 'Then' ( S ) 'EndI'" := (ifthen B S ) (at level 97).
Notation "'While' ( B ) { S } 'EndW'" := (while_loop B S) (at level 97).
Notation "'For' ( S1 ';' B ';' S2 ) { S3 }  'EndF'" := (for_loop S1 B S2 S3) (at level 97).



