Require Import Arith.
Require Import Ascii.
Require Import Nat.
Require Import Bool.
Require Import Coq.Strings.Byte.
Require Import Strings.String.
Scheme Equality for string.
Local Open Scope string_scope.
Require Import List. 
Import ListNotations.
Require Import Omega.
Section Arith.

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


Inductive Types : Type :=
| Nats (n : Nat)
| Bools (b : Bool)
| Strings (s: String).

Definition Env := string -> Types.
Coercion Nats : Nat >-> Types.
Coercion Bools : Bool >-> Types.
Coercion Strings : String >-> Types.

Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.
  
Definition update (env : Env)
           (x : string) (v : Types) : Env :=
  fun y => if (eqb_string y x)
           then v
           else (env y).
           
Definition all (x : Types) : Env :=
  (fun _ => x).

Definition default := all 0.


Inductive Exp :=
| anum : Types -> Exp
| avar : string -> Exp
| aplus : Exp -> Exp -> Exp
| aminus : Exp -> Exp -> Exp
| amul : Exp -> Exp -> Exp
| adiv : Exp -> Exp -> Exp
| amod : Exp -> Exp -> Exp
| not' : Exp -> Exp
| and' : Exp -> Exp -> Exp
| or' : Exp -> Exp -> Exp
| less : Exp -> Exp -> Exp
| lessequal : Exp -> Exp -> Exp
| greater : Exp -> Exp -> Exp
| greaterequal : Exp -> Exp -> Exp
| equal : Exp -> Exp -> Exp
| notequal : Exp -> Exp -> Exp.


Coercion avar : string >-> Exp.
Coercion anum : Types >-> Exp.



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
Check (and' 2 2).

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
| TypeNat x, TypeNat y => if( ltb x  y ) then TypeNat(y - x) else TypeNat(x - y)
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





Fixpoint Eval (exp : Exp) (env : Env) : Types :=
match exp with
| anum x => x
| avar x => env x
| aplus x y => types_plus (Eval x env) (Eval y env)
| aminus x y => types_minus (Eval x env) (Eval y env)
| amul x y => types_mul (Eval x env) (Eval y env)
| adiv x y => types_div (Eval x env) (Eval y env)
| amod x y => types_mod (Eval x env) (Eval y env)
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





Definition env1 := update (update default "x" 5) "y" 6.

Compute Eval ( ( 10 +' ( "y" *' "x" ) /' ( 10 +' ( "x" *' true) +' ("y" *' false) )) /' ( 8 -'( 8 /' 2 )) ) env1.

Inductive Instruction :=
| push_num (n: Types)
| push_var (x: string)
| i_add | i_min
| i_mul | i_div | i_mod
| i_not | i_and | i_or
| i_less  | i_lessequal | i_greater  | i_greaterequal
| i_equal  | i_notequal.
 
Compute push_num 6. Compute push_var "x".
Compute i_add. Compute i_min.
Compute i_mul. Compute i_div. Compute i_mod.
Compute i_not. Compute i_and. Compute i_or.
Compute i_less . Compute i_lessequal. Compute i_greater. Compute i_greaterequal.
Compute i_equal . Compute i_notequal.

Definition Environment := string -> Types.

Definition Stack := list Types.


Definition run_instruction (i : Instruction) (env: Environment) (stack : Stack) : Stack :=
match i with
| push_num n => n :: stack
| push_var x => (env x) :: stack
| i_add => match stack with
					| n1 :: n2 :: stack' => Nats (types_plus n1 n2) :: stack'
					| _ => stack
					end
| i_min => match stack with
					| n1 :: n2 :: stack' => Nats (types_minus n1 n2) :: stack'
					| _ => stack
					end
| i_mul => match stack with
					| n1 :: n2 :: stack' => Nats (types_mul n1 n2) :: stack'
					| _ => stack
					end
| i_div => match stack with
					| n1 :: n2 :: stack' => Nats (types_div n1 n2) :: stack'
					| _ => stack
					end
| i_mod => match stack with
					| n1 :: n2 :: stack' => Nats (types_mod n1 n2) :: stack'
					| _ => stack
					end
| i_not => match stack with
					| n :: stack' => Bools (types_not n) :: stack'
					| _ => stack
					end
| i_and => match stack with
					| n1 :: n2 :: stack' => Bools (types_and n1 n2) :: stack'
					| _ => stack 
					end
| i_or => match stack with
					| n1 :: n2 :: stack' => Bools (types_or n1 n2) :: stack'
					| _ => stack
					end
| i_less => match stack with
					| n1 :: n2 :: stack' => Bools (types_less n1 n2) :: stack'
					| _ => stack
					end
| i_lessequal => match stack with
					| n1 :: n2 :: stack' => Bools (types_lessequal n1 n2) :: stack'
					| _ => stack
					end
| i_greater => match stack with
					| n1 :: n2 :: stack' => Bools (types_greater n1 n2) :: stack'
					| _ => stack
					end
| i_greaterequal => match stack with
					| n1 :: n2 :: stack' => Bools (types_greaterequal n1 n2) :: stack'
					| _ => stack
					end
| i_equal => match stack with
					| n1 :: n2 :: stack' => Bools (types_equal n1 n2) :: stack'
					| _ => stack
					end
| i_notequal => match stack with
					| n1 :: n2 :: stack' => Bools (types_notequal n1 n2) :: stack'
					| _ => stack
					end
end.


Fixpoint run_instructions (is' : list Instruction) (env : Env) (stack : Stack) : Stack :=
match is' with
| [] => stack
| i :: is'' => run_instructions is'' env (run_instruction i env stack)
end.

Fixpoint compile (e : Exp) : list Instruction :=
match e with
| anum c => [push_num c]
| avar x => [push_var x]
| e1 +' e2 => (compile e2) ++ (compile e1) ++ [i_add]
| e1 -' e2 => (compile e2) ++ (compile e1) ++ [i_min]
| e1 *' e2 => (compile e2) ++ (compile e1) ++ [i_mul]
| e1 /' e2 => (compile e2) ++ (compile e1) ++ [i_div]
| e1 %' e2 => (compile e2) ++ (compile e1) ++ [i_mod]
| ! e => (compile e) ++ [i_not]
| e1 &&' e2 => (compile e2) ++ (compile e1) ++ [i_and]
| e1 ||' e2 => (compile e2) ++ (compile e1) ++ [i_or]
| e1 <' e2 => (compile e2) ++ (compile e1) ++ [i_less]
| e1 <=' e2 => (compile e2) ++ (compile e1) ++ [i_lessequal]
| e1 >' e2 => (compile e2) ++ (compile e1) ++ [i_greater]
| e1 >=' e2 => (compile e2) ++ (compile e1) ++ [i_greaterequal]
| e1 ==' e2 => (compile e2) ++ (compile e1) ++ [i_equal]
| e1 !=' e2 => (compile e2) ++ (compile e1) ++ [i_notequal]
end.


Compute compile (2 +' "x").
Compute compile (2 +' "x" *' 7).
Compute compile (2 *' "x" +' 7).

Compute Eval (2 *' "x" +' 7) env1.
Compute run_instructions
        (compile (2 *' "x" +' 7))
        env1
        [].
        



Theorem plus_com : forall (x y : Types), types_plus x y = types_plus y x.
Proof.
 intros x y.
 induction x. destruct y.
 - unfold types_plus.
   -- induction n.
   --- induction n0.
   ---- rewrite PeanoNat.Nat.add_comm. reflexivity.
   ---- reflexivity.
   --- induction n0. reflexivity. reflexivity.
 - unfold types_plus. 
   -- induction n.
     --- induction b.
     ---- rewrite <- PeanoNat.Nat.add_comm. replace (0 + n) with (n + 0). 
     ----- reflexivity.
     ----- rewrite <- PeanoNat.Nat.add_comm. reflexivity.
     ----  reflexivity.
     --- induction b. reflexivity. reflexivity.
  - unfold types_plus. 
   -- induction n.
     --- reflexivity. 
     --- reflexivity.
  - unfold types_plus. 
     -- induction b.
     --- induction y.
     ---- induction n.
     ----- rewrite <- PeanoNat.Nat.add_comm. replace (0 + n) with (n + 0). 
     ------ reflexivity.
     ------ rewrite <- PeanoNat.Nat.add_comm. reflexivity.
     -----  reflexivity.
     ---- induction b0. 
     ----- induction b.
     ------ reflexivity. 
     ------ reflexivity.
     ----- reflexivity. 
     ---- reflexivity.
     --- induction y.
     ---- induction n. reflexivity. reflexivity.
     ---- induction b. reflexivity. reflexivity. 
     ---- reflexivity.
  - unfold types_plus.
   -- induction y.
   --- induction n. reflexivity. reflexivity.
   --- induction b. reflexivity. reflexivity. 
   --- reflexivity.
Qed.


Theorem mul_com : forall (x y : Types), types_mul x y = types_mul y x.
Proof.
intros x y.
 induction x. destruct y.
 - unfold types_mul.
   -- induction n.
   --- induction n0.
   ---- rewrite PeanoNat.Nat.mul_comm. reflexivity.
   ---- reflexivity.
   --- induction n0. reflexivity. reflexivity.
 - unfold types_mul. 
   -- induction n.
     --- induction b.
     ---- reflexivity. 
     ---- reflexivity.
     --- induction b. reflexivity. reflexivity.
  - unfold types_mul. 
   -- induction n.
     --- reflexivity. 
     --- reflexivity.
  - unfold types_mul. 
     -- induction b.
     --- induction y.
     ---- induction n.
     ------ reflexivity.
     ------ reflexivity.
     ---- induction b0. 
     ----- induction b.
     ------ reflexivity. 
     ------ induction b0.
     ------- reflexivity. 
     ------- reflexivity.
     ----- reflexivity.
     ---- reflexivity.
     --- induction y.
     ---- induction n. reflexivity. reflexivity.
     ---- induction b. reflexivity. reflexivity. 
     ---- reflexivity.
  - unfold types_mul.
   -- induction y.
   --- induction n. reflexivity. reflexivity.
   --- induction b. reflexivity. reflexivity. 
   --- reflexivity.
Qed.



Theorem and_com : forall (x y : Types), types_and x y = types_and y x.
Proof.
intros x y.
 induction x. destruct y.
 - unfold types_and.
   -- induction n.
   --- induction n0.
   ---- induction n.
   ----- induction n0. reflexivity. reflexivity.
   ----- induction n0. reflexivity. reflexivity.
   ---- reflexivity.
   --- induction n0. reflexivity. reflexivity.
 - unfold types_and. 
   -- induction n.
     --- induction b.
     ---- induction n. 
     ----- induction b. reflexivity. reflexivity. 
     ----- reflexivity.
     ---- reflexivity.
     --- induction b. reflexivity. reflexivity. 
  - unfold types_and. 
   -- induction n.
     --- reflexivity. 
     --- reflexivity.
  - unfold types_and. 
     -- induction b.
     --- induction y.
     ---- induction n.
     ------ induction n.
     ------- induction b. reflexivity. reflexivity.
     ------- reflexivity. 
     ------ reflexivity.
     ---- induction b0. 
     ----- induction b.
     ------ reflexivity. 
     ------ induction b0.
     ------- reflexivity. 
     ------- reflexivity.
     ----- reflexivity.
     ---- reflexivity.
     --- induction y.
     ---- induction n. reflexivity. reflexivity.
     ---- induction b. reflexivity. reflexivity. 
     ---- reflexivity.
  - unfold types_and.
   -- induction y.
   --- induction n. reflexivity. reflexivity.
   --- induction b. reflexivity. reflexivity. 
   --- reflexivity.
Qed.


Theorem or_com : forall (x y : Types), types_or x y = types_or y x.
Proof.
intros x y.
 induction x. destruct y.
 - unfold types_or.
   -- induction n.
   --- induction n0.
   ---- induction n.
   ----- induction n0. reflexivity. reflexivity.
   ----- induction n0. reflexivity. reflexivity.
   ---- reflexivity.
   --- induction n0. reflexivity. reflexivity.
 - unfold types_or. 
   -- induction n.
     --- induction b.
     ---- induction n. 
     ----- induction b. reflexivity. reflexivity. 
     ----- induction b. reflexivity. reflexivity.
     ---- reflexivity.
     --- induction b. reflexivity. reflexivity. 
  - unfold types_or. 
   -- induction n.
     --- reflexivity. 
     --- reflexivity.
  - unfold types_or. 
     -- induction b.
     --- induction y.
     ---- induction n.
     ------ induction n.
     ------- induction b. reflexivity. reflexivity.
     ------- induction b. reflexivity. reflexivity.
     ------ reflexivity.
     ---- induction b0. 
     ----- induction b.
     ------ induction b0.
     ------- reflexivity. 
     ------- reflexivity.
     ------ reflexivity.
     ----- reflexivity.
     ---- reflexivity.
     --- induction y.
     ---- induction n. reflexivity. reflexivity.
     ---- induction b. reflexivity. reflexivity. 
     ---- reflexivity.
  - unfold types_or.
   -- induction y.
   --- induction n. reflexivity. reflexivity.
   --- induction b. reflexivity. reflexivity. 
   --- reflexivity.
Qed.

 





Lemma soundness_helper :
  forall e env stack is',
    run_instructions (compile e ++ is') env stack =
    run_instructions is' env ((Eval e env) :: stack).
Proof. 
  induction e; intros; simpl; trivial.
  - rewrite <- app_assoc.
    rewrite <- app_assoc.
    rewrite IHe2.
    rewrite IHe1.
    simpl.
    reflexivity.
  - rewrite <- app_assoc.
    rewrite <- app_assoc.
    rewrite IHe2.
    rewrite IHe1.
    simpl.
    reflexivity.
  - rewrite <- app_assoc.
    rewrite <- app_assoc.
    rewrite IHe2.
    rewrite IHe1.
    simpl.
    reflexivity.
  - rewrite <- app_assoc.
    rewrite <- app_assoc.
    rewrite IHe2.
    rewrite IHe1.
    simpl.
    reflexivity.
  - rewrite <- app_assoc.
    rewrite <- app_assoc.
    rewrite IHe2.
    rewrite IHe1.
    simpl.
    reflexivity.
  - rewrite <- app_assoc.
    rewrite IHe.
    simpl.
    reflexivity.
  - rewrite <- app_assoc.
    rewrite <- app_assoc.
    rewrite IHe2.
    rewrite IHe1.
    simpl.
    reflexivity.
  - rewrite <- app_assoc.
    rewrite <- app_assoc.
    rewrite IHe2.
    rewrite IHe1.
    simpl.
    reflexivity.
  - rewrite <- app_assoc.
    rewrite <- app_assoc.
    rewrite IHe2.
    rewrite IHe1.
    simpl.
    reflexivity.
  - rewrite <- app_assoc.
    rewrite <- app_assoc.
    rewrite IHe2.
    rewrite IHe1.
    simpl.
    reflexivity.
  - rewrite <- app_assoc.
    rewrite <- app_assoc.
    rewrite IHe2.
    rewrite IHe1.
    simpl.
    reflexivity.
  - rewrite <- app_assoc.
    rewrite <- app_assoc.
    rewrite IHe2.
    rewrite IHe1.
    simpl.
    reflexivity.
  - rewrite <- app_assoc.
    rewrite <- app_assoc.
    rewrite IHe2.
    rewrite IHe1.
    simpl.
    reflexivity.
  - rewrite <- app_assoc.
    rewrite <- app_assoc.
    rewrite IHe2.
    rewrite IHe1.
    simpl.
    reflexivity.
Qed.


Theorem soundness :
  forall e env,
    run_instructions (compile e) env [] =
    [Eval e env].
Proof.
  intros.
  rewrite <- app_nil_r with (l := (compile e)).
  rewrite soundness_helper.
  simpl. reflexivity.
Qed.
