-- This Happy file was machine-generated by the BNF converter
{
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns #-}
module ParkCP where
import AbskCP
import LexkCP
import ErrM

}

%name pProgram Program

-- no lexer declaration
%monad { Err } { thenM } { returnM }
%tokentype { Token }

%token 
 '!' { PT _ (TS _ 1) }
 '!=' { PT _ (TS _ 2) }
 '%' { PT _ (TS _ 3) }
 '%=' { PT _ (TS _ 4) }
 '&&' { PT _ (TS _ 5) }
 '(' { PT _ (TS _ 6) }
 ')' { PT _ (TS _ 7) }
 '*' { PT _ (TS _ 8) }
 '*=' { PT _ (TS _ 9) }
 '+' { PT _ (TS _ 10) }
 '++' { PT _ (TS _ 11) }
 '+=' { PT _ (TS _ 12) }
 ',' { PT _ (TS _ 13) }
 '-' { PT _ (TS _ 14) }
 '--' { PT _ (TS _ 15) }
 '-=' { PT _ (TS _ 16) }
 '/' { PT _ (TS _ 17) }
 '/=' { PT _ (TS _ 18) }
 ';' { PT _ (TS _ 19) }
 '<' { PT _ (TS _ 20) }
 '<=' { PT _ (TS _ 21) }
 '=' { PT _ (TS _ 22) }
 '==' { PT _ (TS _ 23) }
 '>' { PT _ (TS _ 24) }
 '>=' { PT _ (TS _ 25) }
 'bool' { PT _ (TS _ 26) }
 'break' { PT _ (TS _ 27) }
 'continue' { PT _ (TS _ 28) }
 'do' { PT _ (TS _ 29) }
 'else' { PT _ (TS _ 30) }
 'false' { PT _ (TS _ 31) }
 'for' { PT _ (TS _ 32) }
 'if' { PT _ (TS _ 33) }
 'int' { PT _ (TS _ 34) }
 'print' { PT _ (TS _ 35) }
 'return' { PT _ (TS _ 36) }
 'true' { PT _ (TS _ 37) }
 'void' { PT _ (TS _ 38) }
 'while' { PT _ (TS _ 39) }
 '{' { PT _ (TS _ 40) }
 '||' { PT _ (TS _ 41) }
 '}' { PT _ (TS _ 42) }

L_ident  { PT _ (TV $$) }
L_integ  { PT _ (TI $$) }
L_err    { _ }


%%

Ident   :: { Ident }   : L_ident  { Ident $1 }
Integer :: { Integer } : L_integ  { (read ( $1)) :: Integer }

Program :: { Program }
Program : ListDeclaration { Progr $1 } 


ListDeclaration :: { [Declaration] }
ListDeclaration : Declaration { (:[]) $1 } 
  | Declaration ListDeclaration { (:) $1 $2 }


Declaration :: { Declaration }
Declaration : Type_specifier Declarator Compound_stm { FuncDecl $1 $2 $3 } 
  | Type_specifier ListInit_declarator ';' { VarDecl $1 $2 }
  | Exp ';' { ExpDecl $1 }


ListInit_declarator :: { [Init_declarator] }
ListInit_declarator : Init_declarator { (:[]) $1 } 
  | Init_declarator ',' ListInit_declarator { (:) $1 $3 }


Init_declarator :: { Init_declarator }
Init_declarator : Ident { OnlyDecl $1 } 
  | Ident '=' Exp { InitDecl $1 $3 }


Type_specifier :: { Type_specifier }
Type_specifier : 'int' { Tint } 
  | 'bool' { Tbool }
  | 'void' { Tvoid }


Declarator :: { Declarator }
Declarator : Ident '(' ListParameter_declaration ')' { FuncIdent $1 $3 } 


ListParameter_declaration :: { [Parameter_declaration] }
ListParameter_declaration : {- empty -} { [] } 
  | Parameter_declaration { (:[]) $1 }
  | Parameter_declaration ',' ListParameter_declaration { (:) $1 $3 }


Parameter_declaration :: { Parameter_declaration }
Parameter_declaration : Type_specifier Ident { TypeAndParam $1 $2 } 


ListIdent :: { [Ident] }
ListIdent : Ident { (:[]) $1 } 
  | Ident ',' ListIdent { (:) $1 $3 }


Stm :: { Stm }
Stm : Compound_stm { CompStm $1 } 
  | Expression_stm { ExprStm $1 }
  | Selection_stm { SelecStm $1 }
  | Iter_stm { IterStm $1 }
  | Jump_stm { JumpStm $1 }
  | Print_stm { PrintStm $1 }
  | Declaration { DeclStm $1 }


Compound_stm :: { Compound_stm }
Compound_stm : '{' '}' { SEmptyComp } 
  | '{' ListStm '}' { SStmtComp $2 }
  | '{' ListDeclaration '}' { SDeclComp $2 }
  | '{' ListDeclaration ListStm '}' { SMixComp $2 $3 }


Expression_stm :: { Expression_stm }
Expression_stm : ';' { SEmptyExpr } 
  | Exp ';' { SExpr $1 }


Selection_stm :: { Selection_stm }
Selection_stm : 'if' '(' Exp ')' Compound_stm { SIf $3 $5 } 
  | 'if' '(' Exp ')' Compound_stm 'else' Compound_stm { SIfElse $3 $5 $7 }


Iter_stm :: { Iter_stm }
Iter_stm : 'while' '(' Exp ')' Compound_stm { SWhile $3 $5 } 
  | 'do' Compound_stm 'while' '(' Exp ')' { SDoWhile $2 $5 }
  | 'for' '(' Expression_stm Expression_stm ')' Compound_stm { SForEmpty $3 $4 $6 }
  | 'for' '(' Expression_stm Expression_stm Exp ')' Compound_stm { SFor $3 $4 $5 $7 }


Jump_stm :: { Jump_stm }
Jump_stm : 'continue' ';' { SjumpCont } 
  | 'break' ';' { SjumpBreak }
  | 'return' ';' { SjumpReturn }
  | 'return' Exp ';' { SjumpRetExp $2 }


Print_stm :: { Print_stm }
Print_stm : 'print' '(' ListExp ')' ';' { Sprint $3 } 


ListStm :: { [Stm] }
ListStm : Stm { (:[]) $1 } 
  | Stm ListStm { (:) $1 $2 }


Exp :: { Exp }
Exp : Exp8 Assignment_op Exp { Eassign $1 $2 $3 } 
  | Exp2 { $1 }


Exp2 :: { Exp }
Exp2 : Exp2 '||' Exp4 { Elor $1 $3 } 
  | Exp3 { $1 }


Exp3 :: { Exp }
Exp3 : Exp3 '&&' Exp4 { Eland $1 $3 } 
  | Exp4 { $1 }


Exp4 :: { Exp }
Exp4 : Exp4 '==' Exp5 { Eeq $1 $3 } 
  | Exp4 '!=' Exp5 { Eneq $1 $3 }
  | Exp5 { $1 }


Exp5 :: { Exp }
Exp5 : Exp5 '<' Exp6 { Elthen $1 $3 } 
  | Exp5 '>' Exp6 { Egrthen $1 $3 }
  | Exp5 '<=' Exp6 { Ele $1 $3 }
  | Exp5 '>=' Exp6 { Ege $1 $3 }
  | Exp6 { $1 }


Exp6 :: { Exp }
Exp6 : Exp6 '+' Exp7 { Eplus $1 $3 } 
  | Exp6 '-' Exp7 { Eminus $1 $3 }
  | Exp7 { $1 }


Exp7 :: { Exp }
Exp7 : Exp7 '*' Exp8 { Etimes $1 $3 } 
  | Exp7 '/' Exp8 { Ediv $1 $3 }
  | Exp7 '%' Exp8 { Emod $1 $3 }
  | Exp8 { $1 }


Exp8 :: { Exp }
Exp8 : '++' Exp8 { Epreinc $2 } 
  | '--' Exp8 { Epredec $2 }
  | Unary_operator Exp8 { Epreop $1 $2 }
  | Exp9 { $1 }


Exp9 :: { Exp }
Exp9 : Ident '(' ')' { Efunk $1 } 
  | Ident '(' ListExp ')' { Efunkpar $1 $3 }
  | Exp9 '++' { Epostinc $1 }
  | Exp9 '--' { Epostdec $1 }
  | Exp10 { $1 }


Exp10 :: { Exp }
Exp10 : Ident { Evar $1 } 
  | Constant { Econst $1 }
  | Exp11 { $1 }


Constant :: { Constant }
Constant : Integer { Eint $1 } 
  | Boolean { Ebool $1 }


Boolean :: { Boolean }
Boolean : 'true' { Vtrue } 
  | 'false' { Vfalse }


Constant_expression :: { Constant_expression }
Constant_expression : Exp3 { Especial $1 } 


Exp11 :: { Exp }
Exp11 : Exp12 { $1 } 


Exp12 :: { Exp }
Exp12 : Exp13 { $1 } 


Exp13 :: { Exp }
Exp13 : Exp14 { $1 } 


Exp14 :: { Exp }
Exp14 : Exp15 { $1 } 


Exp15 :: { Exp }
Exp15 : Exp16 { $1 } 


Exp16 :: { Exp }
Exp16 : Exp17 { $1 } 


Exp17 :: { Exp }
Exp17 : '(' Exp ')' { $2 } 


Unary_operator :: { Unary_operator }
Unary_operator : '+' { Plus } 
  | '-' { Negative }
  | '!' { Logicalneg }


ListExp :: { [Exp] }
ListExp : Exp { (:[]) $1 } 
  | Exp ',' ListExp { (:) $1 $3 }


Assignment_op :: { Assignment_op }
Assignment_op : '=' { Assign } 
  | '*=' { AssignMul }
  | '/=' { AssignDiv }
  | '%=' { AssignMod }
  | '+=' { AssignAdd }
  | '-=' { AssignSub }



{

returnM :: a -> Err a
returnM = return

thenM :: Err a -> (a -> Err b) -> Err b
thenM = (>>=)

happyError :: [Token] -> Err a
happyError ts =
  Bad $ "syntax error at " ++ tokenPos ts ++ 
  case ts of
    [] -> []
    [Err _] -> " due to lexer error"
    _ -> " before " ++ unwords (map (id . prToken) (take 4 ts))

myLexer = tokens
}

