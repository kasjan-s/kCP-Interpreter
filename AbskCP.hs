module AbskCP where

-- Haskell module generated by the BNF converter


newtype Ident = Ident String deriving (Eq,Ord,Show)
data Program =
   Progr [Declaration]
  deriving (Eq,Ord,Show)

data Declaration =
   ProcDecl Declarator Compound_stm
 | VarDecl Type_specifier [Init_declarator]
 | ExpDecl Exp
  deriving (Eq,Ord,Show)

data Init_declarator =
   OnlyDecl Ident
 | InitDecl Ident Exp
  deriving (Eq,Ord,Show)

data Type_specifier =
   Tint
 | Tbool
  deriving (Eq,Ord,Show)

data Declarator =
   FuncIdent Ident Parameter_declarations
  deriving (Eq,Ord,Show)

data Parameter_declarations =
   ParamDec Parameter_declaration
 | MoreParamDec Parameter_declarations Parameter_declaration
  deriving (Eq,Ord,Show)

data Parameter_declaration =
   TypeAndParam Type_specifier Ident
  deriving (Eq,Ord,Show)

data Stm =
   CompStm Compound_stm
 | ExprStm Expression_stm
 | SelecStm Selection_stm
 | IterStm Iter_stm
 | JumpStm Jump_stm
 | PrintStm Print_stm
  deriving (Eq,Ord,Show)

data Compound_stm =
   ScompOne
 | ScompTwo [Stm]
 | ScompThree [Declaration]
 | ScompFour [Declaration] [Stm]
  deriving (Eq,Ord,Show)

data Expression_stm =
   SexprOne
 | SexprTwo Exp
  deriving (Eq,Ord,Show)

data Selection_stm =
   SselOne Exp Compound_stm
 | SselTwo Exp Compound_stm Compound_stm
  deriving (Eq,Ord,Show)

data Iter_stm =
   SiterOne Exp Compound_stm
 | SiterTwo Compound_stm Exp
 | SiterThree Expression_stm Expression_stm Compound_stm
 | SiterFour Expression_stm Expression_stm Exp Compound_stm
  deriving (Eq,Ord,Show)

data Jump_stm =
   SjumpTwo
 | SjumpThree
 | SjumpFour
 | SjumpFive Exp
  deriving (Eq,Ord,Show)

data Print_stm =
   Sprint [Exp]
  deriving (Eq,Ord,Show)

data Exp =
   Eassign Exp Assignment_op Exp
 | Elor Exp Exp
 | Eland Exp Exp
 | Eeq Exp Exp
 | Eneq Exp Exp
 | Elthen Exp Exp
 | Egrthen Exp Exp
 | Ele Exp Exp
 | Ege Exp Exp
 | Eplus Exp Exp
 | Eminus Exp Exp
 | Etimes Exp Exp
 | Ediv Exp Exp
 | Emod Exp Exp
 | Epreinc Exp
 | Epredec Exp
 | Epreop Unary_operator Exp
 | Efunk Exp
 | Efunkpar Exp [Exp]
 | Epostinc Exp
 | Epostdec Exp
 | Evar Ident
 | Econst Constant
  deriving (Eq,Ord,Show)

data Constant =
   Eint Integer
 | Ebool Boolean
  deriving (Eq,Ord,Show)

data Boolean =
   Vtrue
 | Vfalse
  deriving (Eq,Ord,Show)

data Constant_expression =
   Especial Exp
  deriving (Eq,Ord,Show)

data Unary_operator =
   Plus
 | Negative
 | Logicalneg
  deriving (Eq,Ord,Show)

data Assignment_op =
   Assign
 | AssignMul
 | AssignDiv
 | AssignMod
 | AssignAdd
 | AssignSub
  deriving (Eq,Ord,Show)

