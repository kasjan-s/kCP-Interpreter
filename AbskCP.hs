module AbskCP where

-- Haskell module generated by the BNF converter


newtype Ident = Ident String deriving (Eq,Ord,Show)
data Program =
   Progr [External_declaration]
  deriving (Eq,Ord,Show)

data External_declaration =
   DefFunc Function_def
 | Global Dec
  deriving (Eq,Ord,Show)

data Function_def =
   Func Declaration_specifier Declarator Compound_stm
  deriving (Eq,Ord,Show)

data Dec =
   Declarators Declaration_specifier [Init_declarator]
  deriving (Eq,Ord,Show)

data Declaration_specifier =
   Type Type_specifier
  deriving (Eq,Ord,Show)

data Init_declarator =
   OnlyDecl Declarator
 | InitDecl Declarator Initializer
  deriving (Eq,Ord,Show)

data Type_specifier =
   Tvoid
 | Tint
 | Tbool
 | Tstruct Struct_spec
  deriving (Eq,Ord,Show)

data Struct_spec =
   Tag Struct Ident [Struct_dec]
  deriving (Eq,Ord,Show)

data Struct =
   Structword
  deriving (Eq,Ord,Show)

data Struct_dec =
   Structen [Spec_qual] [Struct_declarator]
  deriving (Eq,Ord,Show)

data Spec_qual =
   TypeSpec Type_specifier
  deriving (Eq,Ord,Show)

data Struct_declarator =
   Decl Declarator
  deriving (Eq,Ord,Show)

data Declarator =
   Name Ident
 | InnitArray Declarator Constant_expression
 | Incomplete Declarator
 | NewFuncDec Declarator Parameter_type
 | OldFuncDef Declarator [Ident]
 | OldFuncDec Declarator
  deriving (Eq,Ord,Show)

data Parameter_type =
   AllSpec Parameter_declarations
 | More Parameter_declarations
  deriving (Eq,Ord,Show)

data Parameter_declarations =
   ParamDec Parameter_declaration
 | MoreParamDec Parameter_declarations Parameter_declaration
  deriving (Eq,Ord,Show)

data Parameter_declaration =
   OnlyType [Declaration_specifier]
 | TypeAndParam [Declaration_specifier] Declarator
  deriving (Eq,Ord,Show)

data Initializer =
   InitExpr Exp
 | InitList1 Initializers
 | InitList2 Initializers
 | InitList3 Exp Exp
 | InitList4 Initializers
 | InitList5 Initializers
  deriving (Eq,Ord,Show)

data Initializers =
   AnInit Initializer
 | MoreInit Initializers Initializer
  deriving (Eq,Ord,Show)

data Stm =
   CompStm Compound_stm
 | ExprStm Expression_stm
 | SelecStm Selection_stm
 | IterStm Iter_stm
 | JumpStm Jump_stm
  deriving (Eq,Ord,Show)

data Compound_stm =
   ScompOne
 | ScompTwo [Stm]
 | ScompThree [Dec]
 | ScompFour [Dec] [Stm]
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
 | SiterFive Ident Expression_stm Compound_stm
  deriving (Eq,Ord,Show)

data Jump_stm =
   SjumpTwo
 | SjumpThree
 | SjumpFour
 | SjumpFive Exp
  deriving (Eq,Ord,Show)

data Exp =
   Ecomma Exp Exp
 | Eassign Exp Assignment_op Exp
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
 | Earray Exp Exp
 | Efunk Exp
 | Efunkpar Exp [Exp]
 | Eselect Exp Ident
 | Epostinc Exp
 | Epostdec Exp
 | Evar Ident
 | Econst Constant
  deriving (Eq,Ord,Show)

data Constant =
   Eint Integer
 | Ebool Boolean
 | Evoid
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
 | AssignAnd
 | AssignOr
  deriving (Eq,Ord,Show)

