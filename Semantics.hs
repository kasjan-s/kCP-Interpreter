module Semantics where

import AbskCP

import Data.Map

data ExprVal =
      TInt Integer
    | TBool Bool
    | TVoid
    deriving (Ord, Eq, Show)

instance Num ExprVal where
  TInt x + TInt y = TInt (x + y)
  _ + _ = error "Can't add these values"
  TInt x - TInt y = TInt (x - y)
  _ - _ = error "Can't subtract these values"
  TInt x * TInt y = TInt (x * y)
  _ * _ = error "Can't multiply these values"
  abs (TInt x) = TInt (abs x)
  abs _ = error "abs on wrong value"
  signum (TInt x) = TInt (signum x)
  signum _ = error "signum on wrong value"
  fromInteger x = TInt x

exprDiv :: ExprVal -> ExprVal -> ExprVal
exprDiv (TInt x) (TInt y) =
  if y == 0 then error "Division by zero"
  else TInt (div x y)
exprDiv _ _ = error "Dividing invalid values"

exprMod :: ExprVal -> ExprVal -> ExprVal
exprMod (TInt x) (TInt y) =
  if y == 0 then error "Division by zero"
  else TInt (mod x y)
exprMod _ _ = error "Dividing invalid values"

type Loc = Int
type Store = Map Loc ExprVal

type FName = Ident
type Func = (Type_specifier, [Parameter_declaration], Compound_stm)

type VEnv = Map Ident Loc
type PEnv = Map FName Func

type Env = (VEnv, PEnv)

type Ans = IO (Store, Env)
type Cont = Store -> Ans
type DeclCont = Env -> Cont
type ExprCont = ExprVal -> Cont
type StmCont = Env -> Cont
type ReturnH = ExprVal -> Cont

newLoc :: Store -> Loc
newLoc s = if Data.Map.null s then 0 else (fst $ findMax s) + 1

getLoc :: Ident -> Env -> Loc
getLoc v (venv, _) =
  if member v venv then venv ! v else error ("Variable " ++ show v ++ " not declared")

getVal :: Loc -> Store -> ExprVal
getVal l s = s ! l

getFunc :: FName -> Env -> Func
getFunc fname (_, fenv) =
  if member fname fenv then fenv ! fname else error ("Function " ++ show fname ++ " not defined")

newVar :: Ident -> Loc -> Env -> Env
newVar var loc (venv, fenv) = (insert var loc venv, fenv)

newFunc :: FName -> Func -> Env -> Env
newFunc fName func (venv, fenv) = (venv, insert fName func fenv)

createFunc :: Type_specifier -> [Parameter_declaration] -> Compound_stm -> Func
createFunc fType params comp = (fType, params, comp)

updateStore :: Loc -> ExprVal -> Store -> Store
updateStore l n s = (insert l n s)

defaultValue :: Type_specifier -> ExprVal
defaultValue Tint = TInt 0
defaultValue Tbool = TBool False
defaultValue Tvoid = TVoid

unaryOp :: Unary_operator -> ExprVal -> ExprVal
unaryOp uop expr =
  case uop of
    Plus -> expr
    Negative -> (-1) * expr
    Logicalneg -> case expr of
      TBool b -> TBool (not b)
      TInt n -> if n == 0 then TBool True else TBool False
      _ -> error "Trying to negate invalid value"

isTrue :: ExprVal -> Bool
isTrue (TBool b) = b
isTrue (TInt n) = if n == 0 then False else True
isTrue _ = False

correctType :: ExprVal -> ExprVal -> Bool
correctType (TInt _) (TInt _) = True
correctType (TBool _) (TBool _) = True
correctType TVoid TVoid = True
correctType t a = error ("Cannot bind " ++ show a ++ " to type " ++ show t)

runDecl :: Declaration -> Env -> DeclCont -> Cont
runDecl (VarDecl _ []) _ _ = error "Declaration does not declare anything"
runDecl (VarDecl varType (vd:vds)) env kd =
  runSingleDecl varType vd env kd'
  where
    kd' env' s' =
      if Prelude.null vds
      then kd env' s'
      else runDecl (VarDecl varType vds) env' kd s'
runDecl (ExpDecl vd) env kd =
  runExpr vd env ke
  where
    ke :: ExprCont
    ke _ s =
      kd env s
runDecl (FuncDecl fType (FuncIdent fName params) comp) env kd =
  if (member fName (snd env)) then error ("Redeclaration of function: " ++ show fName)
  else
    let
      func = createFunc fType params comp
      env' = newFunc fName func  env
      in
    kd env'

runSingleDecl :: Type_specifier -> Init_declarator -> Env -> DeclCont -> Cont
runSingleDecl varType varDecl env kd =
  if (varType == Tvoid) then error "Cannot have void variable!"
  else
  case varDecl of
    OnlyDecl varName -> \s ->
      if (member varName (fst env)) then error "Redeclaration of variable!"
      else
      let
        l = newLoc s
        env' = newVar varName l env
        s' = updateStore l (defaultValue varType) s
      in
        kd env' s'
    InitDecl varName expr ->
      if (member varName (fst env)) then error "Redeclaration of variable!"
      else
      runExpr expr env ke
      where
        ke :: ExprCont
        ke val s =
          if not (correctType (defaultValue varType) val)
          then error "Wrong type!"
          else
            let
              l = newLoc s
              env' = newVar varName l env
              s' = updateStore l val s
            in
              kd env' s'

runDecls :: [Declaration] -> Env -> DeclCont -> Cont
runDecls [] env kd = kd env
runDecls (d:ds) env kd = runDecl d env kd'
  where
    kd' :: DeclCont
    kd' env' = runDecls ds env' kd

assign :: Ident -> Assignment_op -> Exp -> Env -> ExprCont -> Cont
assign ident assOp expr env ke =
  runExpr expr env ke'
  where
    ke' :: ExprCont
    ke' val s =
      let
        l = getLoc ident env
        curVal = getVal l s
        val' = calculateNewVal curVal val
        s' = updateStore l val' s
      in
        if not (correctType curVal val) then error "Wrong types!"
        else
        ke val' s'
      where
        calculateNewVal :: ExprVal -> ExprVal -> ExprVal
        calculateNewVal v1 v2 =
          case assOp of
            Assign -> v2
            AssignMul -> (v1 * v2)
            AssignDiv -> (exprDiv v1 v2)
            AssignMod -> (exprMod v1 v2)
            AssignAdd -> (v1 + v2)
            AssignSub -> (v1 - v2)

voidError :: t
voidError = error "Cannot evaluate void value"

runExpr :: Exp -> Env -> ExprCont -> Cont
runExpr (Eassign exp1 assOp exp2) env ke =
  case exp1 of
    Evar varName -> assign varName assOp exp2 env ke
    Epreinc expr -> runExpr (Eassign expr AssignAdd (Econst (Eint 1))) env ke'
      where
        ke' :: ExprCont
        ke' _ = runExpr (Eassign expr assOp exp2) env ke
    Epredec expr -> runExpr (Eassign expr AssignSub (Econst (Eint 1))) env ke'
      where
        ke' :: ExprCont
        ke' _ = runExpr (Eassign expr assOp exp2) env ke
    Epostinc expr -> runExpr (Eassign expr assOp exp2) env ke'
      where
        ke' :: ExprCont
        ke' _ = runExpr (Eassign expr AssignAdd (Econst (Eint 1))) env ke
    Epostdec expr -> runExpr (Eassign expr assOp exp2) env ke'
      where
        ke' :: ExprCont
        ke' _ = runExpr (Eassign expr AssignSub (Econst (Eint 1))) env ke
    _ -> error "Cannot assign not to a variable"
runExpr (Elor x y) env ke =
  runExpr x env ke'
  where
    ke' :: ExprCont
    ke' (TBool val) = if val then ke (TBool val)
                      else runExpr y env ke
    ke' (TInt val) = if (val /= 0) then ke (TBool True)
                     else runExpr y env ke
    ke' TVoid = voidError
runExpr (Eland x y) env ke =
  runExpr x env ke'
  where
    ke' :: ExprCont
    ke' (TBool val) = if val then runExpr y env ke
                      else ke (TBool False)
    ke' (TInt val) = if (val == 0) then runExpr y env ke
                     else ke (TBool False)
    ke' TVoid = voidError
runExpr (Eeq x y) env ke =
  runExpr x env ke'
  where
    ke' :: ExprCont
    ke' val = runExpr y env (\v -> ke $ TBool (val == v))
runExpr (Eneq x y) env ke =
  runExpr x env ke'
  where
    ke' :: ExprCont
    ke' val = runExpr y env (\v -> ke $ TBool (val /= v))
runExpr (Elthen x y) env ke =
  runExpr x env ke'
  where
    ke' :: ExprCont
    ke' val = runExpr y env (\v -> ke $ TBool (val < v))
runExpr (Egrthen x y) env ke =
  runExpr x env ke'
  where
    ke' :: ExprCont
    ke' val = runExpr y env (\v -> ke $ TBool (val > v))
runExpr (Ele x y) env ke =
  runExpr x env ke'
  where
    ke' :: ExprCont
    ke' val = runExpr y env (\v -> ke $ TBool (val <= v))
runExpr (Ege x y) env ke =
  runExpr x env ke'
  where
    ke' :: ExprCont
    ke' val = runExpr y env (\v -> ke $ TBool (val >= v))
runExpr (Eplus x y) env ke =
  runExpr x env ke'
  where
    ke' :: ExprCont
    ke' val = runExpr y env (\v -> ke $ val + v)
runExpr (Eminus x y) env ke =
  runExpr x env ke'
  where
    ke' :: ExprCont
    ke' val = runExpr y env (\v -> ke $ val - v)
runExpr (Etimes x y) env ke =
  runExpr x env ke'
  where
    ke' :: ExprCont
    ke' val = runExpr y env (\v -> ke $ val * v)
runExpr (Ediv x y) env ke =
  runExpr x env ke'
  where
    ke' :: ExprCont
    ke' val = runExpr y env (\v -> ke $! exprDiv val v)
runExpr (Emod x y) env ke =
  runExpr x env ke'
  where
    ke' :: ExprCont
    ke' val = runExpr y env (\v -> ke $! exprMod val v)
runExpr (Epreinc expr) env ke =
  runExpr (Eassign expr AssignAdd (Econst (Eint 1))) env ke
runExpr (Epredec expr) env ke =
  runExpr (Eassign expr AssignSub (Econst (Eint 1))) env ke
runExpr (Epreop uop expr) env ke=
  runExpr expr env (\val -> ke $ unaryOp uop val)
runExpr (Epostinc expr) env ke =
  runExpr expr env ke'
  where
    ke' :: ExprCont
    ke' val =
      runExpr (Eassign expr AssignAdd (Econst (Eint 1))) env ke''
      where
        ke'' :: ExprCont
        ke'' _ = ke val
runExpr (Epostdec expr) env ke =
  runExpr expr env ke'
  where
    ke' :: ExprCont
    ke' val =
      runExpr (Eassign expr AssignSub (Econst (Eint 1))) env ke''
      where
        ke'' :: ExprCont
        ke'' _ = ke val
runExpr (Evar varName) env ke = \s ->
  ke (getVal  (getLoc varName env) s) s
runExpr (Econst constant) _ ke =
  case constant of
    Eint n -> ke (TInt n)
    Ebool b -> case b of
      Vtrue -> ke (TBool True)
      Vfalse -> ke (TBool False)
runExpr (Efunk fName) env ke =
  let
    (fType, _, comp) = getFunc fName env
    ks _ = ke (defaultValue fType)
    kjc _ = error "Continue outside of loop"
    kbc _ = error "Break outside of loop"
  in
    runStmt (CompStm comp) env ks kjc kbc ke
runExpr (Efunkpar fName args) env ke =
  let
    (fType, params, comp) = getFunc fName env
  in
    runFunc fType comp params args env ke

runFunc :: Type_specifier -> Compound_stm -> [Parameter_declaration] -> [Exp] -> Env -> ExprCont -> Cont
runFunc _ _ (_:_) [] _ _ = error "Too few arguments!"
runFunc fType comp [] args env ke =
  if not $ Prelude.null args then error "Too many arguments!"
  else
    let
      ks :: StmCont
      ks _ = ke (defaultValue fType)
      kjc _ = error "Continue outside of loop"
      kbc _ = error "Break outside of loop"
    in
      runStmt (CompStm comp) env ks kjc kbc ke
runFunc fType comp ((TypeAndParam pType pId):ps) (expr:exps) env ke =
  runExpr expr env ke'
  where
    ke' :: ExprCont
    ke' val s =
      let
        l = newLoc s
        env' = newVar pId l env
        s' = updateStore l val s
      in
        if correctType (defaultValue pType) val
        then runFunc fType comp ps exps env' ke s'
        else error "Wrong types"

runStmts :: [Stm] -> Env -> StmCont -> StmCont -> StmCont -> ReturnH -> Cont
runStmts [] env ks _ _ _ = ks env
runStmts (s:ss) env ks ksc ksb retH = runStmt s env ks' ksc ksb retH
  where
    ks' :: StmCont
    ks' env' = runStmts ss env' ks ksc ksb retH

runStmt :: Stm -> Env -> StmCont -> StmCont -> StmCont -> ReturnH -> Cont
runStmt (DeclStm decl) env ks _ _ _ =
  runDecl decl env kd
  where
    kd :: DeclCont
    kd env' = ks env'
runStmt (CompStm stm) env ks ksc ksb retH =
  case stm of
    SEmptyComp -> ks env
    SStmtComp ss -> runStmts ss env (\_ -> ks env) (\_ -> ksc env) (\_ -> ksb env) retH
    SDeclComp ds -> runDecls ds env (\_ -> ks env)
    SMixComp ds ss -> runDecls ds env
      (\env' -> runStmts ss env' (\_ -> ks env) (\_ -> ksc env) (\_ -> ksb env) retH)
runStmt (ExprStm expStm) env ks _ _ _ =
  case expStm of
    SEmptyExpr -> ks env
    SExpr expr -> runExpr expr env (\_ -> ks env)
runStmt (SelecStm sel) env ks ksc ksb retH =
  case sel of
    SIf expr comp -> runExpr expr env (\val ->
                                          if (isTrue val)
                                          then runStmt (CompStm comp) env ks ksc ksb retH
                                          else ks env)
    SIfElse expr comp1 comp2 -> runExpr expr env
                                (\val ->
                                   if (isTrue val)
                                   then runStmt (CompStm comp1) env ks ksc ksb retH
                                   else runStmt (CompStm comp2) env ks ksc ksb retH)
runStmt (IterStm iter) env ks ksc ksb retH =
  case iter of
    SWhile expr comp -> runExpr expr env (\val ->
                                             if (isTrue val)
                                             then runStmt (CompStm comp) env ks' ksc' ksb' retH
                                             else ks env)
      where
        ks' :: StmCont
        ks' _ = runStmt (IterStm iter) env ks ksc ksb retH
        ksc' :: StmCont
        ksc' _ = runStmt (IterStm iter) env ks ksc ksb retH
        ksb' :: StmCont
        ksb' _ = ks env
    SDoWhile comp expr -> runStmt (CompStm comp) env ks' ks' ksb' retH
      where
        ks' :: StmCont
        ks' _ = runStmt (IterStm (SWhile expr comp)) env ks ksc ksb retH
        ksb' :: StmCont
        ksb' _ = ks env
    SFor expStm1 expStm2 expr comp -> runStmt (ExprStm expStm1) env ks' ksc ksb retH
      where
        ks' :: StmCont
        ks' _ = case expStm2 of
          SEmptyExpr -> runStmt (CompStm comp) env ks'' ksc' ksb' retH
          SExpr exp2 -> runExpr exp2 env
            (\val ->
                if (isTrue val)
                then runStmt (CompStm comp) env ks'' ksc' ksb' retH
                else ks env)
          where
            ks'' :: StmCont
            ks'' _ = runExpr expr env (\_ ->
                                          runStmt (IterStm
                                                    (SFor
                                                     SEmptyExpr
                                                     expStm2
                                                     expr
                                                     comp))
                                         env ks ksc ksb retH)
            ksc' _ = runExpr expr env (\_ ->
                                          runStmt (IterStm
                                                    (SFor
                                                     SEmptyExpr
                                                     expStm2
                                                     expr
                                                     comp))
                                         env ks ksc ksb retH)
            ksb' _ = ks env
    SForEmpty expStm1 expStm2 comp ->
      runStmt (ExprStm expStm1) env ks' ksc ksb retH
      where
        ks' :: StmCont
        ks' _ = case expStm2 of
          SEmptyExpr ->
            runStmt (IterStm (SWhile (Econst (Ebool (Vtrue))) comp)) env ks ksc' ksb' retH
          SExpr exp' -> runStmt (IterStm (SWhile exp' comp)) env ks ksc' ksb' retH
          where
            ksc' _ =
              runStmt (IterStm (SWhile (Econst (Ebool (Vtrue))) comp)) env ks ksc ksb retH
            ksb' _ = ks env
runStmt (JumpStm jump) env _ ksc ksb retH =
  case jump of
    SjumpCont -> ksc env
    SjumpBreak -> ksb env
    SjumpReturn -> retH TVoid
    SjumpRetExp expr -> runExpr expr env (\val -> retH val)
runStmt (PrintStm (Sprint exps)) env ks ksc ksb retH =
  case exps of
    [] -> ks env
    (e:es) -> runExpr e env ke
      where
        ke :: ExprCont
        ke val s = do
          case val of
            TInt n -> print n
            TBool b -> print b
            TVoid -> error "Invalid value - void"
          runStmt (PrintStm (Sprint es)) env ks ksc ksb retH s

runProgram :: Program -> Ans
runProgram (Progr decl) =
  runProgram' decl Data.Map.empty (Data.Map.empty, Data.Map.empty)
    where
      runProgram' :: [Declaration] -> Store -> Env -> Ans
      runProgram' [] s env = return (s, env)
      runProgram' decls s env = runDecls decls env kd s
        where
          kd :: DeclCont
          kd env' =
            if member (Ident "main") (snd env')
            then
              runExpr (Efunk (Ident "main")) env' (\_ s' -> return (s',env'))
            else
              error "No main function!"
