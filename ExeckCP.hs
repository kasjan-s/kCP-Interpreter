module ExeckCP where

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
type ContD = Env -> Cont
type ContE = ExprVal -> Cont
type ContS = Env -> Cont
type ReturnH = ExprVal -> Cont

newLoc :: Store -> Loc
newLoc s = if Data.Map.null s then 0 else (+1) . fst $ findMax s

getLoc :: Ident -> Env -> Loc
getLoc v (venv, _) = venv ! v

getVal :: Loc -> Store -> ExprVal
getVal l s = s ! l

getFunc :: FName -> Env -> Func
getFunc fname (_, fenv) = fenv ! fname

newVar :: Ident -> Loc -> Env -> Env
newVar var loc (venv, fenv) = (insert var loc venv, fenv)

newFunc :: FName -> Func -> Env -> Env
newFunc fName func (venv, fenv) = (venv, insert fName func fenv)

createFunc :: Type_specifier -> [Parameter_declaration] -> Compound_stm -> Func
createFunc fType params comp = (fType, params, comp)

updateStore :: Loc -> ExprVal -> Store -> Store
updateStore l n s = (insert l n s)

newStore :: Store
newStore = Data.Map.empty

newEnv :: Env
newEnv = (Data.Map.empty, Data.Map.empty)

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

execDecl :: Declaration -> Env -> ContD -> Cont
execDecl (VarDecl _ []) _ _ = error "Declaration does not declare anything"
execDecl (VarDecl varType (vd:vds)) env kd =
  execSingleDecl varType vd env kd'
  where
    kd' env' s' =
      if Prelude.null vds
      then kd env' s'
      else execDecl (VarDecl varType vds) env' kd s'
execDecl (ExpDecl vd) env kd =
  execExpr vd env ke
  where
    ke :: ContE
    ke _ s =
      kd env s
execDecl (FuncDecl fType (FuncIdent fName params) comp) env kd =
  if (member fName (snd env)) then error ("Redeclaration of function: " ++ show fName)
  else
    let
      func = createFunc fType params comp
      env' = newFunc fName func  env
      in
    kd env'

execSingleDecl :: Type_specifier -> Init_declarator -> Env -> ContD -> Cont
execSingleDecl varType varDecl env kd =
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
      execExpr expr env ke
      where
        ke :: ContE
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

execDecls :: [Declaration] -> Env -> ContD -> Cont
execDecls [] env kd = kd env
execDecls (d:ds) env kd = execDecl d env kd'
  where
    kd' :: ContD
    kd' env' = execDecls ds env' kd

execAssign :: Ident -> Assignment_op -> Exp -> Env -> ContE -> Cont
execAssign ident assOp expr env ke =
  execExpr expr env ke'
  where
    ke' :: ContE
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

voidError = error "Cannot evaluate void value"

execExpr :: Exp -> Env -> ContE -> Cont
execExpr (Eassign exp1 assOp exp2) env ke =
  case exp1 of
    Evar varName -> execAssign varName assOp exp2 env ke
    Epreinc expr -> execExpr (Eassign expr AssignAdd (Econst (Eint 1))) env ke'
      where
        ke' :: ContE
        ke' _ = execExpr (Eassign expr assOp exp2) env ke
    Epredec expr -> execExpr (Eassign expr AssignSub (Econst (Eint 1))) env ke'
      where
        ke' :: ContE
        ke' _ = execExpr (Eassign expr assOp exp2) env ke
    Epostinc expr -> execExpr (Eassign expr assOp exp2) env ke'
      where
        ke' :: ContE
        ke' _ = execExpr (Eassign expr AssignAdd (Econst (Eint 1))) env ke
    Epostdec expr -> execExpr (Eassign expr assOp exp2) env ke'
      where
        ke' :: ContE
        ke' _ = execExpr (Eassign expr AssignSub (Econst (Eint 1))) env ke
    _ -> error "Cannot assign not to a variable"
execExpr (Elor x y) env ke =
  execExpr x env ke'
  where
    ke' :: ContE
    ke' (TBool val) = if val then ke (TBool val)
                      else execExpr y env ke
    ke' (TInt val) = if (val /= 0) then ke (TBool True)
                     else execExpr y env ke
    ke' TVoid = voidError
execExpr (Eland x y) env ke =
  execExpr x env ke'
  where
    ke' :: ContE
    ke' (TBool val) = if val then execExpr y env ke
                      else ke (TBool False)
    ke' (TInt val) = if (val == 0) then execExpr y env ke
                     else ke (TBool False)
    ke' TVoid = voidError
execExpr (Eeq x y) env ke =
  execExpr x env ke'
  where
    ke' :: ContE
    ke' val = execExpr y env (\v -> ke $ TBool (val == v))
execExpr (Eneq x y) env ke =
  execExpr x env ke'
  where
    ke' :: ContE
    ke' val = execExpr y env (\v -> ke $ TBool (val /= v))
execExpr (Elthen x y) env ke =
  execExpr x env ke'
  where
    ke' :: ContE
    ke' val = execExpr y env (\v -> ke $ TBool (val < v))
execExpr (Egrthen x y) env ke =
  execExpr x env ke'
  where
    ke' :: ContE
    ke' val = execExpr y env (\v -> ke $ TBool (val > v))
execExpr (Ele x y) env ke =
  execExpr x env ke'
  where
    ke' :: ContE
    ke' val = execExpr y env (\v -> ke $ TBool (val <= v))
execExpr (Ege x y) env ke =
  execExpr x env ke'
  where
    ke' :: ContE
    ke' val = execExpr y env (\v -> ke $ TBool (val >= v))
execExpr (Eplus x y) env ke =
  execExpr x env ke'
  where
    ke' :: ContE
    ke' val = execExpr y env (\v -> ke $ val + v)
execExpr (Eminus x y) env ke =
  execExpr x env ke'
  where
    ke' :: ContE
    ke' val = execExpr y env (\v -> ke $ val - v)
execExpr (Etimes x y) env ke =
  execExpr x env ke'
  where
    ke' :: ContE
    ke' val = execExpr y env (\v -> ke $ val * v)
execExpr (Ediv x y) env ke =
  execExpr x env ke'
  where
    ke' :: ContE
    ke' val = execExpr y env (\v -> ke $! exprDiv val v)
execExpr (Emod x y) env ke =
  execExpr x env ke'
  where
    ke' :: ContE
    ke' val = execExpr y env (\v -> ke $! exprMod val v)
execExpr (Epreinc expr) env ke =
  execExpr (Eassign expr AssignAdd (Econst (Eint 1))) env ke
execExpr (Epredec expr) env ke =
  execExpr (Eassign expr AssignSub (Econst (Eint 1))) env ke
execExpr (Epreop uop expr) env ke=
  execExpr expr env (\val -> ke $ unaryOp uop val)
execExpr (Epostinc expr) env ke =
  execExpr expr env ke'
  where
    ke' :: ContE
    ke' val =
      execExpr (Eassign expr AssignAdd (Econst (Eint 1))) env ke''
      where
        ke'' :: ContE
        ke'' _ = ke val
execExpr (Epostdec expr) env ke =
  execExpr expr env ke'
  where
    ke' :: ContE
    ke' val =
      execExpr (Eassign expr AssignSub (Econst (Eint 1))) env ke''
      where
        ke'' :: ContE
        ke'' _ = ke val
execExpr (Evar varName) env ke = \s ->
  ke (getVal  (getLoc varName env) s) s
execExpr (Econst constant) _ ke =
  case constant of
    Eint n -> ke (TInt n)
    Ebool b -> case b of
      Vtrue -> ke (TBool True)
      Vfalse -> ke (TBool False)
execExpr (Efunk fName) env ke =
  let
    (fType, _, comp) = getFunc fName env
    ks _ = ke (defaultValue fType)
    kjc _ = error "Continue outside of loop"
    kbc _ = error "Break outside of loop"
  in
    execStmt (CompStm comp) env ks kjc kbc ke
execExpr (Efunkpar fName args) env ke =
  let
    (fType, params, comp) = getFunc fName env
  in
    execFunc fType comp params args env ke

execFunc :: Type_specifier -> Compound_stm -> [Parameter_declaration] -> [Exp] -> Env -> ContE -> Cont
execFunc _ _ (_:_) [] _ _ = error "Too few arguments!"
execFunc fType comp [] args env ke =
  if not $ Prelude.null args then error "Too many arguments!"
  else
    let
      ks :: ContS
      ks _ = ke (defaultValue fType)
      kjc _ = error "Continue outside of loop"
      kbc _ = error "Break outside of loop"
    in
      execStmt (CompStm comp) env ks kjc kbc ke
execFunc fType comp ((TypeAndParam pType pId):ps) (expr:exps) env ke =
  execExpr expr env ke'
  where
    ke' :: ContE
    ke' val s =
      let
        l = newLoc s
        env' = newVar pId l env
        s' = updateStore l val s
      in
        if correctType (defaultValue pType) val
        then execFunc fType comp ps exps env' ke s'
        else error "Wrong types"

execStmts :: [Stm] -> Env -> ContS -> ContS -> ContS -> ReturnH -> Cont
execStmts [] env ks _ _ _ = ks env
execStmts (s:ss) env ks ksc ksb retH = execStmt s env ks' ksc ksb retH
  where
    ks' :: ContS
    ks' env' = execStmts ss env' ks ksc ksb retH

execStmt :: Stm -> Env -> ContS -> ContS -> ContS -> ReturnH -> Cont
execStmt (DeclStm decl) env ks _ _ _ =
  execDecl decl env kd
  where
    kd :: ContD
    kd env' = ks env'
execStmt (CompStm stm) env ks ksc ksb retH =
  case stm of
    SEmptyComp -> ks env
    SStmtComp ss -> execStmts ss env (\_ -> ks env) (\_ -> ksc env) (\_ -> ksb env) retH
    SDeclComp ds -> execDecls ds env (\_ -> ks env)
    SMixComp ds ss -> execDecls ds env
      (\env' -> execStmts ss env' (\_ -> ks env) (\_ -> ksc env) (\_ -> ksb env) retH)
execStmt (ExprStm expStm) env ks _ _ _ =
  case expStm of
    SEmptyExpr -> ks env
    SExpr expr -> execExpr expr env (\_ -> ks env)
execStmt (SelecStm sel) env ks ksc ksb retH =
  case sel of
    SIf expr comp -> execExpr expr env (\val ->
                                          if (isTrue val)
                                          then execStmt (CompStm comp) env ks ksc ksb retH
                                          else ks env)
    SIfElse expr comp1 comp2 -> execExpr expr env
                                (\val ->
                                   if (isTrue val)
                                   then execStmt (CompStm comp1) env ks ksc ksb retH
                                   else execStmt (CompStm comp2) env ks ksc ksb retH)
execStmt (IterStm iter) env ks ksc ksb retH =
  case iter of
    SWhile expr comp -> execExpr expr env (\val ->
                                             if (isTrue val)
                                             then execStmt (CompStm comp) env ks' ksc' ksb' retH
                                             else ks env)
      where
        ks' :: ContS
        ks' _ = execStmt (IterStm iter) env ks ksc ksb retH
        ksc' :: ContS
        ksc' _ = execStmt (IterStm iter) env ks ksc ksb retH
        ksb' :: ContS
        ksb' _ = ks env
    SDoWhile comp expr -> execStmt (CompStm comp) env ks' ks' ksb' retH
      where
        ks' :: ContS
        ks' _ = execStmt (IterStm (SWhile expr comp)) env ks ksc ksb retH
        ksb' :: ContS
        ksb' _ = ks env
    SFor expStm1 expStm2 expr comp -> execStmt (ExprStm expStm1) env ks' ksc ksb retH
      where
        ks' :: ContS
        ks' _ = case expStm2 of
          SEmptyExpr -> execStmt (CompStm comp) env ks'' ksc' ksb' retH
          SExpr exp2 -> execExpr exp2 env
            (\val ->
                if (isTrue val)
                then execStmt (CompStm comp) env ks'' ksc' ksb' retH
                else ks env)
          where
            ks'' :: ContS
            ks'' _ = execExpr expr env (\_ ->
                                          execStmt (IterStm
                                                    (SFor
                                                     SEmptyExpr
                                                     expStm2
                                                     expr
                                                     comp))
                                         env ks ksc ksb retH)
            ksc' _ = execExpr expr env (\_ ->
                                          execStmt (IterStm
                                                    (SFor
                                                     SEmptyExpr
                                                     expStm2
                                                     expr
                                                     comp))
                                         env ks ksc ksb retH)
            ksb' _ = ks env
    SForEmpty expStm1 expStm2 comp ->
      execStmt (ExprStm expStm1) env ks' ksc ksb retH
      where
        ks' :: ContS
        ks' _ = case expStm2 of
          SEmptyExpr ->
            execStmt (IterStm (SWhile (Econst (Ebool (Vtrue))) comp)) env ks ksc' ksb' retH
          SExpr exp' -> execStmt (IterStm (SWhile exp' comp)) env ks ksc' ksb' retH
          where
            ksc' _ =
              execStmt (IterStm (SWhile (Econst (Ebool (Vtrue))) comp)) env ks ksc ksb retH
            ksb' _ = ks env
execStmt (JumpStm jump) env _ ksc ksb retH =
  case jump of
    SjumpCont -> ksc env
    SjumpBreak -> ksb env
    SjumpReturn -> retH TVoid
    SjumpRetExp expr -> execExpr expr env (\val -> retH val)
execStmt (PrintStm (Sprint exps)) env ks ksc ksb retH =
  case exps of
    [] -> ks env
    (e:es) -> execExpr e env ke
      where
        ke :: ContE
        ke val s = do
          case val of
            TInt n -> print n
            TBool b -> print b
            TVoid -> error "Invalid value - void"
          execStmt (PrintStm (Sprint es)) env ks ksc ksb retH s

runProgram :: Program -> Ans
runProgram (Progr decl) =
  runProgram' decl newStore newEnv
    where
      runProgram' :: [Declaration] -> Store -> Env -> Ans
      runProgram' [] s env = return (s, env)
      runProgram' decls s env = execDecls decls env kd s
        where
          kd :: ContD
          kd env' =
            if member (Ident "main") (snd env')
            then
              execExpr (Efunk (Ident "main")) env' (\_ s' -> return (s',env'))
            else
              error "No main function!"
