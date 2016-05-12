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
  TInt x - TInt y = TInt (x - y)
  TInt x * TInt y = TInt (x * y)
  abs (TInt x) = TInt (abs x)
  signum (TInt x) = TInt (signum x)
  fromInteger x = TInt x

exprDiv :: ExprVal -> ExprVal -> ExprVal
exprDiv (TInt x) (TInt y) =
  if y == 0 then error "Division by zero"
  else TInt (div x y)

exprMod :: ExprVal -> ExprVal -> ExprVal
exprMod (TInt x) (TInt y) =
  if y == 0 then error "Division by zero"
  else TInt (mod x y)

type Loc = Int
type Store = Map Loc ExprVal

type FName = Ident
type Func = ([Ident], Compound_stm)

type Record = Map Ident Loc

type VEnv = Map Ident Loc
type PEnv = Map FName Func

type Env = (VEnv, PEnv)

type Ans = Store
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
unaryOp uop exp =
  case uop of
    Plus -> exp
    Negative -> (-1) * exp
    Logicalneg -> case exp of
      TBool b -> TBool (not b)
      TInt n -> if n == 0 then TBool True else TBool False

isTrue :: ExprVal -> Bool
isTrue (TBool b) = b
isTrue (TInt n) = if n == 0 then False else True

correctType :: ExprVal -> ExprVal -> Bool
correctType (TInt _) (TInt _) = True
correctType (TBool _) (TBool _) = True
correctType TVoid TVoid = True
correctType t a = error ("Cannot bind " ++ show a ++ " to type " ++ show t)

execDecl :: Declaration -> Env -> ContD -> Cont
execDecl (VarDecl varType (vd:vds)) env kd =
  execSingleDecl varType vd env kd'
  where
    kd' env' s' =
      execDecl (VarDecl varType vds) env' kd s'
execDecl (ExpDecl vd) env kd =
  execExpr vd env ke
  where
    ke :: ContE
    ke val s =
      kd env s
execDecl _ env kd = kd env

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
    InitDecl varName exp -> 
      if (member varName (fst env)) then error "Redeclaration of variable!"
      else
      execExpr exp env ke
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
execAssign ident assOp exp env ke =
  execExpr exp env ke'
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

execExpr :: Exp -> Env -> ContE -> Cont
execExpr (Eassign exp1 assOp exp2) env ke =
  case exp1 of
    Evar varName -> execAssign varName assOp exp2 env ke
    Epreinc exp -> execExpr (Eassign exp AssignAdd (Econst (Eint 1))) env ke'
      where
        ke' :: ContE
        ke' val = execExpr (Eassign exp assOp exp2) env ke
    Epredec exp -> execExpr (Eassign exp AssignSub (Econst (Eint 1))) env ke'
      where
        ke' :: ContE
        ke' val = execExpr (Eassign exp assOp exp2) env ke
    Epostinc exp -> execExpr (Eassign exp assOp exp2) env ke'
      where
        ke' :: ContE
        ke' val = execExpr (Eassign exp AssignAdd (Econst (Eint 1))) env ke
    Epostdec exp -> execExpr (Eassign exp assOp exp2) env ke'
      where
        ke' :: ContE
        ke' val = execExpr (Eassign exp AssignSub (Econst (Eint 1))) env ke
    _ -> error "Cannot assign not to a variable"
execExpr (Elor x y) env ke =
  execExpr x env ke'
  where
    ke' :: ContE
    ke' (TBool val) = if val then ke (TBool val)
                      else execExpr y env ke
    ke' (TInt val) = if (val /= 0) then ke (TBool True)
                     else execExpr y env ke
execExpr (Eland x y) env ke =
  execExpr x env ke'
  where
    ke' :: ContE
    ke' (TBool val) = if val then execExpr y env ke
                      else ke (TBool False)
    ke' (TInt val) = if (val == 0) then execExpr y env ke 
                     else ke (TBool False)
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
    ke' val = execExpr y env (\v -> ke $ exprDiv val v)
execExpr (Emod x y) env ke =
  execExpr x env ke'
  where
    ke' :: ContE
    ke' val = execExpr y env (\v -> ke $ exprMod val v)
execExpr (Epreinc exp) env ke =
  execExpr (Eassign exp AssignAdd (Econst (Eint 1))) env ke
execExpr (Epredec exp) env ke =
  execExpr (Eassign exp AssignSub (Econst (Eint 1))) env ke
execExpr (Epreop uop exp) env ke=
  execExpr exp env (\val -> ke $ unaryOp uop val)
execExpr (Epostinc exp) env ke =
  execExpr exp env ke'
  where
    ke' :: ContE
    ke' val =
      execExpr (Eassign exp AssignAdd (Econst (Eint 1))) env ke''
      where
        ke'' :: ContE
        ke'' _ = ke val
execExpr (Epostdec exp) env ke =
  execExpr exp env ke'
  where
    ke' :: ContE
    ke' val =
      execExpr (Eassign exp AssignSub (Econst (Eint 1))) env ke''
      where
        ke'' :: ContE
        ke'' _ = ke val
execExpr (Evar varName) env ke = \s ->
  ke (getVal  (getLoc varName env) s) s
execExpr (Econst const) env ke =
  case const of
    Eint n -> ke (TInt n)
    Ebool b -> case b of
      Vtrue -> ke (TBool True)
      Vfalse -> ke (TBool False)
execExpr (Efunkpar fName args) env ke =
  execFunc fName args env ke
execExpr _ _ _ = \s -> s

--TODO Do it properly motherfucker
execFunc :: Ident -> [Exp] -> Env -> ContE -> Cont
execFunc fName args env ke =
  let
    (args, func) = getFunc fName env
  in
  ke 0


execStmts :: [Stm] -> Env -> ContS -> ContS -> ContS -> ReturnH -> Cont
execStmts [] env ks _ _ _ = ks env
execStmts (s:ss) env ks ksc ksb retH = execStmt s env ks' ksc ksb retH
  where
    ks' :: ContS
    ks' env' = execStmts ss env' ks ksc ksb retH

execStmt :: Stm -> Env -> ContS -> ContS -> ContS -> ReturnH -> Cont
execStmt (CompStm stm) env ks ksc ksb retH =
  case stm of
    SEmptyComp -> ks env
    SStmtComp ss -> execStmts ss env (\_ -> ks env) (\_ -> ksc env) (\_ -> ksb env) retH
    SDeclComp ds -> execDecls ds env (\_ -> ks env)
    SMixComp ds ss -> execDecls ds env
      (\env' -> execStmts ss env' (\_ -> ks env) (\_ -> ksc env) (\_ -> ksb env) retH)
execStmt (ExprStm expStm) env ks ksc ksb retH =
  case expStm of
    SEmptyExpr -> ks env
    SExpr exp -> execExpr exp env (\_ -> ks env)
execStmt (SelecStm sel) env ks ksc ksb retH =
  case sel of
    SIf exp comp -> execExpr exp env (\val ->
                                        if (isTrue val)
                                        then execStmt (CompStm comp) env ks ksc ksb retH
                                        else ks env)
    SIfElse exp comp1 comp2 -> execExpr exp env (\val ->
                                        if (isTrue val)
                                        then execStmt (CompStm comp1) env ks ksc ksb retH
                                        else execStmt (CompStm comp2) env ks ksc ksb retH)
execStmt (IterStm iter) env ks ksc ksb retH =
  case iter of
    SWhile exp comp -> execExpr exp env (\val ->
                                           if (isTrue val)
                                           then execStmt (CompStm comp) env ks' ksc' ksb' retH
                                           else ks env)
      where
        ks' :: ContS
        ks' env' = execStmt (IterStm iter) env ks ksc ksb retH
        ksc' :: ContS
        ksc' env' = execStmt (IterStm iter) env ks ksc ksb retH
        ksb' :: ContS
        ksb' env' = ks env
    SDoWhile comp exp -> execStmt (CompStm comp) env ks' ks' ksb' retH
      where
        ks' :: ContS
        ks' env' = execStmt (IterStm (SWhile exp comp)) env ks ksc ksb retH
        ksb' :: ContS
        ksb' env' = ks env
    SFor expStm1 expStm2 exp comp -> execStmt (ExprStm expStm1) env ks' ksc ksb retH
      where
        ks' :: ContS
        ks' env' = case expStm2 of
          SEmptyExpr -> execStmt (CompStm comp) env ks'' ksc' ksb' retH
          SExpr exp2 -> execExpr exp2 env
            (\val ->
                if (isTrue val)
                then execStmt (CompStm comp) env ks'' ksc' ksb' retH
                else ks env)
          where
            ks'' :: ContS
            ks'' env'' = execExpr exp env (\_ ->
                                              execStmt (IterStm
                                                        (SFor
                                                         SEmptyExpr
                                                         expStm2
                                                         exp
                                                         comp))
                                            env ks ksc ksb retH)
            ksc' env'' = execExpr exp env (\_ ->
                                              execStmt (IterStm
                                                        (SFor
                                                         SEmptyExpr
                                                         expStm2
                                                         exp
                                                         comp))
                                            env ks ksc ksb retH)
            ksb' env'' = ks env
    SForEmpty expStm1 expStm2 comp ->
      execStmt (ExprStm expStm1) env ks' ksc ksb retH
      where
        ks' :: ContS
        ks' env' = case expStm2 of
          SEmptyExpr ->
            execStmt (IterStm (SWhile (Econst (Ebool (Vtrue))) comp)) env ks ksc' ksb' retH
          SExpr exp' -> execStmt (IterStm (SWhile exp' comp)) env ks ksc' ksb' retH
          where
            ksc' env'' =
              execStmt (IterStm (SWhile (Econst (Ebool (Vtrue))) comp)) env ks ksc ksb retH
            ksb' env'' = ks env
execStmt (JumpStm jump) env ks ksc ksb retH =
  case jump of
    SjumpCont -> ksc env
    SjumpBreak -> ksb env
    SjumpReturn -> retH TVoid
    SjumpRetExp exp -> execExpr exp env (\val -> retH val)
execStmt _ env k _ _ _ = k env

runProgram :: Program -> Store
runProgram (Progr decl) =
  runProgram decl newStore newEnv
    where
      runProgram :: [Declaration] -> Store -> Env -> Store
      runProgram [] s env = s
      runProgram decls s env = execDecls decls env kd s
        where
          kd :: ContD
          kd env s = s
