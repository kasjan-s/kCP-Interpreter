module ExeckCP where

import AbskCP

import Data.Map

data ExprVal =
      TInt Integer
    | TBool Bool
    deriving (Ord, Eq)

instance Num ExprVal where
  TInt x + TInt y = TInt (x + y)
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

type PName = Ident
type Proc = ([Ident], Compound_stm)

type Record = Map Ident Loc

type VEnv = Map Ident Loc
type PEnv = Map PName Proc

type Env = (VEnv, PEnv)

type Ans = Store
type Cont = Store -> Ans
type ContD = Env -> Cont
type ContE = ExprVal -> Cont

newLoc :: Store -> Loc
newLoc s = if Data.Map.null s then 0 else (+1) . fst $ findMax s

getLoc :: Ident -> Env -> Loc
getLoc v (venv, _) = venv ! v

getVal :: Loc -> Store -> ExprVal
getVal l s = s ! l

getFunc :: PName -> Env -> Proc
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

execDecl :: Declaration -> Env -> ContD -> Cont
execDecl (VarDecl varType (vd:vds)) env kd =
  execSingleDecl varType vd env kd'
  where
    kd' env' s' =
      execDecl (VarDecl varType vds) env' kd s'

execSingleDecl :: Type_specifier -> Init_declarator -> Env -> ContD -> Cont
execSingleDecl varType varDecl env kd =
  case varDecl of
    OnlyDecl varName -> \s ->
      let
        l = newLoc s
        env' = newVar varName l env
        s' = updateStore l (defaultValue varType) s
      in
        kd env' s'
    InitDecl varName exp -> execExpr exp env ke
      where
        ke :: ContE
        ke val s =
          let
            l = newLoc s
            env' = newVar varName l env
            s' = updateStore l val s
          in
            kd env' s'


execAssign :: Ident -> Assignment_op -> Exp -> Env -> ContE -> Cont
execAssign ident assOp exp env ke =
  execExpr exp env ke'
  where
    ke' :: ContE
    ke' val s =
      let
        l = getLoc ident env
        curVal = getVal l s
        s' = updateStore l (calculateNewVal curVal val) s
      in
        ke val s'
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
    _ -> \s -> s -- TODO: Co tu powinno byc?
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
-- execExpr (Epostinc exp) env ke =
--   execExpr exp env ke'
--   where
--     ke' :: ContE
--     ke' val s = let
--       l = getLoc 
--       s' = updateStore 
execExpr (Evar varName) env ke = \s ->
  ke (getVal  (getLoc varName env) s) s
execExpr (Econst const) env ke =
  case const of
    Eint n -> ke (TInt n)
    Ebool b -> case b of
      Vtrue -> ke (TBool True)
      Vfalse -> ke (TBool False)
execExpr _ _ _ = \s -> s

-- execDecl :: Declaration -> Store -> Env -> ContD -> Cont
-- execDecl (Declaration specifier (d:ds)) s env kd =
--   execDecl (Declaration specifier ds) s' env' kd'
--   where

-- runProgram :: Program -> IO ()
-- runProgram (Progr decl) =
--   do
--     runProgram decl newStore newEnv
--     return ()
--     where
--       runProgram :: [External_declaration] -> Store -> Env -> IO Store
--       runProgram [] s env = return s
--       runProgram list s env = k s
--                               where
--                                 k = runExternals list env (\_ -> return s) (\_ -> return s)
