module ExeckCP where

import AbskCP

import Data.Map

data ExprVal =
      Void
    | TInt Integer
    | TBool Bool
    | TRecord Record

type Loc = Int
type Store = Map Loc ExprVal

type FName = Ident
type Func = ([Ident], Compound_stm)

type Record = Map Ident Loc

type VEnv = Map Ident Loc
type FEnv = Map FName Func

type Env = (VEnv, FEnv)


type Cont = Store -> IO (Store)
type ContD = Env -> Cont
type ContE = ExprVal -> Cont

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

-- execDecl :: Declaration -> Store -> Env -> ContD -> Cont
-- execDecl (Declaration specifier (d:ds)) s env kd =
--   execDecl (Declaration specifier ds) s' env' kd'
--   where
    


execSingleDecl :: Declaration_specifier -> Init_declarator -> Store -> Env -> ContD -> Cont
execSingleDecl specifier (OnlyDecl x) s env kd =
  execOnlyDecl specifier x s env
  where
    execOnlyDecl :: Declaration_specifier -> Declarator -> Store -> Env -> Cont
    execOnlyDecl specifier (Name var) s env = kd' env
      where
        kd' :: ContD
        kd' env s =
          let
            l = newLoc s
            env' = newVar var l env
            s' = updateStore l 0 s
          in kd' env' s'


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


-- runExternals :: [External_declaration] -> Env -> Cont -> Cont -> Cont
-- runExternals _ _ _ k = k


-- constM :: (Monad m) => a -> m a
-- constM = return
