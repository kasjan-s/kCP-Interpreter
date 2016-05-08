module ExeckCP where

import AbskCP

import Data.Map

data DataVal =
      Void
    | TInt Integer
    | TBool Bool
    | TRecord Record

type Loc = Int
type Store = Map Loc DataVal

type FName = Ident
type Func = ([Ident], Compound_stm)

type Record = Map Ident Loc

type VEnv = Map Ident Loc
type FEnv = Map FName Func

type Env = (VEnv, FEnv)

newLoc :: Store -> Loc
newLoc s = if Data.Map.null s then 0 else (+1) . fst $ findMax s

getLoc :: Ident -> Env -> Loc
getLoc v (venv, _) = venv ! v

getVal :: Loc -> Store -> DataVal
getVal l s = s ! l

getFunc :: FName -> Env -> Func
getFunc fname (_, fenv) = fenv ! fname

newVar :: Ident -> Loc -> Env -> Env
newVar var loc (venv, fenv) = (insert var loc venv, fenv)
