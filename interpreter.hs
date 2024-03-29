-- automatically generated by BNF Converter
{-# LANGUAGE FlexibleContexts #-}
module Main where


import System.IO ( stdin, hGetContents )
import System.Environment ( getArgs, getProgName )

import LexkCP
import ParkCP
import SkelkCP
import PrintkCP
import AbskCP
import Semantics



import ErrM

type ParseFun a = [Token] -> Err a

myLLexer = myLexer

type Verbosity = Int

putStrV :: Verbosity -> String -> IO ()
putStrV v s = if v > 1 then putStrLn s else return ()

runFile :: (Print Program, Show Program) => Verbosity -> ParseFun Program -> FilePath -> IO ()
runFile v p f = putStrLn f >> readFile f >>= run v p

run :: (Print Program, Show Program) => Verbosity -> ParseFun Program -> String -> IO ()
run v p s = let ts = myLLexer s in case p ts of
           Bad st   -> do putStrLn "\nParse              Failed...\n"
                          putStrV v "Tokens:"
                          putStrV v $ show ts
                          putStrLn st
           Ok  tree -> do
                          showTree v tree
			  (store, (venv, fenv)) <- runProgram tree
			  putStrV v $ show store
			  putStrV v $ show venv
                          putStrV v $ show fenv

showTree :: (Show Program, Print Program) => Int -> Program -> IO ()
showTree v tree
 = if v > 0
   then do
      putStrV 2 $ "\n[Abstract Syntax]\n\n" ++ show tree
      putStrV 2 $ "\n[Linearized tree]\n\n" ++ printTree tree
   else return ()

main :: IO ()
main = do args <- getArgs
          case args of
            [] -> hGetContents stdin >>= run 2 pProgram
            "-t":fs -> mapM_ (runFile 1 pProgram) fs
            "-v":fs -> mapM_ (runFile 2 pProgram) fs
            fs -> mapM_ (runFile 0 pProgram) fs
