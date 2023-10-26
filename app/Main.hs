{-# LANGUAGE BangPatterns #-}
module Main (main) where

import System.Environment

import Frontend.Parser (parseProgram, lexer)
import System.IO (openFile, IOMode (..), hGetContents)
import qualified Frontend.SurfaceSyntax as Surf
import qualified Frontend.ElabSyntax as Elab
import qualified Frontend.Typecheck as Tck (doCheck)
import qualified CoreSyntax as Core
import qualified Semantics as Sem

fread :: String -> IO String
fread s = do
    handle <- openFile s ReadMode
    hGetContents handle


main :: IO ()
main = do
    contents <- fread . head =<< getArgs
    let surfP = parseProgram (lexer contents)
    elabP <- Elab.doElab surfP
    coreP <- Tck.doCheck elabP
    Sem.doRun coreP
