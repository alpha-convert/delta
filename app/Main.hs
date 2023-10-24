module Main (main) where

import System.Environment

import Frontend.Parser (parseProgram, lexer)
import System.IO (openFile, IOMode (..), hGetContents)
import Data.Foldable (sequenceA_)
import qualified Frontend.SurfaceSyntax as Surf
import qualified Frontend.ElabSyntax as Elab
import qualified Frontend.Typecheck as Tck (doCheck)
import qualified CoreSyntax as Core

fread :: String -> IO String
fread s = do
    handle <- openFile s ReadMode
    hGetContents handle

elab :: Surf.FunDef Surf.Term -> IO (Surf.FunDef Elab.Term)
elab = mapM Elab.doElab

tck :: Surf.FunDef Elab.Term -> IO (Surf.FunDef Core.Term)
tck (Surf.FD f g s e) = do
    e' <- Tck.doCheck g s e
    print "Typechecked: \n"
    print e'
    return (Surf.FD f g s e')


main :: IO ()
main = do
    contents <- fread . head =<< getArgs
    let surfP = parseProgram (lexer contents)
    elabP <- mapM elab surfP
    tckP <- mapM tck elabP
    return ()