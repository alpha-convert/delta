{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use newtype instead of data" #-}
module Var(Var(..)) where

data Var = Var String deriving (Eq, Ord, Show)