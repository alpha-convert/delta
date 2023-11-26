-- AUTHOR: Emeka Nkurumeh, Joe Cutler 2023
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE DeriveFoldable #-}

module Util.PartialOrder
    ( Partial
    , checkDisjoint
    , checkNotIn
    , concat
    , delete
    , empty
    , insert
    , lessThan
    , comparable
    , map
    , set
    , list
    , singleton
    -- , subOrder
    , subst
    , substSing
    , substSingAll
    , union
    , consistentWith
    , OrderErr(..)
    ) where

import Control.Monad
import Data.Functor
import qualified Data.Set as Set
import GHC.Exts            (IsList)
import GHC.Stack
import Prelude             hiding (concat, map)
import Control.Monad.Except
import Data.Set (Set)
import Types (CtxStruct (..))
import Control.Monad.Loops
import Data.Foldable (toList)

data OrderErr a =
    OutOfOrder a a
  | SomeOrder a a
  | AntiSym a a
  deriving (Eq,Ord,Show)


newtype Partial a
  = Partial { unPartial :: Set (a, a) }
  deriving (Eq, Foldable, IsList, Monoid, Ord, Semigroup, Show)

empty :: (Ord a) => Partial a
empty = fromList []

fromList :: (Ord a) => [(a, a)] -> Partial a
fromList = Partial . transClosure . Set.fromList

singleton :: a -> Partial a
singleton a = Partial $ Set.singleton (a, a)

delete :: (Ord a) => Partial a -> a -> Partial a
delete (Partial p) x = Partial $ Set.foldl' f Set.empty p
  where
    f acc x'@(a, b)
      | x == a || x == b = acc
      | otherwise        = Set.insert x' acc

set :: (Ord a) => Partial a -> Set a
set (Partial p) = foldMap (\(x,y)-> Set.fromList [x,y]) p

list :: (Ord a) => Partial a -> [a]
list p = Set.toList (set p)

map :: (Ord b) => (a -> b) -> Partial a -> Partial b
map f (Partial p) = Partial (Set.map g p)
  where g (x, y) = (f x, f y)

transClosure :: (Ord a) => Set (a, a) -> Set (a, a)
transClosure p =
  let p' = transClosure1 p in
    if length p' > length p then
      transClosure p'
    else p'
  where
    transClosure1 p' = p' <> foldMap trans (Set.cartesianProduct p' p')
    trans ((a, b), (c, d))
      | b == c = Set.singleton (a, d)
      | otherwise = Set.empty

insert :: (Ord a) => Partial a -> a -> a -> Partial a
insert (Partial p) a b = Partial $ transClosure (Set.insert (a, b) p)

lessThan :: (Ord a) => Partial a -> a -> a -> Bool
lessThan (Partial p) a b = Set.member (a, b) p

comparable :: (Ord a) => Partial a -> a -> a -> Bool
comparable p x y = lessThan p x y || lessThan p y x

checkAntiSymm :: (Ord a, Monad m) => Partial a -> ExceptT (OrderErr a) m ()
checkAntiSymm (Partial p) = foldM f () p
  where
    f _ (a,b) = when (a /= b && Set.member (b,a) p) $ throwError (AntiSym a b)

checkDisjoint :: (Ord a, Monad m) => Partial a -> Partial a -> ExceptT a m ()
checkDisjoint (Partial p1) (Partial p2) =
  case Set.lookupMin (Set.intersection p1 p2) of
    Nothing -> return ()
    Just (a,b) -> when (a /= b) $ error "reflexivity of partial order violated"

checkNotIn :: (Ord a, Monad m) => a -> Partial a -> ExceptT a m ()
checkNotIn x (Partial p) = when (Set.member (x,x) p) $ throwError x

union :: (Ord a, Monad m) => Partial a -> Partial a -> ExceptT (OrderErr a) m (Partial a)
union (Partial p1) (Partial p2) = do
  let p3 = Partial (transClosure (p1 <> p2))
  checkAntiSymm p3
  return p3

concat :: (Ord a, Monad m) => Partial a -> Partial a -> ExceptT (OrderErr a) m (Partial a)
concat p1 p2 = do
  p12 <- p1 `union` p2
  p12 `union` Partial (Set.cartesianProduct (set p1) (set p2))

-- This would be great if it could report `OrderErr a`s. The error messages don't make much sense otherwise.
subst :: (Eq a, Ord b, Monad m) => (a -> Partial b) -> Partial a -> ExceptT (OrderErr b) m (Partial b)
subst f (Partial p) = foldM g (Partial (Set.fromList [])) p
  where
    g acc (x, y)
      | x == y = acc `union` f x
      | otherwise = concat (f x) (f y) >>= union acc

-- p[p'/x] = substSing p p' x
substSing :: (Ord a, Monad m) => Partial a -> Partial a -> a -> ExceptT (OrderErr a) m (Partial a)
substSing p p' x = subst (\u -> if u == x then p' else singleton u) p

substSingAll :: (Ord a, Monad m) => Partial a -> [(Partial a, a)] -> ExceptT (OrderErr a) m (Partial a)
substSingAll = foldM (\p (p',x) -> substSing p p' x)

subOrder :: (Ord a) => Partial a -> Partial a -> Maybe (Partial a)
subOrder (Partial sub) (Partial super) =
  let d = Set.difference sub super in
    if null d then Nothing else Just (Partial d)

pm :: (Monad m, Foldable t1, Foldable t2) => t1 t3 -> t2 a -> (t3 -> a -> m b) -> m ()
pm g g' f = mapM_ (\x -> mapM_ (f x) g') g

consistentWith :: (Ord a, Monad m) => Partial a -> CtxStruct a -> ExceptT (OrderErr a) m ()
consistentWith _ EmpCtx = return ()
consistentWith _ (SngCtx _) = return ()
consistentWith p (SemicCtx g g') = do
  consistentWith p g
  consistentWith p g'
  pm g g' $ \x y -> when (lessThan p y x) (throwError (OutOfOrder x y))
consistentWith p (CommaCtx g g') = do
  consistentWith p g
  consistentWith p g'
  pm g g' $ \x y -> when (comparable p x y) (throwError (SomeOrder x y))


-- = if not (lessThan p y x) then consistentWith p (y:xs) else throwError (x,y)