-- AUTHOR: Emeka Nkurumeh, 2023
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE DeriveFoldable #-}

module Util.PartialOrder
    ( Partial
    , checkDisjoint
    , concat
    , delete
    , empty
    , insert
    , lessThan
    , map
    , set
    , singleton
    , subOrder
    , subst
    , substSing
    , substSingAll
    , union
    ) where

import Control.Monad
import Data.Functor
import qualified Data.Set as Set
import GHC.Exts            (IsList)
import GHC.Stack
import Prelude             hiding (concat, map)
import Control.Monad.Except
import Data.Set (Set)

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

map :: (Ord b) => (a -> b) -> Partial a -> Partial b
map f (Partial p) = Partial (Set.map g p)
  where g (x, y) = (f x, f y)

transClosure :: (Ord b) => Set (b, b) -> Set (b, b)
transClosure p =
  let p' = transClosure1 p in
    if length p' > length p then
      transClosure p'
    else p'
  where
    transClosure1 p = p <> foldMap trans (Set.cartesianProduct p p)
    trans ((a, b), (c, d))
      | b == c = Set.singleton (a, d)
      | otherwise = Set.empty

insert :: (Ord a) => Partial a -> a -> a -> Partial a
insert (Partial p) a b = Partial $ transClosure (Set.insert (a, b) p)

lessThan :: (Ord a) => Partial a -> a -> a -> Bool
lessThan (Partial p) a b = Set.member (a, b) p

checkAntiSymm :: (Ord a, Monad m) => Partial a -> ExceptT (a, a) m ()
checkAntiSymm (Partial p) = maybe (return ()) throwError $ foldl f Nothing p
  where
    f x@(Just _) _ = x
    f Nothing (a, b)
      | a == b || Set.notMember (b, a) p = Nothing
      | otherwise                        = Just (a, b)

checkDisjoint :: (Ord a, HasCallStack, Monad m) => Partial a -> Partial a -> ExceptT a m ()
checkDisjoint (Partial p1) (Partial p2) =
  mapM_ (throwError . checkRefl) $ Set.lookupMin (Set.intersection p1 p2)
  where
    -- since we enforce reflexivity,
    -- the minimum element must be of the form (a, a)
    checkRefl (a, b)
      | a == b    = a
      | otherwise = error "reflexivity of partial order violated"

union :: (Ord a, Monad m) => Partial a -> Partial a -> ExceptT (a, a) m (Partial a)
union (Partial p1) (Partial p2) =
  let p3 = Partial (transClosure (p1 <> p2)) in
    checkAntiSymm p3 $> p3

concat :: (Ord a, Monad m) => Partial a -> Partial a -> ExceptT (a, a) m (Partial a)
concat p1 p2 = do
  p12 <- p1 `union` p2
  union p12 . Partial $ Set.cartesianProduct (set p1) (set p2)

subst :: (Eq a, Ord b, Monad m) => (a -> Partial b) -> Partial a -> ExceptT (b,b) m (Partial b)
subst f (Partial p) = foldM g (Partial (Set.fromList [])) p
  where
    g acc (x, y)
      | x == y = acc `union` f x
      | otherwise = concat (f x) (f y) >>= union acc

-- p[p'/x] = substSing p p' x
substSing :: (Ord a, Monad m) => Partial a -> Partial a -> a -> ExceptT (a,a) m (Partial a)
substSing p p' x = subst (\u -> if u == x then p' else singleton x) p

substSingAll :: (Ord a, Monad m) => Partial a -> [(Partial a, a)] -> ExceptT (a,a) m (Partial a)
substSingAll = foldM (\p (p',x) -> substSing p p' x)

subOrder :: (Ord a) => Partial a -> Partial a -> Maybe (Partial a)
subOrder (Partial sub) (Partial super) =
  let d = Set.difference sub super in
    if null d then Nothing else Just (Partial d)
