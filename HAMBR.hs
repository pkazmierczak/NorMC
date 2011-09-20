module HAMBR where

import Prelude hiding (map, filter)
import qualified Prelude (map, filter)
import Data.HashMap hiding ((\\)) 
import Data.Hashable
import Data.List (sort, (\\))
import Data.Set (Set, empty)
import qualified Data.Set as Set

type HAMBR a b = (Map a (Set b), Map b (Set a))

build :: (Hashable a, Ord a, Hashable b, Ord b) => [(a,b)] -> HAMBR a b
build list = (l,r) where
    l = fromList $ compact $ sort list
    r = fromList $ compact $ sort $ Prelude.map swap list

compact :: (Ord a, Ord b) => [(a,b)] -> [(a,Set b)]
compact [] = []
compact l@((x,y):r) = (x, Set.fromList ys):(compact ri)
    where
      ys = Prelude.map snd le
      (le, ri) = break ((x /=).fst) l

swap :: (a,b) -> (b,a)
swap (x,y) = (y,x)

forward1 :: (Hashable a, Ord a) => HAMBR a b -> a -> Set b
forward1 = flip (findWithDefault Set.empty) . fst

backward1 :: (Hashable b, Ord b) => HAMBR a b -> b -> Set a
backward1 = flip (findWithDefault Set.empty) . snd

setMapAcc :: (Ord a, Ord b) => (a -> Set b) -> Set a -> Set b
setMapAcc f as = Set.fold (Set.union . f) Set.empty as

forward :: (Hashable a, Ord a, Ord b) => (HAMBR a b) -> Set a -> Set b
forward rel set = setMapAcc (forward1 rel) set

backward :: (Hashable b, Ord b, Ord a) => (HAMBR a b) -> Set b -> Set a
backward rel set = setMapAcc (backward1 rel) set

restrict :: (Hashable a, Ord a, Hashable b, Ord b) => (HAMBR a b) -> (a -> b -> Bool) -> (HAMBR a b)
restrict (lm, rm) f = (lm', rm') where
    lm' = mapWithKey (\a bs -> Set.filter (f a) bs) lm
    rm' = mapWithKey (\b as -> Set.filter (flip f b) as) rm

minus :: (Hashable a, Ord a, Hashable b, Ord b) => (HAMBR a b) -> (HAMBR a b) -> (HAMBR a b)
minus (lm1,rm1) (lm2,rm2) = (lm1', rm1') where
    lm1' = mapWithKey (\a bs -> bs `Set.difference` (findWithDefault Set.empty a lm2)) lm1
    rm1' = mapWithKey (\b as -> as `Set.difference` (findWithDefault Set.empty b rm2)) rm1

union :: (Hashable a, Ord a, Hashable b, Ord b) => (HAMBR a b) -> (HAMBR a b) -> (HAMBR a b)
union (lm1, rm1) (lm2, rm2) = (lm, rm) where
    lm = mapWithKey (\a bs -> bs `Set.union` (findWithDefault Set.empty a lm2)) lm1
    rm = mapWithKey (\b as -> as `Set.union` (findWithDefault Set.empty b rm2)) rm1

testRel :: HAMBR Int Int
testRel = build [ (x,y) | x <- [1 .. 1000], y <- [x .. 1000], gcd x y == 1 ]

evoddRel :: HAMBR Int Int
evoddRel = build [ (x,y) | x <- [1 .. 1000], y <- [1 .. 1000], (even x && even y) || (odd x && odd y) ]
