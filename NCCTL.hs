module NCCTL where

import HAMBR
import Data.Hashable
import FODBR (nubunion, nubisect, nubminus)
import Data.List (foldl', sort, nub, union, intersect, (\\))
import Data.Set (Set)
import qualified Data.Set as Set

data (Hashable s, Ord s, Eq p) => Kripke p s = Kripke {
  agents :: [Int], 
  states :: Set s, 
  tr :: HAMBR s s,
  owner :: (s, s) -> Int, 
  valuation :: p -> Set s
  } 

data (Eq p) => Formula p = Prop p             | Neg  (Formula p)
             | Disj (Formula p) (Formula p)   | Conj (Formula p) (Formula p)
             | EX   (Formula p)               | EF   (Formula p)
             | EG   (Formula p)               | EU   (Formula p) (Formula p)
             | CD   Coalition   (Formula p)   | CS   Coalition   (Formula p)
               deriving (Show)
               
data Coalition = Subseteq [Int]               | Supseteq [Int]
               | Eq [Int]                     | GEQ Int
               | CNeg Coalition               | CDisj Coalition Coalition
                 deriving (Show)

ag,af :: (Eq p) => (Formula p) -> (Formula p)
ag f = Neg (EF (Neg f))
af f = Neg (EG (Neg f))

forwards,backwards :: (Hashable s, Ord s, Eq p) => Kripke p s -> (Set s -> Set s)
forwards  mod = forward  (tr mod)
backwards mod = backward (tr mod)

check :: (Hashable s, Ord s, Eq p) => (Kripke p s) -> (HAMBR s s) -> (Formula p) -> Set s
check mod sys (Prop p)    = (valuation mod) p
check mod sys (Neg f)     = (states mod) `Set.difference` (check mod sys f)
check mod sys (Disj f f') = (check mod sys f) `Set.union` (check mod sys f')
check mod sys (Conj f f') = (check mod sys f) `Set.intersection` (check mod sys f')
check mod sys (EX f)      =
    (backwards mod) (check mod sys f)
check mod sys (EF f)      = fix ff (check mod sys (EX f)) where 
    ff ss = ss `Set.union` (backwards mod) ss
check mod sys (EG f)      = fix ff (check mod sys f) where
    ff ss = ss `Set.intersection` (backwards mod) ss
check mod sys (EU f f')   = fix ff (check mod sys f') where
    ff ss = ss `Set.union` ((backwards mod) ss `Set.intersection` (check mod sys f))
check mod sys (CD c f) = Set.unions $ 
                         map (\mod -> (check mod sys f)) $
                             map (ir mod sys) $ coasGivenCP mod c
check mod sys (CS c f) = foldl' Set.intersection (states mod) $ 
                         map (\mod -> (check mod sys f)) $
                             map (ir mod sys) $ coasGivenCP mod c

nsimplement :: (Hashable s, Ord s, Eq p) => (Kripke p s) -> (HAMBR s s) -> (Kripke p s)
nsimplement mod sys = mod { tr = (tr mod) `minus` sys }

nsrestrict :: (Hashable s, Ord s, Eq p) => (Kripke p s) -> (HAMBR s s) -> [Int] -> (HAMBR s s)
nsrestrict mod sys coa = restrict sys (\s s' -> ((owner mod (s,s')) `elem` coa))

ir :: (Hashable s, Ord s, Eq p) => (Kripke p s) -> (HAMBR s s) -> [Int] -> (Kripke p s)
ir mod sys coa = nsimplement mod (nsrestrict mod sys coa)

fix :: (Eq a) => (a -> a) -> a -> a
fix f x = if (fx == x) then x else fix f fx where
    fx = f x

checkCoaPred :: Coalition -> [Int] -> Bool
checkCoaPred (Subseteq set) coa = coa `subset` set
checkCoaPred (Supseteq set) coa = set `subset` coa
checkCoaPred (Eq set)       coa = set == coa
checkCoaPred (GEQ n)        coa = n <= length coa
checkCoaPred (CNeg c)       coa = not (checkCoaPred c coa)
checkCoaPred (CDisj c c')   coa = (checkCoaPred c coa) || (checkCoaPred c' coa)

coasGivenCP :: (Hashable s, Ord s, Eq p) => (Kripke p s) -> Coalition -> [[Int]]
coasGivenCP mod cp = filter (checkCoaPred cp) (spowerlist $ agents mod)

spowerlist :: (Ord a) => [a] -> [[a]]
spowerlist list = sort $ map sort $ powerlist' list where
    powerlist' [] = [[]]
    powerlist' (x:l) = (powerlist' l)++(map (x:) (powerlist' l))

subset :: (Ord a) => [a] -> [a] -> Bool
subset [] _ = True
subset (a:r) list = (a `elem` list) && (subset r list)

