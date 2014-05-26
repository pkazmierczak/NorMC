module NCCTL where

import FODBR hiding (fix)
import Data.List (foldl', sort, nub)

data Kripke p s = Kripke {
  agents :: [Int],
  states :: [s],
  tr :: FODBR s s,
  owner :: (s, s) -> Int,
  valuation :: p -> [s]
  }

data  Formula p =
  Prop p                           | Neg  (Formula p)
  | Disj (Formula p) (Formula p)   | Conj (Formula p) (Formula p)
  | EX   (Formula p)               | EF   (Formula p)
  | EG   (Formula p)               | EU   (Formula p) (Formula p)
  | CD   Coalition   (Formula p)   | CS   Coalition   (Formula p)
    deriving (Show)

data Coalition =
   Subseteq [Int]               | Supseteq [Int]
   | Eq [Int]                   | GEQ Int
   | CNeg Coalition             | CDisj Coalition Coalition
     deriving (Show)

fix :: (Eq a) => (a -> a) -> a -> a
fix f x 
  | f x == x  = x
  | otherwise = fix f (f x)

ag,af :: (Eq p) => Formula p -> Formula p
ag f = Neg (EF (Neg f))
af f = Neg (EG (Neg f))

forwards,backwards :: (Ord s, Eq p) => Kripke p s -> BMT s s
forwards = fst . tr
backwards = snd . tr

check :: (Ord s, Eq p) => Kripke p s -> FODBR s s -> Formula p -> [s]
check mod sys (Prop p)    = sort $ valuation mod p
check mod sys (Neg f)     = states mod `nubminus` check mod sys f
check mod sys (Disj f f') = check mod sys f `nubunion` check mod sys f'
check mod sys (Conj f f') = check mod sys f `nubisect` check mod sys f'

check mod sys (EX f)      =
    find (backwards mod) (check mod sys f)
check mod sys (EF f)      = fix ff (check mod sys (EX f)) where
    ff ss = ss `nubunion` (find $ backwards mod) ss
check mod sys (EG f)      = fix ff (check mod sys f) where
    ff ss = ss `nubisect` (find $ backwards mod) ss
check mod sys (EU f f')   = fix ff (check mod sys f') where
    ff ss = ss `nubunion` ((find $ backwards mod) ss `nubisect` check mod sys f)

check mod sys (CD c f) =
   foldl' nubunion []
   . map ((\mod -> check mod sys f) . ir mod sys)
   $ coasGivenCP mod c
check mod sys (CS c f) =
  foldl' nubisect (states mod)
  . map ((\mod -> check mod sys f) . ir mod sys)
  $ coasGivenCP mod c

nsimplement :: (Ord s, Eq p) => Kripke p s -> FODBR s s -> Kripke p s
nsimplement mod sys = mod { tr = tr mod `minus` sys }

nsrestrict :: (Ord s, Eq p) => Kripke p s -> FODBR s s -> [Int] -> FODBR s s
nsrestrict mod sys coa = restrict sys (\s s' -> owner mod (s,s') `elem` coa)

ir :: (Ord s, Eq p) => Kripke p s -> FODBR s s -> [Int] -> Kripke p s
ir mod sys coa = nsimplement mod (nsrestrict mod sys coa)

checkCoaPred :: Coalition -> [Int] -> Bool
checkCoaPred (Subseteq set) coa = coa `subset` set
checkCoaPred (Supseteq set) coa = set `subset` coa
checkCoaPred (Eq set)       coa = set == coa
checkCoaPred (GEQ n)        coa = n <= length coa
checkCoaPred (CNeg c)       coa = not (checkCoaPred c coa)
checkCoaPred (CDisj c c')   coa = checkCoaPred c coa || checkCoaPred c' coa

coasGivenCP :: (Ord s, Eq p) => Kripke p s -> Coalition -> [[Int]]
coasGivenCP mod cp = filter (checkCoaPred cp) (spowerlist $ agents mod)

spowerlist :: (Ord a) => [a] -> [[a]]
spowerlist list = sort . map sort . powerlist' $ list
   where
    powerlist' [] = [[]]
    powerlist' (x:l) = powerlist' l ++ map (x:) (powerlist' l)

subset :: (Ord a) => [a] -> [a] -> Bool
subset [] _ = True
subset (a:r) list = (a `elem` list) && subset r list

