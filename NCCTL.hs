{-
Copyright 2011, University of Bergen. All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are
permitted provided that the following conditions are met:

   1. Redistributions of source code must retain the above copyright notice, this list of
      conditions and the following disclaimer.

   2. Redistributions in binary form must reproduce the above copyright notice, this list
      of conditions and the following disclaimer in the documentation and/or other materials
      provided with the distribution.

THIS SOFTWARE IS PROVIDED BY University of Bergen ``AS IS'' AND ANY EXPRESS OR IMPLIED
WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND
FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL University of Bergen OR
CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF
ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

The views and conclusions contained in the software and documentation are those of the
authors and should not be interpreted as representing official policies, either expressed
or implied, of University of Bergen.
-}

{-# LANGUAGE NoMonomorphismRestriction #-}
module NCCTL where

import FODBR hiding (fix)
import Data.List (foldl', sort, nub)

-- assumes states :: [s] and, for each p, (valuation p) :: [s] is ordered and nubbed
-- BinRel assumes the same about tr and nsys

data (Ord s, Eq p) => Kripke p s = Kripke {
  agents :: [Int], 
  states :: [s], 
  tr :: FODBR s s,
  owner :: (s, s) -> Int, 
  valuation :: p -> [s]
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

forwards,backwards :: (Ord s, Eq p) => Kripke p s -> SBMT s s
forwards  = snd . tr
backwards = fst . tr

check :: (Ord s, Eq p) => (Kripke p s) -> (FODBR s s) -> (Formula p) -> [s]
check mod sys (Prop p)    = sort $ (valuation mod) p
check mod sys (Neg f)     = (states mod) `nubminus` (check mod sys f)
check mod sys (Disj f f') = (check mod sys f) `nubunion` (check mod sys f')
check mod sys (Conj f f') = (check mod sys f) `nubisect` (check mod sys f')
check mod sys (EX f)      =
    sort $ nub $ concat $ map (find1 $ forwards mod) (check mod sys f)
check mod sys (EF f)      = fix ff (check mod sys (EX f)) where 
    ff ss = ss `nubunion` (find $ forwards mod) ss
check mod sys (EG f)      = fix ff (check mod sys f) where
    ff ss = ss `nubisect` (find $ forwards mod) ss
check mod sys (EU f f')   = fix ff (check mod sys f') where
    ff ss = ss `nubunion` ((find $ forwards mod) ss `nubisect` (check mod sys f))
check mod sys (CD c f) = foldl' nubunion [] $ 
                         map (\mod -> (check mod sys f)) $
                             map (ir mod sys) $ coasGivenCP mod c
check mod sys (CS c f) = foldl' nubisect (states mod) $ 
                         map (\mod -> (check mod sys f)) $
                             map (ir mod sys) $ coasGivenCP mod c

implement :: (Ord s, Eq p) => (Kripke p s) -> (FODBR s s) -> (Kripke p s)
implement mod sys = mod { tr = (tr mod) `minus` sys }

nsrestrict :: (Ord s, Eq p) => (Kripke p s) -> (FODBR s s) -> [Int] -> (FODBR s s)
nsrestrict mod sys coa = restrict sys (\s s' -> ((owner mod (s,s')) `elem` coa))

ir :: (Ord s, Eq p) => (Kripke p s) -> (FODBR s s) -> [Int] -> (Kripke p s)
ir mod sys coa = implement mod (nsrestrict mod sys coa)

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

coasGivenCP :: (Ord s, Eq p) => (Kripke p s) -> Coalition -> [[Int]]
coasGivenCP mod cp = filter (checkCoaPred cp) (spowerlist $ agents mod)

spowerlist :: (Ord a) => [a] -> [[a]]
spowerlist list = sort $ map sort $ powerlist' list where
    powerlist' [] = [[]]
    powerlist' (x:l) = (powerlist' l)++(map (x:) (powerlist' l))

subset :: (Ord a) => [a] -> [a] -> Bool
subset [] _ = True
subset (a:r) list = (a `elem` list) && (subset r list)
