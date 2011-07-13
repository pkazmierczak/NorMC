{-
Copyright 2011, Truls Pedersen. All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are
permitted provided that the following conditions are met:

   1. Redistributions of source code must retain the above copyright notice, this list of
      conditions and the following disclaimer.

   2. Redistributions in binary form must reproduce the above copyright notice, this list
      of conditions and the following disclaimer in the documentation and/or other materials
      provided with the distribution.

THIS SOFTWARE IS PROVIDED BY TRULS PEDERSEN ``AS IS'' AND ANY EXPRESS OR IMPLIED
WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND
FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL TRULS PEDERSEN OR
CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF
ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

The views and conclusions contained in the software and documentation are those of the
authors and should not be interpreted as representing official policies, either expressed
or implied, of Truls Pedersen.
-}

module FODBR where

import Data.List (foldl',sort,(\\))
import Data.Tuple (swap)

-- Finite (fixed) Ordered Domain Binary Relation
type FODBR a b = (SBMT a b, SBMT b a)

{-
  Simple construction: 
  (SOUT assumes the argument list is sorted and has no duplicate elements)
  assumes the argument list has no duplicate elements.
-}
build :: (Ord a, Ord b) => [(a,b)] -> FODBR a b
build list =  (l, r) where
    l = construct $ compact $ sort list
    r = construct $ compact $ sort $ map swap list

buildC :: (Ord a, Ord b) => [(a,[b])] -> FODBR a b
buildC clist = (l, r) where
    l = construct clist
    r = construct $ compact $ sort $ map swap $ tolist l

-- Construction
union :: (Ord a, Ord b) => (FODBR a b) -> (FODBR a b) -> (FODBR a b)
union (lt,rt) (lt',rt') = (lt'',rt'') where
    lt'' = trunion lt lt'
    rt'' = trunion rt rt'

compose :: (Ord a, Ord b, Ord c) => (FODBR a b) -> (FODBR b c) -> (FODBR a c)
compose (lt,rt) (lt',rt') = (lt'',rt'') where
    lt'' = trcomp lt lt'
    rt'' = trcomp rt' rt

invert :: (Ord a, Ord b) => (FODBR a b) -> (FODBR b a)
invert = swap

minus :: (Ord a, Ord b) => (FODBR a b) -> (FODBR a b) -> (FODBR a b)
minus (lt,rt) (lt', rt') = (lt'',rt'') where
    lt'' = trminus lt lt'
    rt'' = trminus rt rt'

restrict :: (Ord a, Ord b) => (FODBR a b) -> (a -> b -> Bool) -> (FODBR a b)
restrict (l, r) f = (l',r') where
    l' = trestrict l f
    r' = trestrict r (flip f)

-- Closure
lid :: (Ord a, Ord b) => (FODBR a b) -> (FODBR a a)
lid (r,_) = build $ map (\x -> (x,x)) (keys r)

rid :: (Ord a, Ord b) => (FODBR a b) -> (FODBR b b)
rid (_,r) = build $ map (\x -> (x,x)) (keys r)

refl :: (Ord a) => (FODBR a a) -> (FODBR a a)
refl r = (lid r) `union` r `union` (rid r)

irrefl :: (Ord a) => (FODBR a a) -> (FODBR a a)
irrefl r = (r `minus`(lid r)) `minus`(rid r)


trans :: (Ord a) => (FODBR a a) -> (FODBR a a)
trans (l,r) = buildC $ map (\x -> (x, allsucc l x)) (keys l)

allsucc :: (Ord a) => (SBMT a a) -> a -> [a]
allsucc tree x = fix (\xs -> xs `nubunion` (find tree xs)) (find1 tree x)

fix :: (Eq a) => (a -> a) -> a -> a
fix f x = if fx == x then x else fix f fx where
    fx = f x

-- Strict (i.e. non-lazy) Binary Multivalued Tree
data (Ord a, Ord b) => SBMT a b = Empty
                                | Branch !(a,[b]) !(SBMT a b) !(SBMT a b)
                                  deriving (Eq)

-- We construct a SBMT from a sorted, nubbed and compacted list representation
construct :: (Ord a, Ord b) => [(a,[b])] -> SBMT a b
construct []  = Empty
construct list = construct' (length list) list where
    construct' n list | n == 0 = Empty
                      | n >  0 = Branch p (construct' ll l) (construct' lr r)
        where
          ll = n `div` 2
          lr = ((n+1) `div` 2) - 1
          (l,(p:r)) =  splitAt ll list

-- We compact the list. We take advantage of the fact that the argument is sorted.
compact :: (Ord a, Ord b) => [(a,b)] -> [(a,[b])]
compact [] = []
compact l@((x,y):r) = (x, ys):(compact ri)
    where
      ys = map snd le
      (le, ri) = break ((x /=).fst) l

-- tolist allows the construction of an inverse given a compact list. 
tolist :: (Ord a, Ord b) => (SBMT a b) -> [(a,b)]
tolist tree = concat $ map (\x -> (map (\y -> (x,y)) (find1 tree x))) (keys tree)

{-
  Lookup function
  This could very well have been \cc{(Ord a, Ord b) => (SBMT a b) -> a -> Maybe [b]}, but... 
  let's just say, for simplicity, that keys not in the tree relates to nothing.
-}
find1 :: (Ord a, Ord b) => (SBMT a b) -> a -> [b]
find1 Empty _                            = []
find1 (Branch (k,vs) lst rst) x | x == k = vs
                                  | x <  k = find1 lst x
                                  | x  > k = find1 rst x

find :: (Ord a, Ord b) => (SBMT a b) -> [a] -> [b]
find tree xs = snub $ sort $ concat $ map (find1 tree) xs
    -- foldl' nubunion [] $ map (find1 tree) xs

-- A version of \cc{find} which returns only those elements pointed to by \textit{all} argument elements
fall :: (Ord a, Ord b) => (SBMT a b) -> [a] -> [b]
fall _ [] = []
fall tree (x:xs) = foldl' nubisect (find1 tree x) $ map (find1 tree) xs

-- Construction
trunion :: (Ord a, Ord b) => (SBMT a b) -> (SBMT a b) -> (SBMT a b)
trunion one another = construct base where
    base = map (\key -> (key, nubunion (find1 one key) (find1 another key))) $ keys one

trcomp :: (Ord a, Ord b, Ord c) => (SBMT a b) -> (SBMT b c) -> (SBMT a c)
trcomp one another = construct base where
    base = map (\key -> (key, find another (find1 one key))) (keys one)

trminus :: (Ord a, Ord b) => (SBMT a b) -> (SBMT a b) -> (SBMT a b)
trminus one another = construct base where
    base = map (\key -> (key, (find1 one key) `nubminus` (find1 another key))) (keys one)

trestrict :: (Ord a, Ord b) => (SBMT a b) -> (a -> b -> Bool) -> (SBMT a b)
trestrict Empty _ = Empty
trestrict (Branch (k, vs) l r) f = Branch (k, (filter (f k) vs)) (trestrict l f) (trestrict r f)

{-
  Auxiliary functions - primarily for ordered lists
-}

-- nubunion assumes it's two arguments both are sorted and nubbed
nubunion :: (Ord a) => [a] -> [a] -> [a]
nubunion xs ys = snub $ sort $ xs ++ ys  -- this is faster for some reason... ?
{-
nubunion [] [] = []
nubunion [] x  = x
nubunion x  [] = x
nubunion (x:r) (x':r') | x == x' = x:(nubunion r r')
                       | x <  x' = x:(nubunion r (x':r'))
                       | x  > x' = x':(nubunion (x:r) r')
-}

nubisect :: (Ord a) => [a] -> [a] -> [a]
nubisect [] _ = []
nubisect _ [] = []
nubisect (x:r) (x':r') | x == x' = x:(nubisect r r')
                       | x <  x' = nubisect r (x':r')
                       | x  > x' = nubisect (x:r) r'

nubminus :: (Ord a) => [a] -> [a] -> [a]
nubminus [] _ = []
nubminus x [] = x
nubminus (x:r) (x':r') | x == x' = nubminus r r'
                       | x <  x' = x:(nubminus r (x':r'))
                       | x  > x' = (nubminus (x:r) r')

snub :: (Ord a) => [a] -> [a]
snub []  = []
snub (x:r) = x:(snub r') where
    r' = dropWhile (x ==) r

-- Diagnostics:
suchThat :: (Ord a, Ord b) => (SBMT a b) -> (a -> [b] -> Bool) -> [(a,[b])]
suchThat Empty _ = []
suchThat (Branch (k,vs) l r) f = (suchThat l f) ++ (if (f k vs) then [(k,vs)] else []) ++ (suchThat r f)

getStat :: (Ord a, Ord b) => (SBMT a b) -> (a -> [b] -> c) -> (c -> c -> c -> c) -> c -> c
getStat Empty _ _ h = h
getStat (Branch (k,vs) lst rst) f combine h = combine (f k vs) (getStat lst f combine h) (getStat rst f combine h)

keys :: (Ord a, Ord b) => (SBMT a b) -> [a]
keys Empty = []
keys (Branch (k,_) lst rst) = (keys lst) ++ [k] ++ (keys rst)

-- to dot
toDotSame :: (Show a, Ord a) => (FODBR a a) -> String
toDotSame graph = dotIntro ++ (dotNodes2 aNum) ++ "\n\n" ++ (dotEdge2 aNum aNum (find1 $ fst graph)) ++ dotExtro where
    aNum = zip [1..] $ (keys $ fst graph) `nubunion` (keys $ snd graph)

dotNodes2 :: (Show a, Ord a) => [(Int,a)] -> String
dotNodes2 [] =[]
dotNodes2 ((n,a):r) = ("\tnode [shape = circle, label =\""++(show a)++"\"]; N" ++ (show n) ++ ";\n") ++
                      (dotNodes2 r)

dotEdge2 :: (Show a, Ord a) => [(Int,a)] -> [(Int,a)] -> (a -> [a]) -> String
dotEdge2  [] _ _            = []
dotEdge2 ((_,a):r) aNum fnd = (concat $ map (printEdge (din2 aNum a)) (map (din2 aNum) (fnd a)) )++
                              (dotEdge2 r aNum fnd)

din2 :: (Show a, Ord a) => [(Int,a)] -> a -> String
din2 [] _ = "ERROR"
din2 ((n,a):r) x | a == x = 'N':(show n)
                 | otherwise = din2 r x

toDot :: (Show a, Ord a, Show b, Ord b) => (FODBR a b) -> String
toDot graph = dotIntro ++ (dotNodes abNum baNum graph) ++ "\n\n" ++ (dotEdge abNum baNum graph) ++ dotExtro where
    abNum = zip [1..] (keys $ fst graph)
    baNum = zip [1..] (keys $ snd graph)

dotNodes :: (Show a, Ord a, Show b, Ord b) => [(Int,a)] -> [(Int,b)] -> (FODBR a b) -> String
dotNodes abNum baNum graph = (dotNodes' 'N' abNum (keys $ fst graph)) ++
                             (dotNodes' 'M' baNum (keys $ snd graph))
    where
          dotNodes' prefix _ []        = []
          dotNodes' prefix abNum (a:r) = printNode a (din prefix abNum a) ++
                                         dotNodes' prefix abNum r

printNode :: (Show a) => a -> String -> String
printNode node index = "\tnode [shape = circle, label = \""++(show node)++"\"]; " ++ index ++ ";\n"

dotEdge :: (Show a, Ord a, Show b, Ord b) => [(Int,a)] -> [(Int,b)] -> (FODBR a b) -> String
dotEdge abNum baNum graph = (dotEdge' 'N' abNum 'M' baNum (keys $ fst graph) (find1 $ fst graph)) -- ++
--                            (dotEdge' 'M' baNum 'N' abNum (keys $ snd graph) (find1 $ snd graph))
    where
      dotEdge' _  _  _  _  []    _     = []
      dotEdge' fp ft tp tf (f:r) succs = (concat $ map (printEdge (din fp ft f)) $ map (din tp tf) (succs f)) ++
                                         (dotEdge' fp ft tp tf r succs)

printEdge :: String -> String -> String
printEdge find tind = "\t"++find++" -> "++tind++";\n"

dotIntro :: String
dotIntro = "digraph G {\n"

dotExtro :: String
dotExtro = "}"

din :: (Eq a) => Char -> [(Int,a)] -> a -> String
din _ []  _ = "ERROR"
din prefix ((n, x):r) x' | x == x' = (prefix:(show n))
                  | x /= x' = din prefix r x'
