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

module Ex02 where

import NCCTL hiding (owner)
import FODBR (FODBR, build, find1, nubisect, restrict, union)
import Data.List (sort,(\\))

type EXState = (Int, Int, Int, Int, Int, Int, Int)

statespace :: [EXState]
statespace = sort  
             [(p, s1, s2, c1, c2, c3, a) | 
                   p  <- [0..4], s1 <- [0..4], s2 <- [0..4], 
                   c1 <- [0..4], c2 <- [0..4], c3 <- [0..4], 
                   a  <- [1..4]
             ]

transition :: FODBR EXState EXState
transition = build [((p , s1 , s2 , c1 , c2 , c3 , a),
                     (p', s1', s2', c1', c2', c3', 1 + (a `mod` 4))) | 
                    (p,s1,s2,c1,c2,c3,a) <- statespace,
                    --                                  (i)         (ii)
                    p'  <- if (p  == a || p  == 0) then [0, a] else [p ], 
                    s1' <- if (s1 == a || s1 == 0) then [0, a] else [s1], 
                    s2' <- if (s2 == a || s2 == 0) then [0, a] else [s2], 
                    c1' <- if (c1 == a || c1 == 0) then [0, a] else [c1], 
                    c2' <- if (c2 == a || c2 == 0) then [0, a] else [c2], 
                    c3' <- if (c3 == a || c3 == 0) then [0, a] else [c3]
                   ] 

owner :: (EXState, EXState) -> Int
owner ((_,_,_,_,_,_,i), _) = i

data Resource = Pr | S1 | S2 | C1 | C2 | C3 deriving Eq

project :: Resource -> EXState -> Int
project Pr (pr,_,_,_,_,_,_) = pr
project S1 (_,s1,_,_,_,_,_) = s1
-- and so on...
project S2 (_,_,s2,_,_,_,_) = s2
project C1 (_,_,_,c1,_,_,_) = c1
project C2 (_,_,_,_,c2,_,_) = c2
project C3 (_,_,_,_,_,c3,_) = c3

type Proposition = (Resource, Int)

val :: Proposition -> [EXState]
val (res, ag) = filter ((ag == ) . (project res)) statespace

stHappy :: Int -> EXState -> Bool
stHappy 1 (pr, _,  _,  c1, c2, c3, _) = (pr == 1 && (c1 == 1 || c2 == 1 || c3 == 1))
stHappy 2 (pr, s1, s2, _,  _,  _,  _) = (pr == 2 && (s1 == 2 || s2 == 2))
stHappy 3 (_,  s1, s2, c1, c2, c3, _) = ((s1 == 3 || s2 == 3) && 
                                         (c1 == 3 || c2 == 3 || c3 == 3))
stHappy 4 (_,  s1, s2, _,  _,  _,  _) = (s1 == 4 || s2 == 4)

eta_1 :: FODBR EXState EXState
eta_1 = restrict transition
        (\s s' -> if (stHappy (owner (s,s')) s)
                    then (ownsSomething (owner (s,s')) s')
                    else True)

needprinter 1 = True
needprinter 2 = True
needprinter _ = False
needscanner 2 = True
needscanner 3 = True
needscanner 4 = True
needscanner _ = False
needcomputer 1 = True
needcomputer 3 = True
needcomputer _ = False

component1 :: FODBR EXState EXState
component1 = restrict transition
          (\(pr,s1,s2,c1,c2,c3,a) (pr', s1', s2', c1', c2', c3', a') -> 
           (a == s1' && a == s2') || (a == c1' && a == c2' ) || 
                                      (a == c1' && a == c3') || 
                                      (a == c2' && a == c3'))
component2 :: FODBR EXState EXState
component2 = restrict transition
          (\(pr,s1,s2,c1,c2,c3,a) (pr', s1', s2', c1', c2', c3', a') ->
           ((not $ needprinter a) && ( pr /= a && pr' == a))   || 
           ((not $ needscanner a) && ((s1 /= a && s1' == a)    || 
                                      (s2 /= a && s2' == a)))  ||
           (((not $ needcomputer a) && ( (c1 /= a && c1' == a) || 
                                         (c2 /= a && c2' == a) || 
                                         (c3 /= a && c3' == a) ))))
component3 :: FODBR EXState EXState
component3 = restrict transition
          (\(pr,s1,s2,c1,c2,c3,a) (pr', s1', s2', c1', c2', c3', a') ->
           (foldr (+) 0 $ 
                  zipWith (\x y -> if (x /= a) && (y == a) then 1 else 0) 
                              [pr , s1 , s2 , c1 , c2 , c3 ] 
                              [pr', s1', s2', c1', c2', c3']) > 1)
component4 :: FODBR EXState EXState
component4 = restrict transition
          (\(pr,s1,s2,c1,c2,c3,a) (pr', s1', s2', c1', c2', c3', a') ->
               if (
                    ((pr == 0                      ) && (needprinter  a) 
                                                         && pr /= a    ) || 
                    ((s1 == 0 || s2 == 0           ) && (needscanner  a) 
                                                         && s1 /= a && s2 /= a) || 
                    ((c1 == 0 || c2 == 0 || c3 == 0) && (needcomputer a) 
                                                         && c1 /= a && c2 /= a 
                                                                && c3 /= a)
                  )
               then
                   (pr == pr' && s1 == s1' && 
                    s2 == s2' && c1 == c1' && 
                    c2 == c2' && c3 == c3'
                   ) 
               else False
          )

eta_0 :: FODBR EXState EXState
eta_0 = component1 `union` component2 `union` component3 `union` component4

ownsSomething :: Int -> (EXState -> Bool)
ownsSomething n = (\(pr, s1, s2, c1, c2, c3, a) -> (pr == n || s1 == n || s2 == n || c1 == n || c2 == n || c3 == n))

exampleModel :: Kripke Proposition EXState
exampleModel = Kripke [1,2,3,4] statespace transition owner val 

exampleModel' :: Kripke Proposition EXState
exampleModel' = ir exampleModel eta_0 [1,2,3,4]

fHasPrinter, fHasScanner, fHasComputer :: Int -> (Formula Proposition)
fHasPrinter ag = (Prop (Pr, ag))
fHasScanner ag = (Disj (Prop (S1, ag)) (Prop (S2, ag)))
fHasComputer ag = (Disj (Prop (C1, ag)) (Disj (Prop (C2, ag)) (Prop (C3, ag))))

fHappy :: Int -> Formula Proposition
fHappy 1 = (Conj (fHasPrinter 1) (fHasComputer 1)) 
fHappy 2 = (Conj (fHasPrinter 2) (fHasScanner 2))
fHappy 3 = (Conj (fHasScanner 3) (fHasComputer 3))
fHappy 4 = (fHasScanner 4)

phi_1 :: Formula Proposition
phi_1 = ag (Conj (af (fHappy 1))
                      (Conj (af (fHappy 2))
                            (Conj (af (fHappy 3)) 
                                  (af (fHappy 4)))))