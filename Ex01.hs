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

module Ex01 where

import NCCTL hiding (owner)
import FODBR (FODBR, build, find1, nubisect)
import Data.List (sort, (\\))

exampleModel :: Kripke Prop State
exampleModel = Kripke [0,1] statespace transition owner val

type Prop  = (Int,Char)
type State = (Int,Int,Int)

statespace :: [State]
statespace = [ (i, p0, p1) | i <- [0,1], p0 <- [0..9], p1 <- [0..9], p0 /= p1 ]

initState :: State
initState = (0,0,9)

p0 :: State -> Int
p0 (_,p0,_) = p0

val :: Prop -> [State]
val (0,'n') = filter (even . p0) statespace 
val (0,'s') = filter (odd . p0) statespace 
val (0,'w') = filter ((`elem` [0,1]) . p0) statespace 
val (0,'e') = filter ((`elem` [8,9]) . p0) statespace 
val (0,'t') = filter (\(i,_,_) -> i == 0) statespace 

val (1,'n') = filter (\(_,_,p1) -> p1 `mod` 2 == 0) statespace
val (1,'s') = filter (\(_,_,p1) -> p1 `mod` 2 /= 0) statespace
val (1,'w') = filter (\(_,_,p1) -> p1 == 0 || p1 == 1) statespace
val (1,'e') = filter (\(_,_,p1) -> p1 == 8 || p1 == 9) statespace
val (1,'t') = filter (\(i, _,_) -> i == 1) statespace 

transition = build [((i,p0,p1), ((1-i),p0',p1')) | 
                    (i,p0,p1) <- statespace, 
                    p0'       <- possibleSteps (i == 0) p0,
                    p1'       <- possibleSteps (i == 1) p1, 
                    ((1-i),p0',p1') `elem` statespace
                   ]

possibleSteps :: Bool -> Int -> [Int]
possibleSteps False p = [p]
possibleSteps True p = [p-2, p, p+2]++(if even p then [p+1] else [p-1])

illegal :: FODBR State State
illegal = build [ ((i,p0,p1),(1-i,p0',p1')) | 
                  (i,p0,p1)   <- statespace, 
                  (_,p0',p1') <- (find1 (fst transition) (i,p0,p1)), 
                  p1' == p0' + 2 || if i == 0 then (p0' < 8 && p0 >= p0') 
                                              else (p1' > 1 &&  p1 <= p1')
                ]

owner :: (State,State) -> Int
owner ((i,_,_),_) = i

initF :: Formula Prop 
initF = Conj (Conj (Prop (0,'t')) (Conj (Prop (0,'n')) (Prop (0,'w')))) 
        (Conj (Prop (1,'s')) (Prop (1,'e')))

goalF :: Formula Prop
goalF = Conj (Prop (0,'e')) (Prop (1,'w'))
