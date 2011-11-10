module Ex01 where

import NCCTL hiding (owner)
import FODBR (FODBR, build, find1, nubisect)
import Data.List (sort, (\\))

exampleModel :: Kripke Prop State
exampleModel = Kripke [0,1] statespace transition owner val

data Property = N | S | E | W | T deriving (Show,Eq)
                            
type Prop  = (Property, Int)
type State = (Int, Int, Int)

statespace :: [State]
statespace = [ (p0, p1, i) | p0 <- [0..9], p1 <- [0..9], p0 /= p1, i <- [0,1] ]

initState :: State
initState = (0, 9, 0)

project :: Int -> State -> Int
project 0 (p0, _, _) = p0
project 1 (_, p1, _) = p1

val :: Prop -> [State]
val (N, ag) = filter (even . (project ag)) statespace 
val (S, ag) = filter (odd . (project ag)) statespace 
val (W, ag) = filter ((`elem` [0,1]) . (project ag)) statespace 
val (E, ag) = filter ((`elem` [8,9]) . (project ag)) statespace 
val (T, ag) = filter (\(_,_,i) -> i == ag) statespace 

transition = build [((p0,p1,i), (p0',p1',1-i)) | 
                    (p0,p1,i) <- statespace, 
                    p0'       <- possibleSteps (i == 0) p0,
                    p1'       <- possibleSteps (i == 1) p1, 
                    (p0',p1',1-i) `elem` statespace
                   ]

possibleSteps :: Bool -> Int -> [Int]
possibleSteps False p = [p]
possibleSteps True p = [p-2, p, p+2]++(if even p then [p+1] else [p-1])

illegal :: FODBR State State
illegal = build [ ((p0,p1,i),(p0',p1',1-i)) | 
                  (p0,p1,i)   <- statespace, 
                  (p0',p1',_) <- (find1 (fst transition) (p0,p1,i)), 
                  p1' == p0' + 2 || if i == 0 then (p0' < 8 && p0 >= p0') 
                                              else (p1' > 1 &&  p1 <= p1')
                ]

owner :: (State,State) -> Int
owner ((_,_,i),_) = i

initF :: Formula Prop 
initF = Conj (Conj (Prop (T, 0)) (Conj (Prop (N, 0)) (Prop (W, 0)))) 
             (Conj (Prop (S, 1)) (Prop (E, 1)))

goalF :: Formula Prop
goalF = Conj (Prop (E, 0)) (Prop (W, 1))

