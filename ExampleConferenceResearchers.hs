module ExampleConferenceResearchers where

import NCCTL hiding (owner)
import FODBR (FODBR, build, find1, nubisect, restrict, union)
import Data.List (sort,(\\))

type State = (Int, Int, Int, Int, Int, Int, Int)

statespace :: [State]
statespace = sort  
             [(p, s1, s2, c1, c2, c3, a) | 
                   p  <- [0..4], s1 <- [0..4], s2 <- [0..4], 
                   c1 <- [0..4], c2 <- [0..4], c3 <- [0..4], 
                   a  <- [1..4]
             ]

-- initState :: State -- I'm not sure we actually need initState here at all
-- initState = (0, 0, 0, 0, 0, 0, 1) -- it's not used anywhere else in the file

transition :: FODBR State State
transition = build [((p , s1 , s2 , c1 , c2 , c3 , a),
                     (p', s1', s2', c1', c2', c3', 1 + (a `mod` 4))) | 
                    (p,s1,s2,c1,c2,c3,a) <- statespace,
                    p'  <- if p  == a || p  == 0 then [0, a] else [p ], 
                    s1' <- if s1 == a || s1 == 0 then [0, a] else [s1], 
                    s2' <- if s2 == a || s2 == 0 then [0, a] else [s2], 
                    c1' <- if c1 == a || c1 == 0 then [0, a] else [c1], 
                    c2' <- if c2 == a || c2 == 0 then [0, a] else [c2], 
                    c3' <- if c3 == a || c3 == 0 then [0, a] else [c3]
                   ] 

owner :: (State, State) -> Int
owner ((_,_,_,_,_,_,i), _) = i

data Resource = Pr | S1 | S2 | C1 | C2 | C3 deriving Eq

project :: Resource -> State -> Int
project Pr (pr,_,_,_,_,_,_) = pr
project S1 (_,s1,_,_,_,_,_) = s1
-- and so on...

project S2 (_,_,s2,_,_,_,_) = s2
project C1 (_,_,_,c1,_,_,_) = c1
project C2 (_,_,_,_,c2,_,_) = c2
project C3 (_,_,_,_,_,c3,_) = c3

type Proposition = (Resource, Int)

val :: Proposition -> [State]
val (res, ag) = filter ((ag == ) . project res) statespace

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

hasprinter (pr,_,_,_,_,_,_) a = pr == a 
hasscanner (_,s1,s2,_,_,_,_) a = s1 == a || s2 == a
hascomputer (_,_,_,c1,c2,c3,_) a = c1 == a || c2 == a || c3 == a

component1 :: FODBR State State
component1 = restrict transition
          (\(pr,s1,s2,c1,c2,c3,a) (pr', s1', s2', c1', c2', c3', a') -> 
           (a == s1' && a == s2') || (a == c1' && a == c2' ) || 
           (a == c1' && a == c3') || (a == c2' && a == c3'))

component2 :: FODBR State State
component2 = restrict transition
          (\(pr,s1,s2,c1,c2,c3,a) (pr', s1', s2', c1', c2', c3', a') ->
           (not (needprinter a) && ( pr /= a && pr' == a))   || 
           (not (needscanner a) && ((s1 /= a && s1' == a)    || 
                                      (s2 /= a && s2' == a)))  ||
           (not (needcomputer a) && ( (c1 /= a && c1' == a) || 
                                         (c2 /= a && c2' == a) || 
                                         (c3 /= a && c3' == a) )))
component3 :: FODBR State State
component3 = restrict transition
          (\(pr,s1,s2,c1,c2,c3,a) (pr', s1', s2', c1', c2', c3', a') ->
           sum (zipWith (\x y -> if (x /= a) && (y == a) then 1 else 0) 
                              [pr , s1 , s2 , c1 , c2 , c3 ] 
                              [pr', s1', s2', c1', c2', c3']) > 1)

component4 :: FODBR State State
component4 = restrict transition
          (\s@(pr,s1,s2,c1,c2,c3,a) s' -> 
            (
              (needprinter a && (pr == 0) && not (hasprinter s a)) ||
              (needscanner a && (s1 == 0 || s2 == 0) && not (hasscanner s a)) ||
              (needcomputer a && (c1 == 0 || c2 == 0 || c3 == 0) && not (hascomputer s a))
            ) && not (
              (not (hasprinter s a) && pr == 0 && needprinter a && hasprinter s' a) ||
              (not (hasscanner s a) && (s1 == 0 || s2 == 0) && needscanner a && hasscanner s' a) ||
              (not (hascomputer s a) && (c1 == 0 || c2 == 0 || c3 == 0) && needcomputer a && hascomputer s' a)
            )
          )

eta0 :: FODBR State State
eta0 = component1 `union` component2 `union` component3 `union` component4

stHappy :: Int -> State -> Bool
stHappy 1 (pr, _,  _,  c1, c2, c3, _) = pr == 1 && (c1 == 1 || c2 == 1 || c3 == 1)
stHappy 2 (pr, s1, s2, _,  _,  _,  _) = pr == 2 && (s1 == 2 || s2 == 2)
stHappy 3 (_,  s1, s2, c1, c2, c3, _) = (s1 == 3 || s2 == 3) && 
                                         (c1 == 3 || c2 == 3 || c3 == 3)
stHappy 4 (_,  s1, s2, _,  _,  _,  _) = s1 == 4 || s2 == 4

ownsSomething :: Int -> State -> Bool
ownsSomething n (pr, s1, s2, c1, c2, c3, a) =
   pr == n || s1 == n || s2 == n || 
   c1 == n || c2 == n || c3 == n

eta1 :: FODBR State State
eta1 = restrict transition
        (\s s' -> stHappy (owner (s,s')) s && ownsSomething (owner (s,s')) s')

exampleModel :: Kripke Proposition State
exampleModel = Kripke [1,2,3,4] statespace transition owner val 

exampleModel' :: Kripke Proposition State
exampleModel' = ir exampleModel eta0 [1,2,3,4]

fHasPrinter, fHasScanner, fHasComputer :: Int -> Formula Proposition
fHasPrinter ag = Prop (Pr, ag)
fHasScanner ag = Disj (Prop (S1, ag)) (Prop (S2, ag))
fHasComputer ag = Disj (Prop (C1, ag)) (Disj (Prop (C2, ag)) (Prop (C3, ag)))

fHappy :: Int -> Formula Proposition
fHappy 1 = Conj (fHasPrinter 1) (fHasComputer 1)

fHappy 2 = Conj (fHasPrinter 2) (fHasScanner 2)
fHappy 3 = Conj (fHasScanner 3) (fHasComputer 3)
fHappy 4 = fHasScanner 4

phi1 :: Formula Proposition
phi1 = 
  ag (Conj (af (fHappy 1))(Conj(af (fHappy 2))(Conj(af (fHappy 3))(af (fHappy 4)))))

dontRelease :: FODBR State State
dontRelease = restrict transition
               (\s@(pr,s1,s2,c1,c2,c3,a) (pr',s1',s2',c1',c2',c3',_) ->
                 not (stHappy a s) && 
                 ((pr == a && pr' /= a) || (s1 == a && s1' /= a) ||
                  (s2 == a && s2' /= a) || (c1 == a && c1' /= a) ||
                  (c2 == a && c2' /= a) || (c3 == a && c3' /= a)))

eta1' :: FODBR State State
eta1' = eta1 `union` dontRelease

phi2 :: Formula Proposition
phi2 = EG (Neg (fHappy 2))

