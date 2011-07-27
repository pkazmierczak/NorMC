{-
This module serves as a tool for finding loops (used for finding bugs in
the example mentioned in the paper). Provides counter examples.
-}

module Loops where

import FODBR
import Ex02

revpaths :: (Ord a) => FODBR a a -> [[a]] -> [[a]]
revpaths rel hists = hists ++ revpaths rel hists'
  where
    hists' = concat $ map (\hist -> map (:hist) (find1 (fst rel)
                                                 (head hist))) hists

loop :: (Eq a) => [a] -> Bool
loop (h:t) = h `elem` t
loop _ = False

eta01NotEnough = map reverse $ 
                 filter loop (revpaths (transition `minus` 
                                        (eta_0 `union` eta_1)) [[(0,0,0,0,0,0,1)]])
                 
counterExample = head eta01NotEnough