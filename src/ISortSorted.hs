{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module ISortSorted where 

import Prelude hiding (pure,(<*>),(>>=), length)
import List 
import Language.Haskell.Liquid.ProofCombinators 

import RTick 
import ISort 

{-@ ignore theorem @-}
theorem :: Ord a => [a] -> () 
{-@ theorem :: Ord a => xs:OList a 
            -> { tcost (isort xs) <= length xs } @-} 
theorem []  = ()
theorem (x:xs) 
  =   tcost (isort (x:xs)) 
  === tcost (bbind (length xs) (isort xs) (insert x))
  === tcost (isort xs) + tcost ((insert x) (tval (isort xs)))
      ? isortSortedVal xs -- tval (isort xs) == xs
  === tcost (isort xs) + tcost (insert x xs)
      ? theorem xs 
  =<= length xs + tcost (insert x xs)
  =<= length xs + 1      -- FAILS: xs := y:ys and x <= y 
  =<= length (x:xs)
  *** QED 







isortSortedVal :: Ord a => [a] -> () 
{-@ isortSortedVal :: Ord a => xs:OList a -> { tval (isort xs) == xs }  @-}
isortSortedVal []     = () 
isortSortedVal [_]    = () 
isortSortedVal (_:xs) = isortSortedVal xs 
