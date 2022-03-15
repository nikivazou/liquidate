{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module ISortSorted where 

import Prelude hiding (pure,(<*>),(>>=), length)
import List 
import Language.Haskell.Liquid.ProofCombinators 

import RTick 
import ISort 

theorem :: Ord a => [a] -> () 
{-@ theorem :: Ord a => xs:OList a 
            -> { tcost (isort xs) <= length xs } @-} 
theorem []  = () 
theorem [_] = ()
theorem (x:xs) 
  =   tcost (isort (x:xs)) 
  === tcost (bbind (length xs) (isort xs) (insert x))
  === tcost (isort xs) + tcost ((insert x) (tval (isort xs)))
      ? isortSortedVal xs 
  === tcost (isort xs) + tcost (insert x xs)
      ? theorem xs 
  =<= length xs + 1
  =<= length (x:xs)
  *** QED 


isortSortedVal :: Ord a => [a] -> () 
{-@ isortSortedVal :: Ord a => xs:OList a -> { tval (isort xs) == xs }  @-}
isortSortedVal [] = () 
isortSortedVal [_] = () 
isortSortedVal (x:xs) 
  =   tval (isort (x:xs))
  === tval (bbind (length xs) (isort xs) (insert x)) 
  === tval ((insert x) (tval (isort xs)))
       ? isortSortedVal xs 
  === tval (insert x xs) 
  === (x:xs)
  *** QED 