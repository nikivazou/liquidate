{-@ LIQUID "--reflection" @-}
module ISort where 

import Prelude hiding (pure,(<*>))
import RTick 

insert :: (Ord a) => a -> [a] -> RTick [a]
insert x []   = pure [x]
insert x (y:ys) 
  | x <= y    = pure (x:y:ys)
  | otherwise = pure (y:) <*> insert x ys 