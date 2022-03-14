{-@ LIQUID "--reflection" @-}
module ISort where 

import Prelude hiding (pure,(<*>))
import RTick 

insert :: (Ord a) => a -> [a] -> RTick [a]
{-@ insert :: (Ord a) 
           => x:a -> xs:[a] 
           -> {t:RTick {os:[a] | len os == len xs + 1} | tcost t <= len xs } @-}
insert x []   = pure [x]
insert x (y:ys) 
  | x <= y    = pure (x:y:ys)
  | otherwise = pure (y:) <*> insert x ys 