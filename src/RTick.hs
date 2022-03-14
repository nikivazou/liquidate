{-@ LIQUID "--reflection" @-}

module RTick where 
import Prelude hiding (pure,(<*>))

data RTick a = RTick Int a  

{-@ measure tcost @-}
tcost :: RTick a -> Int 
tcost (RTick x _) = x 

{-@ measure tval @-}
tval :: RTick a -> a 
tval (RTick _ x) = x 


{-@ reflect pure @-}
{-@ pure :: x:a -> {t:RTick a | tcost t == 0 && tval t == x } @-}
pure :: a -> RTick a 
pure x = RTick 0 x


{-@ reflect <*> @-}
{-@ (<*>) :: f:RTick (a -> b) -> x:RTick a 
          -> {t:RTick b | tcost t == tcost f + tcost x && tval t == (tval f) (tval x)} @-} 
(<*>) :: RTick (a -> b) -> RTick a -> RTick b 
RTick i f <*> RTick j x = RTick (i+j) (f x)