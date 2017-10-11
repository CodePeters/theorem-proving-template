{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--exact-data-con" @-}

{-@ LIQUID "--automatic-instances=liquidinstanceslocal" @-}

module Theorems where 

import Prelude hiding (length, map, (++))

import List 
{-@ infix   ++ @-}

import Misc 

import Language.Haskell.Liquid.ProofCombinators 


appendNilId     :: L a -> Proof
{-@ appendNilId ::  xs:_ -> { xs ++ N = xs } @-}
appendNilId N        
  =   N ++ N 
  ==. N 
  *** QED  
appendNilId (C x xs)
   =   (C x xs) ++ N 
   ==. C x (xs ++ N) 
   ==. C x xs        ? appendNilId xs 
   *** QED 


{-@ automatic-instances appendAssoc @-}
appendAssoc :: L a -> L a -> L a -> Proof
{-@ appendAssoc :: xs:_ -> ys:_ -> zs:_ 
                -> { xs ++ (ys ++ zs) = (xs ++ ys) ++ zs } @-}
appendAssoc N _ _          = trivial
appendAssoc (C _ xs) ys zs = appendAssoc xs ys zs


{-@ automatic-instances mapFusion @-}
mapFusion :: (a -> b) -> (b -> c) -> L a -> Proof
{-@ mapFusion :: f:_ -> g:_ -> xs:_ 
              -> { map (f o g) xs = map (f o g) xs } @-}
mapFusion _ _ N        = trivial 
mapFusion f g (C _ xs) = mapFusion f g xs 