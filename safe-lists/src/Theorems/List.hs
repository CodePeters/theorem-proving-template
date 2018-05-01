{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--exact-data-con" @-}

{-@ LIQUID "--automatic-instances=liquidinstanceslocal" @-}

module Theorems.List where 

import Prelude hiding (length, map, (++), (^), reverse, pred)

import Data.List 
-- NV TODO: the infix annotation is not imported by the above module
{-@ infix   ++ @-}
{-@ infix   ^  @-}
{-@ infix   :  @-}
import Data.Misc 

import Language.Haskell.Liquid.ProofCombinators 

-------------------------------------------------------------------------------
-- | Explicit, paper and pencil proofs ----------------------------------------
-------------------------------------------------------------------------------

-- | Left Identity
appendNilId     :: [a] -> Proof
{-@ appendNilId ::  xs:_ -> { xs ++ [] = xs } @-}
appendNilId []        
  =   [] ++ []
  ==. []
  *** QED  

appendNilId (x:xs)
   =   (x:xs) ++ [] 
   ==. x:(xs ++ xs) 
   ==. (x:xs)        ? appendNilId xs 
   *** QED 

-- | Ignore the proof at runtime: 
-- | appendNilId is a theorem that could be used to prove properties in your code
-- | appendNilId is also an expensive recursive function. 
-- | At runtime appendNilId always provably returns the Haskell value (), 
-- | so no need to recurse at runtime 

{-# RULES "appendNilId/runtime"  forall xs. appendNilId xs = () #-}
{-# NOINLINE  appendNilId #-}




app_length :: [a] -> [a] -> Proof
{-@ app_length ::  xs:_ -> ys:_ -> { length (xs ++ ys) == length xs + length ys } @-}

app_length [] ys
    = length ([] ++ ys)
    ==. length ys
    ==. length [] + length ys
    *** QED

app_length (x:xs) ys
    = length ( (x:xs) ++ ys )
    ==.length  (x:(xs ++ ys) )
    ==. 1 + length (xs ++ ys)
    ==. 1 + length xs + length ys     ? app_length xs ys
    ==. length xs + length ys
    *** QED 

{-# RULES "app_length/runtime"  forall xs ys. app_length xs ys = () #-}
{-# NOINLINE  app_length #-}




app_assoc4 :: [a] -> [a] -> [a] -> [a] -> Proof
{-@ app_assoc4 ::  xs:_ -> ys:_ -> zs:_ -> ws:_ -> { xs ++ (ys ++ (zs ++ ws)) = ((xs ++ ys) ++ zs) ++ ws } @-}

app_assoc4 [] ys zs ws
    = [] ++ (ys ++ (zs ++ ws))
    ==.  ys ++ (zs ++ ws)
    ==. (ys ++ zs) ++ ws     ? appendAssoc ys zs ws
    ==. (([] ++ ys) ++ zs) ++ ws
    *** QED

app_assoc4 (x:xs) ys zs ws
    = (x:xs) ++ (ys ++ (zs ++ ws))
    ==. x:(xs ++ (ys ++ (zs ++ ws)))
    ==. x:(((xs ++ ys) ++ zs) ++ ws)      ? app_assoc4 xs ys zs ws
    ==. (x:((xs ++ ys) ++ zs)) ++ ws 
    ==. ((x:(xs ++ ys)) ++ zs ) ++ ws
    ==. (((x:xs) ++ ys) ++ zs ) ++ ws
    *** QED 

{-# RULES "app_assoc4/runtime"  forall xs ys zs ws. app_assoc4 xs ys zs ws = () #-}
{-# NOINLINE  app_assoc4 #-}




rev_app_distr :: [a] -> [a] -> Proof
{-@ rev_app_distr ::  xs:_ -> ys:_ -> {reverse (xs ++ ys) = reverse (ys) ++ reverse (xs)} @-}

rev_app_distr [] ys
    = reverse ([] ++ ys)
    ==. reverse ys 
    ==. reverse ys ++ []    ? appendNilId (reverse ys)
    ==. (reverse ys) ++ reverse([])    
    *** QED

rev_app_distr (x:xs) ys
    = reverse ((x:xs) ++ ys)
    ==. reverse (x:(xs ++ ys))
    ==. (reverse (xs ++ ys) ) ++ ([x])
    ==. ((reverse ys) ++ (reverse xs) ) ++ ([x])       ? rev_app_distr  xs ys
    ==. (reverse ys) ++ ((reverse xs) ++ ([x]))        ? appendAssoc (reverse ys) (reverse xs) ([x])
    ==. (reverse ys) ++ (reverse (x:xs)) 
    *** QED

{-# RULES "rev_app_distr/runtime"  forall xs ys. rev_app_distr xs ys = () #-}
{-# NOINLINE  rev_app_distr #-}




rev_involutive :: [a] ->  Proof
{-@ rev_involutive ::  xs:_ -> { reverse (reverse xs) =  xs } @-}

rev_involutive []
    = reverse (reverse [])
    ==. reverse [] 
    ==. []
    *** QED

rev_involutive (x:xs)
    = reverse (reverse (x:xs) )
    ==. reverse ( (reverse xs) ++ ([x]) )
    ==. (reverse ([x]) ) ++ (reverse ( (reverse xs) ))    ? rev_app_distr (reverse xs) ([x])
    ==. (reverse ([x]) ) ++ xs                            ? rev_involutive xs
    ==. ( (reverse [] ) ++ ([x]) ) ++ xs
    ==. ([] ++ ([x])) ++ xs
    ==. ([x]) ++ xs
    ==. x:([] ++ xs)
    ==. x:xs
    *** QED

{-# RULES "rev_involutive/runtime"  forall xs. rev_involutive xs  = () #-}
{-# NOINLINE  rev_involutive #-}




rev_length :: [a] -> Proof
{-@ rev_length :: xs:_ -> { length (reverse xs) == length xs } @-}

rev_length []
    = length (reverse [])
    ==.length []
    *** QED

rev_length (x:xs)
    = length (reverse (x:xs))
    ==. length ( (reverse xs) ++ ([x]) )
    ==. length (reverse xs) + length ([x])    ? app_length  (reverse xs)  ([x])
    ==. length xs + length ([x])              ? rev_length xs
    ==. length (([x]) ++ xs )                 ? app_length ([x]) xs
      ==. length (x:([] ++ xs))
    ==. length (x:xs)
    *** QED

{-# RULES "rev_length/runtime"  forall xs. rev_length xs = () #-}
{-# NOINLINE  rev_length #-}   




nonzeros_app :: [Int] -> [Int] -> Proof
{-@  nonzeros_app ::  xs:_ -> ys:_ -> { nonzeros (xs ++ ys) = (nonzeros xs) ++ (nonzeros ys) } @-}

nonzeros_app [] ys
    = nonzeros ([] ++ ys)
    ==. nonzeros ys
    ==. [] ++ (nonzeros ys)
    ==. (nonzeros []) ++ (nonzeros ys)
    *** QED

nonzeros_app (0:xs) ys
    = nonzeros ( (0:xs) ++ ys)
    ==. nonzeros (0:(xs ++ ys))
    ==. nonzeros (xs ++ ys)
    ==. nonzeros (xs) ++ nonzeros (ys)           ? (nonzeros_app xs ys)
    ==. nonzeros (0:xs) ++ nonzeros (ys)           
    *** QED    

nonzeros_app (x:xs) ys
    = nonzeros ( (x:xs) ++ ys)
    ==. nonzeros (x:(xs ++ ys))
    ==. (x:(nonzeros ( xs ++ ys))) 
    ==. (x:((nonzeros xs) ++ (nonzeros ys))) ?(nonzeros_app xs ys)
    ==. (x:(nonzeros xs)) ++ (nonzeros ys)
    ==. (nonzeros (x:xs)) ++ (nonzeros ys)
    *** QED    


{-# RULES " nonzeros_app/runtime"  forall xs ys. nonzeros_app xs ys = () #-}
{-# NOINLINE   nonzeros_app #-}



tl_length_pred :: [a] -> Proof
{-@ tl_length_pred ::  xs:_ -> { pred (length xs) == length ( select_C_2 xs) } @-}

tl_length_pred []
   = pred (length [])
   ==. length []
   ==. length( select_C_2 [])
   *** QED

tl_length_pred (x:xs)
   = pred (length (x:xs))
   ==. length xs                        ? tl_length_pred xs
   ==. length( select_C_2 (x:xs))
   *** QED

{-# RULES "tl_length_pred/runtime"  forall xs. tl_length_pred xs = () #-}
{-# NOINLINE  tl_length_pred #-}


beq_natlist_refl :: [Int]  -> Proof
{-@ beq_natlist_refl ::  xs: [Nat] -> { beq_list xs xs } @-}

beq_natlist_refl []
   = (beq_list [] [])
   ==. True
   *** QED

beq_natlist_refl (x:xs) 
   =  beq_list (x:xs) (x:xs) 
   ==. beq_list xs xs      
   ==. True                ? beq_natlist_refl xs
   *** QED

{-# RULES "beq_natlist_refl/runtime"  forall xs. beq_natlist_refl xs = () #-}
{-# NOINLINE  beq_natlist_refl #-}


-------------------------------------------------------------------------------
-- | Automatic Proofs ---------------------------------------------------------
-------------------------------------------------------------------------------

-- | Associativity proofs automated by automatic-instances
{-@ automatic-instances appendAssoc @-}
appendAssoc :: [a] -> [a] -> [a] -> Proof
{-@ appendAssoc :: xs:_ -> ys:_ -> zs:_ 
                -> { xs ++ (ys ++ zs) = (xs ++ ys) ++ zs } @-}
appendAssoc [] _ _          = trivial
appendAssoc (_:xs) ys zs = appendAssoc xs ys zs

{-# RULES "appendNilId/runtime"  forall xs ys zs. appendAssoc xs ys zs = () #-}
{-# NOINLINE  appendAssoc #-}

-------------------------------------------------------------------------------
-- | Use proofs for efficiency ------------------------------------------------
-------------------------------------------------------------------------------

-- | Map Fusion
-- | After you actually prove mapFusion, 

{-@ mapFusion :: f:_ -> g:_ -> xs:_ 
              -> { map f (map g xs) = map (f ^ g) xs } @-}

-- | you can use it to optimize your code

{-# RULES "mapFusion/apply" forall f g xs.  map f (map g xs) = map (f ^ g) xs #-}

{-@ automatic-instances mapFusion @-}
mapFusion :: (b -> c) -> (a -> b) -> [a] -> Proof
mapFusion _ _ []        = trivial 
mapFusion f g (_:xs) = mapFusion f g xs 

{-# RULES "mapFusion/runtime"  forall f g xs. mapFusion f g xs = () #-}
{-# NOINLINE  mapFusion #-}
