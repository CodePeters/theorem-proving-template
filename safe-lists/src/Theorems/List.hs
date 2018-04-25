{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--exact-data-con" @-}

{-@ LIQUID "--automatic-instances=liquidinstanceslocal" @-}

module Theorems.List where 

import Prelude hiding (length, map, (++), (^), reverse, pred)

import Data.List 
-- NV TODO: the infix annotation is not imported by the above module
{-@ infix   ++ @-}
{-@ infix   ^  @-}
import Data.Misc 

import Language.Haskell.Liquid.ProofCombinators 

-------------------------------------------------------------------------------
-- | Explicit, paper and pencil proofs ----------------------------------------
-------------------------------------------------------------------------------

-- | Left Identity
appendNilId     :: L a -> Proof
{-@ appendNilId ::  xs:_ -> { xs ++ N = xs } @-}
appendNilId N        
  =   N ++ N
  ==. N 
  *** QED  
appendNilId (C x xs)
   =   (C x xs) ++ N 
   ==. C x (xs ++ xs) 
   ==. C x xs        ? appendNilId xs 
   *** QED 

-- | Ignore the proof at runtime: 
-- | appendNilId is a theorem that could be used to prove properties in your code
-- | appendNilId is also an expensive recursive function. 
-- | At runtime appendNilId always provably returns the Haskell value (), 
-- | so no need to recurse at runtime 

{-# RULES "appendNilId/runtime"  forall xs. appendNilId xs = () #-}
{-# NOINLINE  appendNilId #-}




app_length :: L a -> L a -> Proof
{-@ app_length ::  xs:_ -> ys:_ -> { length (xs ++ ys) == length xs + length ys } @-}

app_length N ys
    = length (N ++ ys)
    ==. length ys
    ==. length N + length ys
    *** QED

app_length (C x xs) ys
    = length ( (C x xs) ++ ys )
    ==.length  ( C x (xs ++ ys) )
    ==. 1 + length (xs ++ ys)
    ==. 1 + length xs + length ys     ? app_length xs ys
    ==. length xs + length ys
    *** QED 

{-# RULES "app_length/runtime"  forall xs ys. app_length xs ys = () #-}
{-# NOINLINE  app_length #-}




app_assoc4 :: L a -> L a -> L a -> L a -> Proof
{-@ app_assoc4 ::  xs:_ -> ys:_ -> zs:_ -> ws:_ -> { xs ++ (ys ++ (zs ++ ws)) = ((xs ++ ys) ++ zs) ++ ws } @-}

app_assoc4 N ys zs ws
    = N ++ (ys ++ (zs ++ ws))
    ==.  ys ++ (zs ++ ws)
    ==. (ys ++ zs) ++ ws     ? appendAssoc ys zs ws
    ==. ((N ++ ys) ++ zs) ++ ws
    *** QED

app_assoc4 (C x xs) ys zs ws
    = (C x xs) ++ (ys ++ (zs ++ ws))
    ==. C x (xs ++ (ys ++ (zs ++ ws)))
    ==. C x (((xs ++ ys) ++ zs) ++ ws)      ? app_assoc4 xs ys zs ws
    ==. (C x ((xs ++ ys) ++ zs)) ++ ws 
    ==. ((C x (xs ++ ys)) ++ zs ) ++ ws
    ==. (((C x xs) ++ ys) ++ zs ) ++ ws
    *** QED 

{-# RULES "app_assoc4/runtime"  forall xs ys zs ws. app_assoc4 xs ys zs ws = () #-}
{-# NOINLINE  app_assoc4 #-}




rev_app_distr :: L a -> L a -> Proof
{-@ rev_app_distr ::  xs:_ -> ys:_ -> {reverse (xs ++ ys) = reverse (ys) ++ reverse (xs)} @-}

rev_app_distr N ys
    = reverse (N ++ ys)
    ==. reverse ys 
    ==. reverse ys ++ N    ? appendNilId (reverse ys)
    ==. (reverse ys) ++ reverse(N)    
    *** QED

rev_app_distr (C x xs) ys
    = reverse ((C x xs) ++ ys)
    ==. reverse (C x (xs ++ ys))
    ==. (reverse (xs ++ ys) ) ++ (C x N)
    ==. ((reverse ys) ++ (reverse xs) ) ++ (C x N)       ? rev_app_distr  xs ys
    ==. (reverse ys) ++ ((reverse xs) ++ (C x N))        ? appendAssoc (reverse ys) (reverse xs) (C x N)
    ==. (reverse ys) ++ (reverse (C x xs)) 
    *** QED

{-# RULES "rev_app_distr/runtime"  forall xs ys. rev_app_distr xs ys = () #-}
{-# NOINLINE  rev_app_distr #-}




rev_involutive :: L a ->  Proof
{-@ rev_involutive ::  xs:_ -> { reverse (reverse xs) =  xs } @-}

rev_involutive N 
    = reverse (reverse N)
    ==. reverse N 
    ==. N
    *** QED

rev_involutive (C x xs)
    = reverse (reverse (C x xs) )
    ==. reverse ( (reverse xs) ++ (C x N) )
    ==. (reverse (C x N) ) ++ (reverse ( (reverse xs) ))    ? rev_app_distr (reverse xs) (C x N)
    ==. (reverse (C x N) ) ++ xs                            ? rev_involutive xs
    ==. ( (reverse N ) ++ (C x N) ) ++ xs
    ==. (N ++ (C x N)) ++ xs
    ==. (C x N) ++ xs
    ==. C x (N ++ xs)
    ==. C x xs
    *** QED

{-# RULES "rev_involutive/runtime"  forall xs. rev_involutive xs  = () #-}
{-# NOINLINE  rev_involutive #-}




rev_length :: L a -> Proof
{-@ rev_length :: xs:_ -> { length (reverse xs) == length xs } @-}

rev_length N
    = length (reverse N)
    ==.length N
    *** QED

rev_length (C x xs)
    = length (reverse (C x xs))
    ==. length ( (reverse xs) ++ (C x N) )
    ==. length (reverse xs) + length (C x N)    ? app_length  (reverse xs)  (C x N)
    ==. length xs + length (C x N)              ? rev_length xs
    ==. length ((C x N) ++ xs )                 ? app_length (C x N) xs
    ==. length (C x (N ++ xs))
    ==. length (C x xs)
    *** QED

{-# RULES "rev_length/runtime"  forall xs. rev_length xs = () #-}
{-# NOINLINE  rev_length #-}   




nonzeros_app :: L Int -> L Int -> Proof
{-@  nonzeros_app ::  xs:_ -> ys:_ -> { nonzeros (xs ++ ys) = (nonzeros xs) ++ (nonzeros ys) } @-}

nonzeros_app N ys
    = nonzeros (N ++ ys)
    ==. nonzeros ys
    ==. N ++ (nonzeros ys)
    ==. (nonzeros N) ++ (nonzeros ys)
    *** QED

nonzeros_app (C 0 xs) ys
    = nonzeros ( (C 0 xs) ++ ys)
    ==. nonzeros (C 0 (xs ++ ys))
    ==. nonzeros (xs ++ ys)
    ==. nonzeros (xs) ++ nonzeros (ys)           ? (nonzeros_app xs ys)
    ==. nonzeros (C 0 xs) ++ nonzeros (ys)           
    *** QED    

nonzeros_app (C x xs) ys
    = nonzeros ( (C x xs) ++ ys)
    ==. nonzeros (C x (xs ++ ys))
    ==. (C x (nonzeros ( xs ++ ys))) 
    ==. (C x ((nonzeros xs) ++ (nonzeros ys))) ?(nonzeros_app xs ys)
    ==. (C x (nonzeros xs)) ++ (nonzeros ys)
    ==. (nonzeros (C x xs)) ++ (nonzeros ys)
    *** QED    


{-# RULES " nonzeros_app/runtime"  forall xs ys. nonzeros_app xs ys = () #-}
{-# NOINLINE   nonzeros_app #-}



tl_length_pred :: L a -> Proof
{-@ tl_length_pred ::  xs:_ -> { pred (length xs) == length ( select_C_2 xs) } @-}

tl_length_pred N 
   = pred (length N)
   ==. length N
   ==. length( select_C_2 N)
   *** QED

tl_length_pred (C x xs)
   = pred (length (C x xs))
   ==. length xs                        ? tl_length_pred xs
   ==. length( select_C_2 (C x xs))
   *** QED

{-# RULES "tl_length_pred/runtime"  forall xs. tl_length_pred xs = () #-}
{-# NOINLINE  tl_length_pred #-}


beq_natlist_refl :: L Int  -> Proof
{-@ beq_natlist_refl ::  xs:L Nat -> { beq_list xs xs } @-}

beq_natlist_refl N 
   = (beq_list N N)
   ==. True
   *** QED

beq_natlist_refl (C x xs) 
   =  beq_list (C x xs) (C x xs) 
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
appendAssoc :: L a -> L a -> L a -> Proof
{-@ appendAssoc :: xs:_ -> ys:_ -> zs:_ 
                -> { xs ++ (ys ++ zs) = (xs ++ ys) ++ zs } @-}
appendAssoc N _ _          = trivial
appendAssoc (C _ xs) ys zs = appendAssoc xs ys zs

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
mapFusion :: (b -> c) -> (a -> b) -> L a -> Proof
mapFusion _ _ N        = trivial 
mapFusion f g (C _ xs) = mapFusion f g xs 

{-# RULES "mapFusion/runtime"  forall f g xs. mapFusion f g xs = () #-}
{-# NOINLINE  mapFusion #-}
