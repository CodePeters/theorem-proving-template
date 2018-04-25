{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--exact-data-con" @-}

module Data.List where 

import Prelude hiding (length, map, (++), reverse, pred)

data L a = N | C a (L a)
  deriving (Eq, Show)
{-@ data L [length]  @-}

{-@ measure length @-}
length :: L a -> Int 
-- NV TODO: this invariant is required when length is imported
{-@ invariant {v:L a| 0 <= length v } @-}
{-@ length :: L a -> Nat @-}
length N        = 0 
length (C _ xs) = 1 + length xs 


{-@ reflect reverse @-}
reverse :: L a -> L a
reverse N        = N
reverse (C x xs) = reverse xs ++ (C x N) 


{-@ reflect nonzeros @-}
nonzeros ::  L Int -> L Int
nonzeros N = N
nonzeros (C x xs) = if (x==0) then nonzeros xs else C x (nonzeros xs)



{-@ reflect pred @-}
pred :: Int -> Int
pred n 
  | n == 0 = 0
  | otherwise = n-1


{-@ reflect select_C_2 @-}
select_C_2 :: L a -> L a
select_C_2 N = N
select_C_2 (C _ xs) = xs


{-@ reflect beq_list @-}
beq_list :: L Int -> L Int -> Bool
beq_list N N = True
beq_list N _ = False
beq_list _ N = False
beq_list (C x xs) (C y ys) = if (x==y) then (beq_list xs ys) else False


{-@ reflect map @-}
map :: (a -> b) -> L a -> L b 
map _ N        = N 
map f (C x xs) = f x `C` map f xs 

{-@ infix   ++ @-}
{-@ reflect ++ @-}
(++) :: L a -> L a -> L a 
N        ++ ys = ys 
(C x xs) ++ ys = C x (xs ++ ys)




