{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--exact-data-con" @-}

module Data.List where 

import Prelude hiding (length, map, (++), reverse, pred)

{-@ infix   : @-}

{-@ measure length @-}
length :: [a] -> Int 
-- NV TODO: this invariant is required when length is imported
{-@ invariant {v: [a] | 0 <= length v } @-}
{-@ length :: [a] -> Nat @-}
length []        = 0 
length (x:xs) = 1 + length xs 


{-@ reflect reverse @-}
reverse :: [a] -> [a]
reverse []        = []
reverse (x:xs) = reverse xs ++ [x] 


{-@ reflect nonzeros @-}
nonzeros ::  [Int] -> [Int]
nonzeros [] = []
nonzeros (x:xs) = if (x==0) then nonzeros xs else x:(nonzeros xs)


{-@ reflect pred @-}
pred :: Int -> Int
pred n 
  | n == 0 = 0
  | otherwise = n-1


{-@ reflect select_C_2 @-}
select_C_2 :: [a] -> [a]
select_C_2 [] = []
select_C_2 (x:xs) = xs


{-@ reflect beq_list @-}
beq_list :: [Int] -> [Int] -> Bool
beq_list [] []         = True
beq_list [] _          = False
beq_list _ []          = False
beq_list (x:xs) (y:ys) = if (x==y) then (beq_list xs ys) else False


{-@ reflect map @-}
map :: (a -> b) -> [a] -> [b] 
map _ []     = [] 
map f (x:xs) = f x : (map f xs) 


{-@ infix   ++ @-}
{-@ reflect ++ @-}
(++) :: [a] -> [a] -> [a] 
[]        ++ ys = ys 
(x:xs) ++ ys = x:(xs ++ ys)

