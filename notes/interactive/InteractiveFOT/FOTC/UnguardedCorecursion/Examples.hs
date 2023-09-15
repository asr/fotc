
module Examples where

-- This unguarded function is accepted by Telford and Turner (1998),
evens :: [Int]
evens = 2 : map (+2) evens

-- but this unguarded function is correctly rejected
bh :: [Int]
bh = 1 : tail bh

-- Other examples
alter :: [Bool]
alter = True : map not alter

alter' :: [Bool]
alter' = True : False : alter'

test :: Bool
test = take 10 alter == take 10 alter'

------------------------------------------------------------------------------
-- References
--
-- Telford, Alastair and Turner, David (1998). Ensuring the
-- Productivity of Infinite Structures. Tech. rep. 14-97. Revised March
-- 1998. The Computing Laboratory. University of Kent.
