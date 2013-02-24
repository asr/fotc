-- Testing how the pragmas are saved in the Agda interface files (using
-- the program dump-agdai interface).

-- 13 July 2012. Because for example the pragma BUILTIN is not a
-- PragmaOption it is not saved in iPragmaOptions, i.e.
--
-- iPragmaOptions = []

module NoOptionPragma where

data Bool : Set where
  true false : Bool

{-# BUILTIN BOOL  Bool  #-}
{-# BUILTIN TRUE  true  #-}
{-# BUILTIN FALSE false #-}
