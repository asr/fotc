-- Tested with the development version of Agda on 13 July 2012.

-- Testing how the pragmas are saved in the agda interface files (using
-- the program read-agda interface).

-- 13 July 2012. I couldn't find information about the pragma in the
-- interface file.

module Pragma2 where

{-# NO_TERMINATION_CHECK #-}
foo : Set
foo = foo
