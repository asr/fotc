{-# OPTIONS --no-termination-check #-}

-- Tested with the development version of Agda on 13 July 2012.

-- Testing how the pragmas are saved in the agda interface files (using
-- the program read-agda interface).

-- 13 July 2012. The pragma is saved as:
--
-- iPragmaOptions = [["--no-termination-check"]]

module Pragma1 where
