{-# OPTIONS --no-termination-check #-}

-- Tested with the development version of Agda on 17 October 2012.

-- Testing how the pragmas are saved in the agda interface files (using
-- the program dump-agdai).

-- 13 July 2012. Because for example the --no-termination-check is a
-- PragmaOption it is saved as:
--
-- iPragmaOptions = [["--no-termination-check"]]

module OptionPragma where
