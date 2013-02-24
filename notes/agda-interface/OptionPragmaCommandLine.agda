-- Testing how the pragmas are saved in the agda interface files (using
-- the program dump-agdai) when they are used from the command-line:

-- $ agda --no-termination-check OptionPragmaCommandLine.agda

-- 17 October 2012. Because the PragmaOption --no-termination-check
-- was used from the command-line it is *not* saved in the interface
-- file.

-- iPragmaOptions = []

module OptionPragmaCommandLine where
