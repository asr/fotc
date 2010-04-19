------------------------------------------------------------------------------
-- Handling of Agda abstract names
------------------------------------------------------------------------------

module MyAgda.Syntax.Abstract.Name where

-- Haskell imports
import Data.List

-- Agda library imports
import Agda.Syntax.Abstract ( ModuleName(..))

------------------------------------------------------------------------------

-- Adapted from 'instance Show ModuleName' in Agda.Syntax.Abstract.Name
-- TODO: Can we use Agda.Syntax.Concrete.Name.moduleNameToFileName
moduleNameToFilePath :: ModuleName -> FilePath
moduleNameToFilePath m = concat $ intersperse "/" $ map show $ mnameToList m
