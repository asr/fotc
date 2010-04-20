------------------------------------------------------------------------------
-- Handling of Agda abstract names
------------------------------------------------------------------------------

module MyAgda.Syntax.Abstract.Name where

-- Haskell imports
import Data.List ( intersperse )

-- Agda library imports
import Agda.Syntax.Abstract.Name
    ( ModuleName(MName)
    , mnameToList
    )

------------------------------------------------------------------------------

-- Adapted from 'instance Show ModuleName' in Agda.Syntax.Abstract.Name
-- TODO: Can we use Agda.Syntax.Concrete.Name.moduleNameToFileName?
moduleNameToFilePath :: ModuleName -> FilePath
moduleNameToFilePath m = concat $ intersperse "/" $ map show $ mnameToList m

removeLastNameModuleName :: ModuleName -> ModuleName
removeLastNameModuleName (MName names ) = MName (init names)