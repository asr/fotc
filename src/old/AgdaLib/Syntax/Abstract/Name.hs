------------------------------------------------------------------------------
-- Handling of Agda abstract names
------------------------------------------------------------------------------

{-# LANGUAGE UnicodeSyntax #-}

module AgdaLib.Syntax.Abstract.Name
    ( dropLastNameModuleName
    , moduleNameToFilePath
    ) where

-- Haskell imports
import Data.List ( intercalate )

-- Agda library imports
import Agda.Syntax.Abstract.Name
    ( ModuleName(MName)
    , mnameToList
    )

------------------------------------------------------------------------------
-- Adapted from 'instance Show ModuleName' in Agda.Syntax.Abstract.Name
moduleNameToFilePath ∷ ModuleName → FilePath
moduleNameToFilePath m = intercalate "/" (map show $ mnameToList m)

dropLastNameModuleName ∷ ModuleName → ModuleName
dropLastNameModuleName (MName names) = MName (init names)
