------------------------------------------------------------------------------
-- Translation of things about Agda concrete names
------------------------------------------------------------------------------

module FOL.Translation.Concrete.Name where

-- Agda library imports
import Agda.Syntax.Concrete.Name ( NamePart(Id, Hole) )

------------------------------------------------------------------------------

takeId :: NamePart -> String
takeId Hole         = []
takeId (Id strName) = strName

-- We use the parts of a name to produce a new function name,
-- e.g. the function 'if_then_else_' is called 'ifthenelse'.
concatName :: [NamePart] -> String
concatName parts = concatMap takeId parts
