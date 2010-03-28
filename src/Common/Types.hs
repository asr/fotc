------------------------------------------------------------------------------
-- Common types
------------------------------------------------------------------------------

module Common.Types where

-- Agda library imports
import Agda.Syntax.Abstract

------------------------------------------------------------------------------

-- In Agda.Syntax.Abstract an ATP pragma is defined by
-- data Pragma = ...
--             | PragmaATP RoleATP QName [QName]
--
-- where the type QName corresponds to the postulate name and
-- [QName] corresponds to the hints names.

type PostulateName = QName
type HintName      = QName