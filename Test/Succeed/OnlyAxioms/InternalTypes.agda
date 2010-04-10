module Test.Succeed.OnlyAxioms.InternalTypes where

-- Agda internal types (from Agda.Syntax.Internal)

-- -- | Raw values.
-- --
-- --   @Def@ is used for both defined and undefined constants.
-- --   Assume there is a type declaration and a definition for
-- --     every constant, even if the definition is an empty
-- --     list of clauses.
-- --
-- data Term = Var Nat Args
-- 	  | Lam Hiding (Abs Term)   -- ^ terms are beta normal
-- 	  | Lit Literal
-- 	  | Def QName Args
-- 	  | Con QName Args
-- 	  | Pi (Arg Type) (Abs Type)
-- 	  | Fun (Arg Type) Type
-- 	  | Sort Sort
-- 	  | MetaV MetaId Args
--   deriving (Typeable, Data, Eq, Ord, Show)

-- data Type = El Sort Term
--   deriving (Typeable, Data, Eq, Ord, Show)

-- data Sort = Type Term   -- A term of type Nat
-- 	  | Prop
-- 	  | Lub Sort Sort
-- 	  | Suc Sort
-- 	  | MetaS MetaId Args
--           | Inf
--           | DLub Sort (Abs Sort)
--             -- ^ if the free variable occurs in the second sort
--             --   the whole thing should reduce to Inf, otherwise
--             --   it's the normal Lub
--   deriving (Typeable, Data, Eq, Ord, Show)

postulate
  D     : Set
  P₁    : D → Set
  P₃    : D → D → D → Set
  a b c : D

------------------------------------------------------------------------------
-- Testing data Term = Def ...

-- A definition with one argument
postulate
  termDef₁ : P₁ a
{-# ATP axiom termDef₁ #-}

-- A definition with three or more arguments
postulate
  termDef₃ : P₃ a b c
{-# ATP axiom termDef₃ #-}

------------------------------------------------------------------------------
-- Testing data Term = Fun ...
postulate
  termFun : P₁ a  → P₁ a
{-# ATP axiom termFun #-}

------------------------------------------------------------------------------
-- Testing data Term = Pi ...
postulate
  termPi : (d : D) → P₁ d
{-# ATP axiom termPi #-}
