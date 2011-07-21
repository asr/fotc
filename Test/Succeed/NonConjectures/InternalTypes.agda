module Test.Succeed.NonConjectures.InternalTypes where

-- Agda 2.2.9 (13 November 2010) internal types (from Agda.Syntax.Internal)

-- | Raw values.
--
--   @Def@ is used for both defined and undefined constants.
--   Assume there is a type declaration and a definition for
--     every constant, even if the definition is an empty
--     list of clauses.
--
-- data Term = Var Nat Args
-- 	  | Lam Hiding (Abs Term)   -- ^ terms are beta normal
-- 	  | Lit Literal
-- 	  | Def QName Args
-- 	  | Con QName Args
-- 	  | Pi (Arg Type) (Abs Type)
-- 	  | Fun (Arg Type) Type
-- 	  | Sort Sort
-- 	  | MetaV MetaId Args
--           | DontCare               -- ^ nuked irrelevant and other stuff
--   deriving (Typeable, Data, Eq, Ord, Show)
-- -- Andreas 2010-09-21: @DontCare@ replaces the hack @Sort Prop@

-- data Type = El Sort Term
--   deriving (Typeable, Data, Eq, Ord, Show)

-- data Sort = Type Term   -- A term of type Level
-- 	  | Prop  -- ignore me
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
  D   : Set
  _≡_ : D → D → Set

postulate
  P₁    : D → Set
  P₃    : D → D → D → Set
  a b c : D

------------------------------------------------------------------------------
-- Testing data Term = Def ...

-- A definition with one argument
postulate termDef₁ : P₁ a
{-# ATP axiom termDef₁ #-}

-- A definition with three or more arguments
postulate termDef₃ : P₃ a b c
{-# ATP axiom termDef₃ #-}

------------------------------------------------------------------------------
-- Testing data Term = Fun ...

postulate termFun : P₁ a → P₁ a
{-# ATP axiom termFun #-}

------------------------------------------------------------------------------
-- Testing data Term = Lam ...

postulate
  ∃       : (P₁ : D → Set) → Set
  termLam : ∃ (λ e → P₁ e)
{-# ATP axiom termLam #-}

------------------------------------------------------------------------------
-- Testing data Term = Pi ...

postulate termPi : (d : D) → P₁ d
{-# ATP axiom termPi #-}

------------------------------------------------------------------------------
-- The conjecture

-- We need to have at least one conjecture to generate a TPTP file.
postulate refl : ∀ d → d ≡ d
{-# ATP prove refl #-}
