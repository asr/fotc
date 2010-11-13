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
  D : Set

------------------------------------------------------------------------------
-- Testing data Term = Def ...

module Def where

  postulate
    P₁    : D → Set
    P₃    : D → D → D → Set
    a b c : D

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

module Fun where

  postulate
    P       : D → Set
    a       : D
    termFun : P a → P a
  {-# ATP axiom termFun #-}

------------------------------------------------------------------------------
-- Testing data Term = Lam ...

module Lam where

  postulate
    P       : D → Set
    ∃D      : (P : D → Set) → Set
    termLam : ∃D (λ e → P e)
  {-# ATP axiom termLam #-}

------------------------------------------------------------------------------
-- Testing data Term = Pi ...

module Pi where
  postulate
    P      : D → Set
    termPi : (d : D) → P d
  {-# ATP axiom termPi #-}
