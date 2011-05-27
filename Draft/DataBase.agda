module Draft.DataBase where

open import Common.Data.Product

postulate
  P Q R S : Set
  h₁      : P → Q
  h₂      : Q → R
  h₃      : R → S

postulate
  thm₁ : P → S
{-# ATP prove thm₁ h₁ h₂ h₃ #-}

-- Nils' idea about databases in the Agda mailing list.
-- http://thread.gmane.org/gmane.comp.lang.agda/2911/focus=2917

db = h₁ ,′ h₂ ,′ h₃

postulate
  thm₂ : P → S
{-# ATP prove thm₂ db #-}
