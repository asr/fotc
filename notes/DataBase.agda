{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- Nils' idea about databases in the Agda mailing list.
-- http://thread.gmane.org/gmane.comp.lang.agda/2911/focus=2917

module DataBase where

infixr 7 _,_ _,′_
infixr 5 _∧_

data _∧_ (A B : Set) : Set where
  _,_ : A → B → A ∧ B

_,′_ : ∀ {A B} → A → B → A ∧ B
_,′_ = _,_

postulate
  P Q R S : Set
  h₁      : P → Q
  h₂      : Q → R
  h₃      : R → S

postulate thm₁ : P → S
{-# ATP prove thm₁ h₁ h₂ h₃ #-}

db = h₁ ,′ h₂ ,′ h₃

postulate thm₂ : P → S
{-# ATP prove thm₂ db #-}
