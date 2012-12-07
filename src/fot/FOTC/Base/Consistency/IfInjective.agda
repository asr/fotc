{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- If we could prove ifInjective then we could true ≡ false (see Dan
-- Licata example in
-- http://thread.gmane.org/gmane.comp.lang.agda/4511).

module FOTC.Base.Consistency.IfInjective where

open import FOTC.Base

------------------------------------------------------------------------------

postulate ifInjective : ∀ {b₁ b₂ d₁ d₂ } →
                        if b₁ then d₁ else d₂ ≡ if b₂ then d₁ else d₂ → b₁ ≡ b₂
{-# ATP prove ifInjective #-}

true≡false : true ≡ false
true≡false = ifInjective {true} {false} {true} {true}
                         (trans (if-true true) (sym (if-false true)))
