{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- If we could prove ifInjective then we could true ≡ false (see Dan
-- Licata example in
-- http://thread.gmane.org/gmane.comp.lang.agda/4511).

module FOTC.Base.Consistency.IfInjective where

open import FOTC.Base

------------------------------------------------------------------------------

postulate ifInjective : ∀ {b b' t t'} →
                        (if b then t else t') ≡ (if b' then t else t') → b ≡ b'
{-# ATP prove ifInjective #-}

true≡false : true ≡ false
true≡false = ifInjective {true} {false} {true} {true}
                         (trans (if-true true) (sym (if-false true)))
