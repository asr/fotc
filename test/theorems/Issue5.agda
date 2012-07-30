{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Issue5 where

postulate
  D   : Set
  _≡_ : D → D → Set
  p   : ∀ d e → d ≡ e

-- The ATPs only try to prove the last ATP pragma.
postulate foo : ∀ d e → d ≡ e
{-# ATP prove foo #-}
{-# ATP prove foo p #-}
