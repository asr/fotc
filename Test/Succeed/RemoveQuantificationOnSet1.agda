module Test.Succeed.RemoveQuantificationOnSet1 where

data ⊥ : Set where

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

¬ : Set → Set
¬ A = A → ⊥

postulate
  D : Set
  _≡_ : D → D → Set
  a b : D

postulate
  a≠b : ¬ ( a ≡ b)
{-# ATP axiom a≠b #-}

foo : {A : Set} → a ≡ b → A
foo a≡b  = ⊥-elim prf
  where
    postulate
      -- The translation must remove the quantification on Set,
      -- i.e. the translation must be 'a = b → $false'.
      prf : ⊥
    {-# ATP prove prf #-}
