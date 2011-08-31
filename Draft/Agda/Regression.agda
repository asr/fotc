-- From FOTC.Data.Nat.Induction.Acc.WellFoundedInductionI

module Regression where

infix 7 _≡_
infixr 4 _∨_

postulate
  D           : Set
  N           : D → Set
  _≡_ LT LE   : D → D → Set
  zero true   : D
  succ        : D → D
  _<_ _≤_     : D → D → D
  sym         : ∀ {x y} → x ≡ y → y ≡ x
  _∨_         : Set → Set → Set
  [_,_]       : ∀ {A B}{C : Set} → (A → C) → (B → C) → A ∨ B → C
  x≤y→x<y∨x≡y : ∀ {m n} → N m → N n → LE m n → LT m n ∨ m ≡ n

data Acc {T : D → Set}(_<_ : D → D → Set) : D → Set where
  acc : ∀ {x} → T x → (∀ {y} → T y → y < x → Acc {T} _<_ y) → Acc _<_ x

-- It is neccesary add {N} to Acc LT m to avoid the internal error

-- An internal error has occurred. Please report this as a bug.
-- Location of the error: src/full/Agda/TypeChecking/MetaVars.hs:584

-- It seems the regression was after the patch

-- Thu Aug 25 07:29:09 COT 2011  ulfn@chalmers.se
--   * shortcut instantiation of metas to avoid unnecessary unfolding

helper : ∀ {n m} → N n → N m → Acc LT m → LE n m → Acc LT n
helper {n} {m} Nn Nm (acc _ h) n≤m =
    [ (λ n<m → h Nn n<m)
    , (λ n≡m → helper₁ (sym n≡m) (acc Nm h))
    ] (x≤y→x<y∨x≡y Nn Nm n≤m)
    where
    postulate helper₁ : ∀ {a b} → a ≡ b → Acc LT a → Acc LT b
