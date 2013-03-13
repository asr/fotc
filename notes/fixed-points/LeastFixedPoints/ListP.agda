------------------------------------------------------------------------------
-- From ListP as the least fixed-point to ListP using data
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- We want to represent the polymorphic total lists data type
--
-- data ListP (A : D → Set) : D → Set where
--   lnil  : ListP A []
--   lcons : ∀ {x xs} → A x → ListP A xs → ListP A (x ∷ xs)
--
-- using the representation of ListP as the least fixed-point.

module LeastFixedPoints.ListP where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.Nat.Type
open import FOTC.Data.Nat.UnaryNumbers

------------------------------------------------------------------------------
-- ListP is a least fixed-point of a functor

-- The functor.
-- ListPF : (D → Set) → (D → Set) → D → Set
-- ListPF A B xs = xs ≡ [] ∨ (∃[ x' ] ∃[ xs' ] A x' ∧ xs ≡ x' ∷ xs' ∧ B xs' )

-- ListP is the least fixed-point of ListPF.
postulate
  ListP : (D → Set) → D → Set

  -- ListP is a pre-fixed point of ListPF.
  --
  -- Peter: It corresponds to the introduction rules.
  ListP-in :
    (A : D → Set) →
    ∀ {xs} → xs ≡ [] ∨ (∃[ x' ] ∃[ xs' ] A x' ∧ xs ≡ x' ∷ xs' ∧ ListP A xs') →
    ListP A xs

  -- ListP is the least pre-fixed point of ListPF.
  --
  -- Peter: It corresponds to the elimination rule of an inductively
  -- defined predicate.
  ListP-ind :
    (A B : D → Set) →
    (∀ {xs} → xs ≡ [] ∨ (∃[ x' ] ∃[ xs' ] A x' ∧ xs ≡ x' ∷ xs' ∧ B xs') → B xs) →
    ∀ {xs} → ListP A xs → B xs

------------------------------------------------------------------------------
-- The data constructors of ListP.
lnil  : (A : D → Set) → ListP A []
lnil A = ListP-in A (inj₁ refl)

lcons : (A : D → Set) → ∀ {x xs} → A x → ListP A xs → ListP A (x ∷ xs)
lcons A {n} {ns} An LPns = ListP-in A (inj₂ (n , ns , An , refl , LPns))

------------------------------------------------------------------------------
-- The induction principle for ListP.
indListP : (A B : D → Set) →
           B [] →
           (∀ x {xs} → A x → B xs → B (x ∷ xs)) →
           ∀ {xs} → ListP A xs → B xs
indListP A B B[] is = ListP-ind A B prf
  where
  prf : ∀ {xs} →
        xs ≡ [] ∨ (∃[ x' ] ∃[ xs' ] A x' ∧ xs ≡ x' ∷ xs' ∧ B xs') →
        B xs
  prf (inj₁ xs≡[])                        = subst B (sym xs≡[]) B[]
  prf (inj₂ (x' , xs' , Ax' , h₁ , Bxs')) = subst B (sym h₁) (is x' Ax' Bxs')

------------------------------------------------------------------------------
-- Examples

-- "Heterogeneous" total lists
xs : D
xs = [0] ∷ true ∷ [1] ∷ false ∷ []

List : D → Set
List = ListP (λ d → d ≡ d)

xs-ListP : List xs
xs-ListP =
  lcons A refl (lcons A refl (lcons A refl (lcons A refl (lnil A))))
  where
  A : D → Set
  A d = d ≡ d

-- Total lists of total natural numbers
ys : D
ys = [0] ∷ [1] ∷ [2] ∷ []

ListN : D → Set
ListN = ListP N

ys-ListP : ListN ys
ys-ListP =
  lcons N nzero (lcons N (nsucc nzero) (lcons N (nsucc (nsucc nzero)) (lnil N)))
