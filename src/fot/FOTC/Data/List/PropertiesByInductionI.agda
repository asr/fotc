------------------------------------------------------------------------------
--  Properties related with lists (using induction on the FOTC lists type)
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOTC.Data.List.PropertiesByInductionI where

open import Common.FOL.Relation.Binary.EqReasoning

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Base.List.PropertiesI
open import FOTC.Data.List
open import FOTC.Data.Nat.Type

------------------------------------------------------------------------------
-- Congruence properties

++-leftCong : ∀ {xs ys zs} → xs ≡ ys → xs ++ zs ≡ ys ++ zs
++-leftCong refl = refl

------------------------------------------------------------------------------
-- Totality properties

lengthList-N : ∀ {xs} → List xs → N (length xs)
lengthList-N = List-ind A A[] h
  where
  A : D → Set
  A ds = N (length ds)

  A[] : A []
  A[] = subst N (sym length-[]) nzero

  h : ∀ a {as} → A as → A (a ∷ as)
  h a {as} Aas = subst N (sym (length-∷ a as)) (nsucc Aas)

------------------------------------------------------------------------------

++-leftIdentity : ∀ xs → [] ++ xs ≡ xs
++-leftIdentity = ++-[]

++-assoc : ∀ {xs} → List xs → ∀ ys zs → (xs ++ ys) ++ zs ≡ xs ++ ys ++ zs
++-assoc Lxs ys zs = List-ind A A[] h Lxs
  where
  A : D → Set
  A as = (as ++ ys) ++ zs ≡ as ++ ys ++ zs

  A[] : A []
  A[] = ([] ++ ys) ++ zs ≡⟨ ++-leftCong (++-leftIdentity ys) ⟩
        ys ++ zs         ≡⟨ sym (++-leftIdentity (ys ++ zs)) ⟩
        [] ++ ys ++ zs   ∎

  h : ∀ a {as} → A as → A (a ∷ as)
  h a {as} Aas =
    ((a ∷ as) ++ ys) ++ zs ≡⟨ ++-leftCong (++-∷ a as ys) ⟩
    (a ∷ (as ++ ys)) ++ zs ≡⟨ ++-∷ a (as ++ ys) zs ⟩
    a ∷ ((as ++ ys) ++ zs) ≡⟨ ∷-rightCong Aas ⟩
    a ∷ (as ++ ys ++ zs)   ≡⟨ sym (++-∷ a as (ys ++ zs)) ⟩
    (a ∷ as) ++ ys ++ zs   ∎
