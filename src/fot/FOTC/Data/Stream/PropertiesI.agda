------------------------------------------------------------------------------
-- Streams properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Stream.PropertiesI where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Base.List.PropertiesI
open import FOTC.Data.Conat
open import FOTC.Data.Conat.Equality.Type
open import FOTC.Data.Colist
open import FOTC.Data.Colist.PropertiesI
open import FOTC.Data.List
open import FOTC.Data.List.PropertiesI
open import FOTC.Data.Stream.Type

-----------------------------------------------------------------------------
-- Because a greatest post-fixed point is a fixed-point, then the
-- Stream predicate is also a pre-fixed point of the functional
-- StreamF, i.e.
--
-- StreamF Stream ≤ Stream (see FOTC.Data.Stream.Type).
Stream-pre-fixed : ∀ {xs} →
                   ∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ Stream xs' →
                   Stream xs
Stream-pre-fixed h = Stream-coind A h' h
  where
  A : D → Set
  A xs = ∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ Stream xs'

  h' : ∀ {xs} → A xs → ∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ A xs'
  h' (x' , xs' , prf , Sxs') = x' , xs' , prf , Stream-unf Sxs'

∷-Stream : ∀ {x xs} → Stream (x ∷ xs) → Stream xs
∷-Stream h with Stream-unf h
... | x' , xs' , prf , Sxs' =
  subst Stream (sym (∧-proj₂ (∷-injective prf))) Sxs'

Stream→Colist : ∀ {xs} → Stream xs → Colist xs
Stream→Colist {xs} Sxs = Colist-coind A h₁ h₂
  where
  A : D → Set
  A ys = Stream ys

  h₁ : ∀ {xs} → A xs → xs ≡ [] ∨ (∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ A xs')
  h₁ Axs with Stream-unf Axs
  ... | x' , xs' , prf , Sxs' = inj₂ (x' , xs' , prf , Sxs')

  h₂ : A xs
  h₂ = Sxs

++-Stream : ∀ {xs ys} → Colist xs → Stream ys → Stream (xs ++ ys)
++-Stream {xs} {ys} CLxs Sys with Colist-unf CLxs
... | inj₁ prf = subst Stream (sym prf₁) Sys
 where
 prf₁ : xs ++ ys ≡ ys
 prf₁ = trans (++-leftCong prf) (++-[] ys)

... | inj₂ (x' , xs' , prf , CLxs') = subst Stream (sym prf₁) prf₂
   where
   prf₁ : xs ++ ys ≡ x' ∷ (xs' ++ ys)
   prf₁ = trans (++-leftCong prf) (++-∷ x' xs' ys)

   -- TODO (15 December 2013): Why the termination checker accepts the
   -- recursive called ++-Stream_CLxs'_Sys?
   prf₂ : Stream (x' ∷ xs' ++ ys)
   prf₂ = Stream-pre-fixed (x' , (xs' ++ ys) , refl , ++-Stream CLxs' Sys)

-- Adapted from (Sander 1992, p. 59).
streamLength : ∀ {xs} → Stream xs → length xs ≈N ∞
streamLength {xs} Sxs = ≈N-coind R h₁ h₂
  where
  R : D → D → Set
  R m n = ∃[ xs ] Stream xs ∧ m ≡ length xs ∧ n ≡ ∞

  h₁ : ∀ {m n} → R m n →
       m ≡ zero ∧ n ≡ zero
         ∨ (∃[ m' ] ∃[ n' ] m ≡ succ₁ m' ∧ n ≡ succ₁ n' ∧ R m' n')
  h₁ {m} (xs , Sxs , m=lxs , n≡∞) with Stream-unf Sxs
  ... | x' , xs' , xs≡x'∷xs' , Sxs' =
    inj₂ (length xs' , ∞ , helper , trans n≡∞ ∞-eq , (xs' , Sxs' , refl , refl))
    where
    helper : m ≡ succ₁ (length xs')
    helper = trans m=lxs (trans (lengthCong xs≡x'∷xs') (length-∷ x' xs'))

  h₂ : R (length xs) ∞
  h₂ = xs , Sxs , refl , refl

------------------------------------------------------------------------------
-- References
--
-- Sander, Herbert P. (1992). A Logic of Functional Programs with an
-- Application to Concurrency. PhD thesis. Department of Computer
-- Sciences: Chalmers University of Technology and University of
-- Gothenburg.
