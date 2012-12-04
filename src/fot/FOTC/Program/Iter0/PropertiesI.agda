------------------------------------------------------------------------------
-- Some properties of the function iter₀
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.Iter0.PropertiesI where

open import Common.FOL.Relation.Binary.EqReasoning

open import FOTC.Base
open import FOTC.Base.PropertiesI
open import FOTC.Base.List
open import FOTC.Data.List.PropertiesI
open import FOTC.Data.Nat.Type
open import FOTC.Data.Nat.List.Type
open import FOTC.Program.Iter0.Iter0

------------------------------------------------------------------------------

iter₀-0 : ∀ f → iter₀ f zero ≡ []
iter₀-0 f =
  iter₀ f zero
    ≡⟨ iter₀-eq f zero ⟩
  if (iszero₁ zero) then [] else (zero ∷ iter₀ f (f · zero))
    ≡⟨ ifCong₁ iszero-0 ⟩
  if true then [] else (zero ∷ iter₀ f (f · zero))
    ≡⟨ if-true [] ⟩
  [] ∎
