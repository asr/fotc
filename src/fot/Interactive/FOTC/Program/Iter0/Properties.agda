------------------------------------------------------------------------------
-- Some properties of the function iter₀
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.FOTC.Program.Iter0.Properties where

open import Common.FOL.Relation.Binary.EqReasoning

open import Interactive.FOTC.Base
open import Interactive.FOTC.Base.Properties
open import Interactive.FOTC.Base.List
open import Interactive.FOTC.Data.List.Properties
open import Interactive.FOTC.Data.Nat.Type
open import Interactive.FOTC.Data.Nat.List.Type
open import Interactive.FOTC.Program.Iter0.Iter0

------------------------------------------------------------------------------

iter₀-0 : ∀ f → iter₀ f zero ≡ []
iter₀-0 f =
  iter₀ f zero
    ≡⟨ iter₀-eq f zero ⟩
  (if (iszero₁ zero) then [] else (zero ∷ iter₀ f (f · zero)))
    ≡⟨ ifCong₁ iszero-0 ⟩
  (if true then [] else (zero ∷ iter₀ f (f · zero)))
    ≡⟨ if-true [] ⟩
  [] ∎
