------------------------------------------------------------------------------
-- FOTC terms properties
------------------------------------------------------------------------------

module FOTC.Base.PropertiesI where

open import FOTC.Base

open import FOTC.Relation.Binary.EqReasoning

------------------------------------------------------------------------------

succInjective : ∀ {d e} → succ d ≡ succ e → d ≡ e
succInjective {d} {e} h =
  begin
    d              ≡⟨ sym (pred-S d) ⟩
    pred (succ d)  ≡⟨ cong pred h ⟩
    pred (succ e)  ≡⟨ pred-S e ⟩
    e
  ∎

∷-injective : ∀ {x y xs ys} → x ∷ xs ≡ y ∷ ys → x ≡ y ∧ xs ≡ ys
∷-injective {x} {y} {xs} {ys} h = x≡y , xs≡ys
  where
  x≡y : x ≡ y
  x≡y =
    begin
      x              ≡⟨ sym (head-∷ x xs) ⟩
      head (x ∷ xs)  ≡⟨ cong head h ⟩
      head (y ∷ ys)  ≡⟨ head-∷ y ys ⟩
      y
    ∎

  xs≡ys : xs ≡ ys
  xs≡ys =
    begin
      xs             ≡⟨ sym (tail-∷ x xs) ⟩
      tail (x ∷ xs)  ≡⟨ cong tail h ⟩
      tail (y ∷ ys)  ≡⟨ tail-∷ y ys ⟩
      ys
    ∎
