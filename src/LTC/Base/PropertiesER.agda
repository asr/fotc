------------------------------------------------------------------------------
-- PCF terms properties (using equational reasoning)
------------------------------------------------------------------------------

module LTC.Base.PropertiesER where

open import LTC.Base

open import Common.Relation.Binary.EqReasoning using ( _≡⟨_⟩_ ; _∎ ; begin_ )
open import Common.Relation.Binary.PropositionalEquality.PropertiesER
  using ( subst )

------------------------------------------------------------------------------

succInjective : {d e : D} → succ d ≡ succ e → d ≡ e
succInjective {d} {e} Sd≡Se =
  begin
    d              ≡⟨ sym (pred-S d) ⟩
    pred (succ d)  ≡⟨ subst (λ t → pred (succ d) ≡ pred t)
                            Sd≡Se
                            refl
                   ⟩
    pred (succ e)  ≡⟨ pred-S e ⟩
    e
  ∎

∷-injective : {x y xs ys : D} → x ∷ xs ≡ y ∷ ys → x ≡ y ∧ xs ≡ ys
∷-injective {x} {y} {xs} {ys} x∷xs≡y∷ys = x≡y , xs≡ys
  where
    x≡y : x ≡ y
    x≡y =
      begin
        x              ≡⟨ sym (head-∷ x xs) ⟩
        head (x ∷ xs)  ≡⟨ subst (λ t → head (x ∷ xs) ≡ head t)
                                x∷xs≡y∷ys
                                refl
                       ⟩
        head (y ∷ ys)  ≡⟨ head-∷ y ys ⟩
        y
      ∎

    xs≡ys : xs ≡ ys
    xs≡ys =
      begin
        xs             ≡⟨ sym (tail-∷ x xs) ⟩
        tail (x ∷ xs)  ≡⟨ subst (λ t → tail (x ∷ xs) ≡ tail t)
                                x∷xs≡y∷ys
                                refl
                       ⟩
        tail (y ∷ ys)  ≡⟨ tail-∷ y ys ⟩
        ys
      ∎
