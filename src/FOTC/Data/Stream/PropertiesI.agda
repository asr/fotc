------------------------------------------------------------------------------
-- Streams properties
------------------------------------------------------------------------------

module FOTC.Data.Stream.PropertiesI where

open import FOTC.Base
open import FOTC.Base.PropertiesI
open import FOTC.Data.Stream
open import FOTC.Data.Stream.Equality

-----------------------------------------------------------------------------

tailS : ∀ {x xs} → Stream (x ∷ xs) → Stream xs
tailS {x} {xs} h = subst Stream (sym (∧-proj₂ (∷-injective x∷xs≡e∷es))) Ses
  where
  unfold : ∃[ e ] ∃[ es ] Stream es ∧ x ∷ xs ≡ e ∷ es
  unfold = Stream-gfp₁ h

  e : D
  e = ∃-proj₁ unfold

  es : D
  es = ∃-proj₁ (∃-proj₂ unfold)

  Ses : Stream es
  Ses = ∧-proj₁ (∃-proj₂ (∃-proj₂ unfold))

  x∷xs≡e∷es : x ∷ xs ≡ e ∷ es
  x∷xs≡e∷es = ∧-proj₂ (∃-proj₂ (∃-proj₂ unfold))

≈→Stream : ∀ {xs ys} → xs ≈ ys → Stream xs ∧ Stream ys
≈→Stream {xs} {ys} xs≈ys = Stream-gfp₂ P₁ helper₁ (ys , xs≈ys)
                         , Stream-gfp₂ P₂ helper₂ (xs , xs≈ys)
  where
  P₁ : D → Set
  P₁ ws = ∃[ zs ] ws ≈ zs

  helper₁ : ∀ {ws} → P₁ ws →
            ∃[ w' ] ∃[ ws' ] P₁ ws' ∧ ws ≡ w' ∷ ws'
  helper₁ {ws} (zs , ws≈zs) = w' , ws' , (zs' , ws'≈zs') , ws≡w'∷ws'
    where
    unfold-≈ : ∃[ w' ] ∃[ ws' ] ∃[ zs' ]
               ws' ≈ zs' ∧ ws ≡ w' ∷ ws' ∧ zs ≡ w' ∷ zs'
    unfold-≈ = ≈-gfp₁ ws≈zs

    w' : D
    w' = ∃-proj₁ unfold-≈

    ws' : D
    ws' = ∃-proj₁ (∃-proj₂ unfold-≈)

    zs' : D
    zs' = ∃-proj₁ (∃-proj₂ (∃-proj₂ unfold-≈))

    ws'≈zs' : ws' ≈ zs'
    ws'≈zs' = ∧-proj₁ (∃-proj₂ (∃-proj₂ (∃-proj₂ unfold-≈)))

    ws≡w'∷ws' : ws ≡ w' ∷ ws'
    ws≡w'∷ws' = ∧-proj₁ (∧-proj₂ (∃-proj₂ (∃-proj₂ (∃-proj₂ unfold-≈))))

  P₂ : D → Set
  P₂ zs = ∃[ ws ] ws ≈ zs

  helper₂ : ∀ {zs} → P₂ zs → ∃[ z' ] ∃[ zs' ] P₂ zs' ∧ zs ≡ z' ∷ zs'
  helper₂   {zs} (ws , ws≈zs) = w' , zs' , (ws' , ws'≈zs') , zs≡w'∷zs'
    where
    unfold-≈ : ∃[ w' ] ∃[ ws' ] ∃[ zs' ]
               ws' ≈ zs' ∧ ws ≡ w' ∷ ws' ∧ zs ≡ w' ∷ zs'

    unfold-≈ = ≈-gfp₁ ws≈zs

    w' : D
    w' = ∃-proj₁ unfold-≈

    ws' : D
    ws' = ∃-proj₁ (∃-proj₂ unfold-≈)

    zs' : D
    zs' = ∃-proj₁ (∃-proj₂ (∃-proj₂ unfold-≈))

    ws'≈zs' : ws' ≈ zs'
    ws'≈zs' = ∧-proj₁ (∃-proj₂ (∃-proj₂ (∃-proj₂ unfold-≈)))

    zs≡w'∷zs' : zs ≡ w' ∷ zs'
    zs≡w'∷zs' = ∧-proj₂ (∧-proj₂ (∃-proj₂ (∃-proj₂ (∃-proj₂ unfold-≈))))
