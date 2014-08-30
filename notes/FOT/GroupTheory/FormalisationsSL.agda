------------------------------------------------------------------------------
-- Proving that two group theory formalisations are equivalents
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- We prove that group theory axioms based on the signature (G, ·, ε,)
-- (see for example [p. 39, 1]), i.e.

-- ∀ a b c. abc = a(bc)

-- ∀ a. εa = aε = a

-- ∀ a. ∃ a'. a'a = aa' = ε

-- are equivalents to the axioms based on the signature (G, ·, _⁻¹, ε,)
-- (see for example [2,3]), i.e.

-- ∀ a b c. abc = a(bc)

-- ∀ a. εa = aε  = a

-- ∀ a. a⁻¹a = aa⁻¹ = ε

-- [1] C. C. Chang and H. J. Keisler. Model Theory, volume 73 of Studies
--  in Logic and the Foundations of Mathematics. North-Holland, 3rd
--  edition, 3rd impression 1992.

-- [2] Agda standard library 0.6 (see Algebra/Structures.agda)

-- [3] Coq implementation
--     (http://coq.inria.fr/pylons/contribs/files/GroupTheory/v8.3/GroupTheory.g1.html)

module FOT.GroupTheory.FormalisationsSL where

open import Data.Product
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------------

-- NB. We only write the proof for the left-inverse property.

infixl 10 _·_ -- The symbol is '\cdot'.

postulate
  G   : Set        -- The universe
  ε   : G          -- The identity element.
  _·_ : G → G → G  -- The binary operation.

-- Left-inverse property based on the signature (G, ·, ε,).
leftInverse₁ : Set
leftInverse₁ = ∀ a → Σ G (λ a' → a' · a ≡ ε)

-- Left-inverse property based on the signature (G, ·, _⁻¹, ε,).
infix  11 _⁻¹

postulate  _⁻¹ : G → G -- The inverse function.

leftInverse₂ : Set
leftInverse₂ = ∀ a → a ⁻¹ · a ≡ ε

-- From the left-inverse property based on the signature (G, ·, _⁻¹, ε,)
-- to the one based on the signature (G, ·, ε,).
leftInverse₂₋₁ : leftInverse₂ → leftInverse₁
leftInverse₂₋₁ h a = (a ⁻¹) , (h a)

-- From the left-inverse property based on the signature (G, ·, ε,) to
-- the one based on the signature (G, ·, _⁻¹, ε,).
--
-- In this case we prove the existence of the inverse function.
leftInverse₁₋₂ : leftInverse₁ → Σ (G → G) (λ f → ∀ a → f a · a ≡ ε)
leftInverse₁₋₂ h = f , prf
  where
  f : G → G  --  The inverse function.
  f a = proj₁ (h a)

  prf : ∀ a → f a · a ≡ ε
  prf a = proj₂ (h a)
