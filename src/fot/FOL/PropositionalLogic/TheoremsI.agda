------------------------------------------------------------------------------
-- Propositional logic theorems
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOL.PropositionalLogic.TheoremsI where

-- The theorems below are valid on intuitionistic logic and with an
-- empty domain.
open import FOL.Base hiding ( D≢∅ ; pem )

------------------------------------------------------------------------------
-- Boolean laws

→-transposition : {P Q : Set} → (P → Q) → ¬ Q → ¬ P
→-transposition p→q ¬q p = ¬q (p→q p)

∧∨-dist : {P Q R : Set} → P ∧ (Q ∨ R) ↔ P ∧ Q ∨ P ∧ R
∧∨-dist {P} {Q} {R} = l→r , r→l
  where
  l→r : P ∧ (Q ∨ R) → P ∧ Q ∨ P ∧ R
  l→r (p , inj₁ q) = inj₁ (p , q)
  l→r (p , inj₂ r) = inj₂ (p , r)

  r→l : P ∧ Q ∨ P ∧ R → P ∧ (Q ∨ R)
  r→l (inj₁ (p , q)) = p , inj₁ q
  r→l (inj₂ (p , r)) = p , inj₂ r

∧∨-dist' : {P Q R : Set} → P ∧ (Q ∨ R) ⇔ P ∧ Q ∨ P ∧ R
∧∨-dist' {P} {Q} {R} = l⇒r , r⇒l
  where
  l→r : P ∧ (Q ∨ R) → P ∧ Q ∨ P ∧ R
  l→r (p , inj₁ q) = inj₁ (p , q)
  l→r (p , inj₂ r) = inj₂ (p , r)

  l⇒r : P ∧ (Q ∨ R) ⇒ P ∧ Q ∨ P ∧ R
  l⇒r = fun l→r

  r→l : P ∧ Q ∨ P ∧ R → P ∧ (Q ∨ R)
  r→l (inj₁ (p , q)) = p , inj₁ q
  r→l (inj₂ (p , r)) = p , inj₂ r

  -- TODO (21 February 2015). In r⇒l we needed parenthesis in the
  -- antecedent, but they aren't needed in r→l. That is, the fixity of
  -- _⇒_ should be the same than the fixity of _→_.
  r⇒l : (P ∧ Q ∨ P ∧ R) ⇒ P ∧ (Q ∨ R)
  r⇒l = fun r→l

DM : {P Q : Set} → ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q
DM {P} {Q} = l→r , r→l
  where
  l→r : ¬ (P ∨ Q) → ¬ P ∧ ¬ Q
  l→r h = (λ p → h (inj₁ p)) , (λ q → h (inj₂ q))

  r→l : ¬ P ∧ ¬ Q → ¬ (P ∨ Q)
  r→l (¬p , ¬q) p∨q = case ¬p ¬q p∨q

-- The principle of the excluded middle implies the double negation
-- elimination
pem→¬¬-elim : ∀ {P} → (P ∨ ¬ P) → ¬ ¬ P → P
pem→¬¬-elim (inj₁ p)  _ = p
pem→¬¬-elim (inj₂ ¬p) h = ⊥-elim (h ¬p)
