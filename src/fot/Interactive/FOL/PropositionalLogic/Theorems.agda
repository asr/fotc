------------------------------------------------------------------------------
-- Propositional logic theorems
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.FOL.PropositionalLogic.Theorems where

-- The theorems below are valid on intuitionistic logic and with an
-- empty domain.
open import Interactive.FOL.Base hiding ( D≢∅ ; pem )

------------------------------------------------------------------------------
-- Variables

variable
  P Q R : Set

------------------------------------------------------------------------------
-- Boolean laws

¬¬-in : P → ¬ ¬ P
¬¬-in p ¬p = ¬p p

→-transposition : (P → Q) → ¬ Q → ¬ P
→-transposition p→q ¬q p = ¬q (p→q p)

∧∨-dist : P ∧ (Q ∨ R) ↔ P ∧ Q ∨ P ∧ R
∧∨-dist = l→r , r→l
  where
  l→r : P ∧ (Q ∨ R) → P ∧ Q ∨ P ∧ R
  l→r (p , inj₁ q) = inj₁ (p , q)
  l→r (p , inj₂ r) = inj₂ (p , r)

  r→l : P ∧ Q ∨ P ∧ R → P ∧ (Q ∨ R)
  r→l (inj₁ (p , q)) = p , inj₁ q
  r→l (inj₂ (p , r)) = p , inj₂ r

∧∨-dist' : P ∧ (Q ∨ R) ⇔ P ∧ Q ∨ P ∧ R
∧∨-dist' = l⇒r , r⇒l
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

dm : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q
dm = l→r , r→l
  where
  l→r : ¬ (P ∨ Q) → ¬ P ∧ ¬ Q
  l→r h = (λ p → h (inj₁ p)) , (λ q → h (inj₂ q))

  r→l : ¬ P ∧ ¬ Q → ¬ (P ∨ Q)
  r→l (¬p , ¬q) p∨q = case ¬p ¬q p∨q

------------------------------------------------------------------------------
-- The following principles are equivalents:
--
-- PEM: Principle of the excluded middle
-- DNE: Double negation elimination
-- RAA: Reductio ab absurdum rule (proof by contradiction)

pem : Set → Set
pem A = A ∨ ¬ A

dne : Set → Set
dne A = ¬ ¬ A → A

raa : Set → Set
raa A = (¬ A → ⊥) → A

-- PEM → DNE.
pem→dne : pem P → dne P
pem→dne (inj₁ p)  _ = p
pem→dne (inj₂ ¬p) h = ⊥-elim (h ¬p)

-- PEM → RAA.
pem→raa : pem P → raa P
pem→raa pemI h = case (λ p → p) (λ ¬p → ⊥-elim (h ¬p)) pemI

-- DNE → RAA.
dne→raa : dne P → raa P
dne→raa dneI = dneI

-- RAA → PEM.
raa→pem : raa (P ∨ ¬ P) → pem P
raa→pem raaI = raaI (λ h → h (inj₂ λ p → h (inj₁ p)))
