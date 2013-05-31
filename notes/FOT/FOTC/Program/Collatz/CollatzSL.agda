------------------------------------------------------------------------------
-- Reasoning about a function without a termination proof
------------------------------------------------------------------------------

{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --no-universe-polymorphism #-}
-- {-# OPTIONS --without-K #-}

module FOT.FOTC.Program.Collatz.CollatzSL where

open import Data.Bool
open import Data.Empty
open import Data.Nat renaming ( suc to succ )
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality hiding ( [_] )
open import Relation.Nullary

------------------------------------------------------------------------------

_^_ : ℕ → ℕ → ℕ
n ^ zero   = 1
m ^ succ n = m * (m ^ n)

isEven : ℕ → Bool
isEven 0               = true
isEven 1               = false
isEven (succ (succ n)) = isEven n

{-# NO_TERMINATION_CHECK #-}
collatz : ℕ → ℕ
collatz zero        = 1
collatz (succ zero) = 1
collatz n with isEven n
... | true  = collatz ⌊ n /2⌋
... | false = collatz (3 * n + 1)

-- TODO: 31 May 2013. Rejected when using the --without-K option. See
-- Agda issue 865.
xy≡0→x≡0∨y≡0 : (m n : ℕ) → m * n ≡ zero → m ≡ zero ⊎ n ≡ zero
xy≡0→x≡0∨y≡0 zero     n        h = inj₁ refl
xy≡0→x≡0∨y≡0 (succ m) zero     h = inj₂ refl
xy≡0→x≡0∨y≡0 (succ m) (succ n) ()

+∸2 : ∀ {n} → n ≢ zero → n ≢ 1 → n ≡ succ (succ (n ∸ 2))
+∸2 {zero}          0≢0 _   = ⊥-elim (0≢0 refl)
+∸2 {succ zero}     _   1≢1 = ⊥-elim (1≢1 refl)
+∸2 {succ (succ n)} _   _   = refl

2^x≢0 : (n : ℕ) → 2 ^ n ≢ zero
2^x≢0 zero ()
2^x≢0 (succ n) h = [ (λ ())
                   , (λ 2^n≡0 → ⊥-elim (2^x≢0 n 2^n≡0))
                   ]′ (xy≡0→x≡0∨y≡0 2 (2 ^ n) h)

2^[x+1]/2≡2^x : ∀ n → ⌊ 2 ^ succ n /2⌋ ≡ 2 ^ n
2^[x+1]/2≡2^x zero            = refl
2^[x+1]/2≡2^x (succ zero)     = refl
2^[x+1]/2≡2^x (succ (succ n)) = {!!}

collatz-2^x : ∀ n → Σ ℕ (λ k → n ≡ 2 ^ k) → collatz n ≡ 1
collatz-2^x zero     h                = refl
collatz-2^x (succ n) (zero , proj₂)   = subst (λ t → collatz t ≡ 1) (sym proj₂) refl
collatz-2^x (succ n) (succ k , proj₂) = subst (λ t → collatz t ≡ 1) (sym proj₂) {!!}

succInjective : ∀ {m n} → succ m ≡ succ n → m ≡ n
succInjective refl = refl

Sx≡x→⊥ : ∀ n → succ n ≢ n
Sx≡x→⊥ zero ()
Sx≡x→⊥ (succ n) h = ⊥-elim (Sx≡x→⊥ n (succInjective h))

2^[x+1]≢1 : ∀ n → 2 ^ (succ n) ≢ 1
2^[x+1]≢1 n h = Sx≡x→⊥ 1 (i*j≡1⇒i≡1 2 (2 ^ n) h)
