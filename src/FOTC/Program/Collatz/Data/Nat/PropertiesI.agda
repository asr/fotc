------------------------------------------------------------------------------
-- Arithmetic properties (added for the Collatz function example)
------------------------------------------------------------------------------

module FOTC.Program.Collatz.Data.Nat.PropertiesI where

open import FOTC.Base

open import FOTC.Base.PropertiesI

open import FOTC.Data.Nat
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.PropertiesI
open import FOTC.Data.Nat.PropertiesI
open import FOTC.Data.Nat.UnaryNumbers
open import FOTC.Data.Nat.UnaryNumbers.IsN-I

open import FOTC.Program.Collatz.Data.Nat

open import FOTC.Relation.Binary.EqReasoning

------------------------------------------------------------------------------

^-N : ∀ {m n} → N m → N n → N (m ^ n)
^-N {m} Nm zN          = subst N (sym (^-0 m)) (sN zN)
^-N {m} Nm (sN {n} Nn) = subst N (sym (^-S m n)) (*-N Nm (^-N Nm Nn))

2x/2≡x : ∀ {n} → N n → two * n / two ≡ n
2x/2≡x zN = prf
  where
    -- See the combined proof.
    postulate prf : two * zero / two ≡ zero

2x/2≡x (sN zN) =
  begin
    (two * succ zero) / two
      ≡⟨ cong₂ _/_ (*-rightIdentity 2-N) refl ⟩
    two / two
      ≡⟨ /-x≥y (x≥x 2-N) ⟩
    succ ((two ∸ two) / two)
      ≡⟨ cong succ (cong₂ _/_ (x∸x≡0 2-N) refl) ⟩
    succ (zero / two)
      ≡⟨ cong succ (/-x<y (<-0S (succ zero))) ⟩
    succ zero
  ∎

2x/2≡x (sN (sN {n} Nn)) = prf
  where
    -- See the combined proof.
    postulate prf : two * succ (succ n) / two ≡ succ (succ n)

2^[x+1]/2≡x : ∀ {n} → N n → (two ^ (succ n)) / two ≡ two ^ n
2^[x+1]/2≡x {n} Nn =
  begin
    two ^ (succ n) / two
      ≡⟨ subst (λ t → two ^ (succ n) / two ≡ t / two)
               (^-S two n)
               refl
      ⟩
    (two * two ^ n) / two
      ≡⟨ 2x/2≡x (^-N 2-N Nn) ⟩
    two ^ n
  ∎

2^x-Even : ∀ n → Even (two ^ (succ n))
2^x-Even n = two ^ n , ^-S two n

Sx≡2^0→x≡0 : ∀ {n} → N n → succ n ≡ two ^ zero → n ≡ zero
Sx≡2^0→x≡0 zN         _       = refl
Sx≡2^0→x≡0(sN {n} Nn) SSn≡2^0 =
  ⊥-elim (0≠S (sym (succInjective (trans SSn≡2^0 (^-0 two)))))
