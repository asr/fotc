------------------------------------------------------------------------------
-- Arithmetic properties (added for the Collatz function example)
------------------------------------------------------------------------------

module Draft.FOTC.Program.Collatz.Data.Nat.PropertiesI where

open import FOTC.Base

open import FOTC.Base.PropertiesI

open import FOTC.Data.Nat
open import FOTC.Data.Nat.PropertiesI
open import FOTC.Data.Nat.UnaryNumbers

open import Draft.FOTC.Program.Collatz.Data.Nat

open import FOTC.Relation.Binary.EqReasoning

------------------------------------------------------------------------------

^-N : ∀ {m n} → N m → N n → N (m ^ n)
^-N {m} Nm zN          = subst N (sym (^-0 m)) (sN zN)
^-N {m} Nm (sN {n} Nn) = subst N (sym (^-S m n)) (*-N Nm (^-N Nm Nn))

postulate
  2x/2≡x : ∀ {n} → N n → two * n / two ≡ n

2^[x+1]/2≡x : ∀ {n} → N n → (two ^ (succ n)) / two ≡ two ^ n
2^[x+1]/2≡x {n} Nn =
  begin
    two ^ (succ n) / two
      ≡⟨ subst (λ t → two ^ (succ n) / two ≡ t / two)
               (^-S two n)
               refl
      ⟩
    (two * two ^ n) / two
      ≡⟨ 2x/2≡x (^-N (sN (sN zN)) Nn) ⟩
    two ^ n
  ∎

2^x-Even : ∀ n → Even (two ^ (succ n))
2^x-Even n = two ^ n , ^-S two n

Sx≡2^0→x≡0 : ∀ {n} → N n → succ n ≡ two ^ zero → n ≡ zero
Sx≡2^0→x≡0 zN         _       = refl
Sx≡2^0→x≡0(sN {n} Nn) SSn≡2^0 =
  ⊥-elim (0≠S (sym (succInjective (trans SSn≡2^0 (^-0 (succ (succ zero)))))))
