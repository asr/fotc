------------------------------------------------------------------------------
-- The booleans properties
------------------------------------------------------------------------------

module FOTC.Data.Bool.PropertiesATP where

open import FOTC.Base

open import Common.Function using ( _$_ )

open import FOTC.Data.Bool
  using ( _&&_ ; &&-ff ; &&-ft ; &&-tf ; &&-tt
        ; Bool ; fB ; tB  -- The FOTC booleans type.
        )
open import FOTC.Data.Nat.Inequalities using ( _≤_ )
open import FOTC.Data.Nat.Inequalities.PropertiesATP using ( Sx≰0 )
open import FOTC.Data.Nat.Type
  using ( N ; sN ; zN  -- The FOTC natural numbers type.
        )

------------------------------------------------------------------------------
-- Basic properties

&&-Bool : ∀ {b₁ b₂} → Bool b₁ → Bool b₂ → Bool (b₁ && b₂)
&&-Bool tB tB = prf
  where postulate prf : Bool (true && true)
        {-# ATP prove prf #-}
&&-Bool tB fB = prf
  where postulate prf : Bool (true && false)
        {-# ATP prove prf #-}
&&-Bool fB tB = prf
  where postulate prf : Bool (false && true)
        {-# ATP prove prf #-}
&&-Bool fB fB = prf
  where postulate prf : Bool (false && false)
        {-# ATP prove prf #-}

&&-comm : ∀ {b₁ b₂} → Bool b₁ → Bool b₂ → b₁ && b₂ ≡ b₂ && b₁
&&-comm tB tB = refl
&&-comm tB fB = trans &&-tf (sym &&-ft)
&&-comm fB tB = trans &&-ft (sym &&-tf)
&&-comm fB fB = refl

x&&false≡false : ∀ {b} → Bool b → b && false ≡ false
x&&false≡false tB = &&-tf
x&&false≡false fB = &&-ff

false&&x≡false : ∀ {b} → Bool b → false && b ≡ false
false&&x≡false tB = &&-ft
false&&x≡false fB = &&-ff

true&&x≡x : ∀ {b} → Bool b → true && b ≡ b
true&&x≡x tB = &&-tt
true&&x≡x fB = &&-tf

&&-assoc : ∀ {b₁ b₂ b₃} → Bool b₁ → Bool b₂ → Bool b₃ →
           (b₁ && b₂) && b₃ ≡ b₁ && b₂ && b₃
&&-assoc tB tB tB = prf
  where postulate prf : (true && true) && true ≡ true && true && true
        {-# ATP prove prf #-}
&&-assoc tB tB fB = prf
  where postulate prf : (true && true) && false ≡ true && true && false
        {-# ATP prove prf #-}
&&-assoc tB fB tB = prf
  where postulate prf : (true && false) && true ≡ true && false && true
        {-# ATP prove prf #-}
&&-assoc tB fB fB = prf
  where postulate prf : (true && false) && false ≡ true && false && false
        {-# ATP prove prf #-}
&&-assoc fB tB tB = prf
  where postulate prf : (false && true) && true ≡ false && true && true
        {-# ATP prove prf #-}
&&-assoc fB tB fB = prf
  where postulate prf : (false && true) && false ≡ false && true && false
        {-# ATP prove prf #-}
&&-assoc fB fB tB = prf
  where postulate prf : (false && false) && true ≡ false && false && true
        {-# ATP prove prf #-}
&&-assoc fB fB fB = prf
  where postulate prf : (false && false) && false ≡ false && false && false
        {-# ATP prove prf #-}

&&-proj₁ : ∀ {b₁ b₂} → Bool b₁ → Bool b₂ → b₁ && b₂ ≡ true → b₁ ≡ true
&&-proj₁ tB _ _    = refl
&&-proj₁ fB tB h = ⊥-elim $ true≠false $ trans (sym h) &&-ft
&&-proj₁ fB fB h = ⊥-elim $ true≠false $ trans (sym h) &&-ff

&&-proj₂ : ∀ {b₁ b₂} → Bool b₁ → Bool b₂ → b₁ && b₂ ≡ true → b₂ ≡ true
&&-proj₂ _  tB _   = refl
&&-proj₂ tB fB h = ⊥-elim $ true≠false $ trans (sym h) &&-tf
&&-proj₂ fB fB h = ⊥-elim $ true≠false $ trans (sym h) &&-ff

&&₃-proj₁ : ∀ {b₁ b₂ b₃ b₄} →
            Bool b₁ → Bool b₂ → Bool b₃ → Bool b₄ →
            b₁ && b₂ && b₃ && b₄ ≡ true →
            b₁ ≡ true
&&₃-proj₁ tB _ _ _ _ = refl
&&₃-proj₁ fB _ _ _ _ = ⊥-elim prf
  where postulate prf : ⊥
        {-# ATP prove prf &&-Bool false&&x≡false #-}

&&₃-proj₂ : ∀ {b₁ b₂ b₃ b₄} →
            Bool b₁ → Bool b₂ → Bool b₃ → Bool b₄ →
            b₁ && b₂ && b₃ && b₄ ≡ true →
            b₂ ≡ true
&&₃-proj₂ _ tB _ _ _ = refl
&&₃-proj₂ _ fB _ _ _ = ⊥-elim prf
  where postulate prf : ⊥
        {-# ATP prove prf &&-Bool false&&x≡false x&&false≡false #-}

&&₃-proj₃ : ∀ {b₁ b₂ b₃ b₄} →
            Bool b₁ → Bool b₂ → Bool b₃ → Bool b₄ →
            b₁ && b₂ && b₃ && b₄ ≡ true →
            b₃ ≡ true
&&₃-proj₃ _ _ tB _ _ = refl
&&₃-proj₃ _ _ fB _ _ = ⊥-elim prf
  where postulate prf : ⊥
        {-# ATP prove prf x&&false≡false false&&x≡false #-}

&&₃-proj₄ : ∀ {b₁ b₂ b₃ b₄} →
            Bool b₁ → Bool b₂ → Bool b₃ → Bool b₄ →
            b₁ && b₂ && b₃ && b₄ ≡ true →
            b₄ ≡ true
&&₃-proj₄ _ _ _ tB _ = refl
&&₃-proj₄ _ _ _ fB _ = ⊥-elim prf
  where postulate prf : ⊥
        {-# ATP prove prf x&&false≡false #-}

------------------------------------------------------------------------------
-- Properties with inequalities

≤-Bool : ∀ {m n} → N m → N n → Bool (m ≤ n)
≤-Bool {n = n} zN Nn = prf
  where postulate prf : Bool (zero ≤ n)
        {-# ATP prove prf #-}
≤-Bool (sN {m} Nm) zN = prf
  where postulate prf : Bool (succ m ≤ zero)
        {-# ATP prove prf Sx≰0 #-}
≤-Bool (sN {m} Nm) (sN {n} Nn) = prf $ ≤-Bool Nm Nn
  where postulate prf : Bool (m ≤ n) → Bool (succ m ≤ succ n)
        {-# ATP prove prf #-}
