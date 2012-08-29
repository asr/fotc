{-# LANGUAGE UnicodeSyntax #-}

-- The definition of rec in LTC-PCF requires a fixed-point operator of
-- type
--
-- fix : ((D → D) → D → D) → D → D
--
-- instead of
--
-- fix : (D → D) → D.

data Nat = Zero | Succ Nat
         deriving Eq

type T = Nat → Nat → (Nat → Nat → Nat) → Nat

rec ∷ T
rec Zero     a _ = a
rec (Succ n) a f = f n (rec n a f)

rec₁ ∷ T
rec₁ = \n a f → if n == Zero
                then a
                else f n (rec n a f)

fix₁ ∷ (T → T) → T
fix₁ f = f (fix₁ f)

-- Doesn't work!
fix₂ ∷ (Nat → Nat) → Nat
fix₂ f = f (fix₂ f)

rech ∷ T → T
rech r = \n a f → if n == Zero
                  then a
                  else f n (r n a f)

rec₂ ∷ T
rec₂ n a f = (fix₁ rech) n a f
