------------------------------------------------------------------------------
-- Propositional equality properties
-- (they are not required when the ATPs are used)
------------------------------------------------------------------------------

module Common.Relation.Binary.PropositionalEquality.PropertiesER where

open import Common.Relation.Binary.PropositionalEquality using ( _≡_ ; refl )
open import Common.Universe using ( D )

------------------------------------------------------------------------------
-- Identity properties

subst : (P : D → Set){x y : D} → x ≡ y → P x → P y
subst P refl px = px
