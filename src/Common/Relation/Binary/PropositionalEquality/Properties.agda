------------------------------------------------------------------------------
-- Propositional equality properties
------------------------------------------------------------------------------

module Common.Relation.Binary.PropositionalEquality.Properties where

open import Common.Relation.Binary.PropositionalEquality using ( _≡_ ; refl )
open import Common.Universe using ( D )

------------------------------------------------------------------------------
-- Identity properties

sym : {x y : D} → x ≡ y → y ≡ x
sym refl = refl

trans : {x y z : D} → x ≡ y → y ≡ z → x ≡ z
trans refl y≡z = y≡z

-- The substitution is defined in
-- Common.Relation.Binary.PropositionalEquality.PropertiesER
