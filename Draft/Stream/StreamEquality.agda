module StreamEquality where

open import Coinduction
open import Relation.Binary.PropositionalEquality

data Stream (A : Set) : Set where
 consS : (x : A)(xs : ∞ (Stream A)) → Stream A

data _≈_ {A} : (xs ys : Stream A) → Set where
  _∷_ : (x : A){xs ys : Stream A} → xs ≈ ys → consS x (♯ xs) ≈ consS x (♯ ys)

≡-Stream : {A : Set}(x : A)(xs ys : ∞ (Stream A)) → xs ≡ ys →
           consS x xs ≡ consS x ys
≡-Stream y .ys ys refl = refl

-- -≈-≡ : {A : Set} → (xs ys : Stream A) → xs ≈ ys → xs ≡ ys
-- -≈-≡ (consS .x' .♯ x')) (consS x' .(.StreamEquality.♯-1 x')) (.x' ∷ y) = ?
-- --  ≡-Stream x xs ys {!-≈-≡ (♭ xs) (♭ ys) ?!}

-- foo : {A : Set} → (xs ys : ∞ (Stream A)) → ∞ (♭ xs ≈ ♭ ys) → xs ≡ ys
-- foo xs ys xxx with ♭ xxx
-- ... | aaa = {!-≈-≡ ? ? aaa!}
