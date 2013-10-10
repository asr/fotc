{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module LogicalFramework.AdequacyTheorems where

module Example5 where

  -- First-order logic with equality.
  open import Common.FOL.FOL-Eq public

  postulate
    A B C : Set
    f₁    : A → C
    f₂    : B → C

  g : (A → C) → (B → C) → A ∨ B → C
  g f₁ f₂ (inj₁ a) = f₁ a
  g f₁ f₂ (inj₂ b) = f₂ b

  g' : (A → C) → (B → C) → A ∨ B → C
  g' f₁ f₂ x = case f₁ f₂ x

module Example7 where

  -- First-order logic with equality.
  open import Common.FOL.FOL-Eq public

  postulate
    C  : D → D → Set
    d  : ∀ {a} → C a a

  g : ∀ {a b} → a ≡ b → C a b
  g refl = d

  g' : ∀ {a b} → a ≡ b → C a b
  g' {a} h = subst (λ x → C a x) h d

module Example10 where

  -- First-order logic with equality.
  open import Common.FOL.FOL-Eq public

  postulate
    A B C : Set
    f₁ : A → C
    f₂ : B → C

  f : A ∨ B → C
  f (inj₁ a) = f₁ a
  f (inj₂ b) = f₂ b

  f' : A ∨ B → C
  f' = case f₁ f₂

module Example20 where

  -- First-order logic with equality.
  open import Common.FOL.FOL-Eq public

  f : {A : D → Set}{t t' : D} → t ≡ t' → A t → A t'
  f {A} {t} {.t} refl At = d At
    where
    postulate d : A t → A t

  f' : {A : D → Set}{t t' : D} → t ≡ t' → A t → A t'
  f' {A} h At = subst A h At

module Example30 where

  -- First-order logic with equality.
  open import Common.FOL.FOL-Eq public

  postulate
    A B C E : Set
    f₁ : A → E
    f₂ : B → E
    f₃ : C → E

  g : (A ∨ B) ∨ C → E
  g (inj₁ (inj₁ a)) = f₁ a
  g (inj₁ (inj₂ b)) = f₂ b
  g (inj₂ c)        = f₃ c

  g' : (A ∨ B) ∨ C → E
  g' = case (case f₁ f₂) f₃

module Example40 where

  infixl 9  _+_ _+'_
  infix  7  _≡_

  data ℕ : Set where
    zero :     ℕ
    succ : ℕ → ℕ

  PA-ind : (A : ℕ → Set) → A zero → (∀ n → A n → A (succ n)) → ∀ n → A n
  PA-ind A A0 h zero     = A0
  PA-ind A A0 h (succ n) = h n (PA-ind A A0 h n)

  data _≡_ (x : ℕ) : ℕ → Set where
    refl : x ≡ x

  subst : (A : ℕ → Set) → ∀ {x y} → x ≡ y → A x → A y
  subst A refl Ax = Ax

  _+_ : ℕ → ℕ → ℕ
  zero   + n = n
  succ m + n = succ (m + n)

  _+'_ : ℕ → ℕ → ℕ
  m +' n = PA-ind (λ _ → ℕ) n (λ x y → succ y) m

  -- Properties using pattern matching.
  succCong : ∀ {m n} → m ≡ n → succ m ≡ succ n
  succCong refl = refl

  +-rightIdentity : ∀ n → n + zero ≡ n
  +-rightIdentity zero     = refl
  +-rightIdentity (succ n) = succCong (+-rightIdentity n)

  -- Properties using the basic inductive constants.
  succCong' : ∀ {m n} → m ≡ n → succ m ≡ succ n
  succCong' {m} h = subst (λ x → succ m ≡ succ x) h refl

  +'-leftIdentity : ∀ n → zero +' n ≡ n
  +'-leftIdentity n = refl

  +'-rightIdentity : ∀ n → n +' zero ≡ n
  +'-rightIdentity = PA-ind A A0 is
    where
    A : ℕ → Set
    A n = n +' zero ≡ n

    A0 : A zero
    A0 = refl

    is : ∀ n → A n → A (succ n)
    is n ih = succCong' ih

module Example50 where

  infixl 10 _*_
  infixl 9  _+_
  infix  7  _≡_

  data ℕ : Set where
    zero :     ℕ
    succ : ℕ → ℕ

  PA-ind : (A : ℕ → Set) → A zero → (∀ n → A n → A (succ n)) → ∀ n → A n
  PA-ind A A0 h zero     = A0
  PA-ind A A0 h (succ n) = h n (PA-ind A A0 h n)

  data _≡_ (x : ℕ) : ℕ → Set where
    refl : x ≡ x

  recℕ : {A : Set} → A → (ℕ → A → A) → ℕ → A
  recℕ {A} = PA-ind (λ _ → A)

  _+_ : ℕ → ℕ → ℕ
  m + n = recℕ n (λ _ x → succ x) m

  +-0x : ∀ n → zero + n ≡ n
  +-0x n = refl

  +-Sx : ∀ m n → succ m + n ≡ succ (m + n)
  +-Sx m n = refl

  _*_ : ℕ → ℕ → ℕ
  m * n = recℕ zero (λ _ x → n + x) m

  *-0x : ∀ n → zero * n ≡ zero
  *-0x n = refl

  *-Sx : ∀ m n → succ m * n ≡ n + m * n
  *-Sx m n = refl
