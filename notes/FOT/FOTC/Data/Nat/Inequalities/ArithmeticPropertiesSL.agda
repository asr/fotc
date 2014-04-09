------------------------------------------------------------------------------
-- Testing normalisation on arithmetic properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.FOTC.Data.Nat.Inequalities.ArithmeticPropertiesSL where

module NonPrimitives where

  open import Data.Nat
  open import Relation.Binary.PropositionalEquality

  101≡100+11∸10 : 101 ≡ 100 + 11 ∸ 10
  101≡100+11∸10 = refl

  91≡100+11∸10∸10 : 91 ≡ 100 + 11 ∸ 10 ∸ 10
  91≡100+11∸10∸10 = refl

  -- Agsy failed using a timeout of 5 minutes and it succeed with a
  -- timeout of 10 minutes.
  100+11>100 : 100 + 11 > 100
  100+11>100 = s≤s
               (s≤s
                (s≤s
                 (s≤s
                  (s≤s
                   (s≤s
                    (s≤s
                     (s≤s
                      (s≤s
                       (s≤s
                        (s≤s
                         (s≤s
                          (s≤s
                           (s≤s
                            (s≤s
                             (s≤s
                              (s≤s
                               (s≤s
                                (s≤s
                                 (s≤s
                                  (s≤s
                                   (s≤s
                                    (s≤s
                                     (s≤s
                                      (s≤s
                                       (s≤s
                                        (s≤s
                                         (s≤s
                                          (s≤s
                                           (s≤s
                                            (s≤s
                                             (s≤s
                                              (s≤s
                                               (s≤s
                                                (s≤s
                                                 (s≤s
                                                  (s≤s
                                                   (s≤s
                                                    (s≤s
                                                     (s≤s
                                                      (s≤s
                                                       (s≤s
                                                        (s≤s
                                                         (s≤s
                                                          (s≤s
                                                           (s≤s
                                                            (s≤s
                                                             (s≤s
                                                              (s≤s
                                                               (s≤s
                                                                (s≤s
                                                                 (s≤s
                                                                  (s≤s
                                                                   (s≤s
                                                                    (s≤s
                                                                     (s≤s
                                                                      (s≤s
                                                                       (s≤s
                                                                        (s≤s
                                                                         (s≤s
                                                                          (s≤s
                                                                           (s≤s
                                                                            (s≤s
                                                                             (s≤s
                                                                              (s≤s
                                                                               (s≤s
                                                                                (s≤s
                                                                                 (s≤s
                                                                                  (s≤s
                                                                                   (s≤s
                                                                                    (s≤s
                                                                                     (s≤s
                                                                                      (s≤s
                                                                                       (s≤s
                                                                                        (s≤s
                                                                                         (s≤s
                                                                                          (s≤s
                                                                                           (s≤s
                                                                                            (s≤s
                                                                                             (s≤s
                                                                                              (s≤s
                                                                                               (s≤s
                                                                                                (s≤s
                                                                                                 (s≤s
                                                                                                  (s≤s
                                                                                                   (s≤s
                                                                                                    (s≤s
                                                                                                     (s≤s
                                                                                                      (s≤s
                                                                                                       (s≤s
                                                                                                        (s≤s
                                                                                                         (s≤s
                                                                                                          (s≤s
                                                                                                           (s≤s
                                                                                                            (s≤s
                                                                                                             (s≤s
                                                                                                              (s≤s
                                                                                                               (s≤s
                                                                                                                (s≤s
                                                                                                                 (s≤s
                                                                                                                  (s≤s
                                                                                                                   z≤n))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

module Primitives where

  open import Data.Bool
  open import Data.Nat hiding ( _<_ )
  open import Relation.Binary.PropositionalEquality

  primitive primNatLess : ℕ → ℕ → Bool

  _<_ : ℕ → ℕ → Bool
  _<_ = primNatLess

  100<100+11 : 100 < (100 + 11) ≡ true
  100<100+11 = refl
