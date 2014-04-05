------------------------------------------------------------------------------
-- Testing normalisation on arithmetic properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.FOTC.Data.Nat.Inequalities.ArithmeticPropertiesSL where

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
