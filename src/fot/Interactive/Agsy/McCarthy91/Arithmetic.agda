------------------------------------------------------------------------------
-- Testing Agsy arithmetic properties used by the McCarthy 91 function
------------------------------------------------------------------------------

{-# OPTIONS --exact-split    #-}
{-# OPTIONS --no-sized-types #-}
{-# OPTIONS --without-K      #-}

-- Tested with the development version of the Agda standard library on
-- 02 February 2012.

module Interactive.Agsy.McCarthy91.Arithmetic where

open import Data.Nat
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------------

91≡[100+11∸10]∸10 : (100 + 11 ∸ 10) ∸ 10 ≡ 91
91≡[100+11∸10]∸10 = refl

20>19 : 20 > 19  -- via Agsy
20>19 = s≤s
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
                    (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))))))))))))

50>49 : 50 > 49  -- via Agsy {-t 30}
50>49 = s≤s
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
                                                           z≤n)))))))))))))))))))))))))))))))))))))))))))))))))

75>74 : 75 > 74  -- via Agsy {-t 180}
75>74 = s≤s
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
                                                                                    z≤n))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

101>100 : 101 > 100  -- via Agsy {-t 600}
101>100 = s≤s
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
