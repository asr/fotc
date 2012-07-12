module Records where

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B

-- {-# ATP hint _×_.proj₁ #-}
