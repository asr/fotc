module TestExternalFail where

data True : Set where
  tt : True

a : True
a = tt

-- EXTERNAL fails because 'a' is not a postulate
{-# EXTERNAL Equinox a #-}
