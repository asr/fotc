------------------------------------------------------------------------------
-- The alternating bit protocol (ABP)
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- This module define the ABP following the presentation in [1].

-- [1] Peter Dybjer and Herbert Sander. A functional programming
--     approach to the specification and verification of concurrent
--     systems. Formal Aspects of Computing, 1:303–319, 1989.

module FOTC.Program.ABP.ABP where

open import FOTC.Base
open import FOTC.Base.Loop
open import FOTC.Base.List
open import FOTC.Data.Bool
open import FOTC.Data.Stream
open import FOTC.Program.ABP.Fair
open import FOTC.Program.ABP.Terms

------------------------------------------------------------------------------
-- ABP equations

postulate
  send ack out corrupt : D → D
  await                : D → D → D → D → D

postulate send-eq : ∀ b i is ds →
                    send b · (i ∷ is) · ds ≡ < i , b > ∷ await b i is ds
{-# ATP axiom send-eq #-}

postulate
  await-ok≡ : ∀ b b' i is ds →
              b ≡ b' →
              await b i is (ok b' ∷ ds) ≡ send (not b) · is · ds

  await-ok≢ : ∀ b b' i is ds →
              b ≢ b' →
              await b i is (ok b' ∷ ds) ≡ < i , b > ∷ await b i is ds

  await-error : ∀ b i is ds →
                await b i is (error ∷ ds) ≡ < i , b > ∷ await b i is ds
{-# ATP axiom await-ok≡ await-ok≢ await-error #-}

postulate
  ack-ok≡ : ∀ b b' i bs →
            b ≡ b' → ack b · (ok < i , b' > ∷ bs) ≡ b ∷ ack (not b) · bs

  ack-ok≢ : ∀ b b' i bs →
            b ≢ b' → ack b · (ok < i , b' > ∷ bs) ≡ not b ∷ ack b · bs

  ack-error : ∀ b bs → ack b · (error ∷ bs) ≡ not b ∷ ack b · bs
{-# ATP axiom ack-ok≡ ack-ok≢ ack-error #-}

postulate
  out-ok≡ : ∀ b b' i bs →
            b ≡ b' → out b · (ok < i , b' > ∷ bs) ≡ i ∷ out (not b) · bs

  out-ok≢ : ∀ b b' i bs →
            b ≢ b' → out b · (ok < i , b' > ∷ bs) ≡ out b · bs

  out-error : ∀ b bs → out b · (error ∷ bs) ≡ out b · bs
{-# ATP axiom out-ok≡ out-ok≢ out-error #-}

postulate
  corrupt-T : ∀ os x xs →
              corrupt (T ∷ os) · (x ∷ xs) ≡ ok x ∷ corrupt os · xs
  corrupt-F : ∀ os x xs →
              corrupt (F ∷ os) · (x ∷ xs) ≡ error ∷ corrupt os · xs
{-# ATP axiom corrupt-T corrupt-F #-}

postulate has hbs hcs hds : D → D → D → D → D → D → D

postulate has-eq : ∀ f₁ f₂ f₃ g₁ g₂ is →
                   has f₁ f₂ f₃ g₁ g₂ is ≡ f₁ · is · (hds f₁ f₂ f₃ g₁ g₂ is)
{-# ATP axiom has-eq #-}

postulate hbs-eq : ∀ f₁ f₂ f₃ g₁ g₂ is →
                   hbs f₁ f₂ f₃ g₁ g₂ is ≡ g₁ · (has f₁ f₂ f₃ g₁ g₂ is)
{-# ATP axiom hbs-eq #-}

postulate hcs-eq : ∀ f₁ f₂ f₃ g₁ g₂ is →
                   hcs f₁ f₂ f₃ g₁ g₂ is ≡ f₂ · (hbs f₁ f₂ f₃ g₁ g₂ is)
{-# ATP axiom hcs-eq #-}

postulate hds-eq : ∀ f₁ f₂ f₃ g₁ g₂ is →
                   hds f₁ f₂ f₃ g₁ g₂ is ≡ g₂ · (hcs f₁ f₂ f₃ g₁ g₂ is)
{-# ATP axiom hds-eq #-}

postulate
  transfer    : D → D → D → D → D → D → D
  transfer-eq : ∀ f₁ f₂ f₃ g₁ g₂ is →
                transfer f₁ f₂ f₃ g₁ g₂ is ≡ f₃ · (hbs f₁ f₂ f₃ g₁ g₂ is)
{-# ATP axiom transfer-eq #-}

postulate
  abpTransfer    : D → D → D → D → D
  abpTransfer-eq : ∀ b os₁ os₂ is →
                   abpTransfer b os₁ os₂ is ≡
                     transfer (send b) (ack b) (out b) (corrupt os₁)
                       (corrupt os₂) is
{-# ATP axiom abpTransfer-eq #-}

------------------------------------------------------------------------------
-- ABP relations

-- Abbreviation for the recursive equations of the alternating bit
-- protocol.
ABP : D → D → D → D → D → D → D → D → D → Set
ABP b is os₁ os₂ as bs cs ds js =
  as ≡ send b · is · ds
  ∧ bs ≡ corrupt os₁ · as
  ∧ cs ≡ ack b · bs
  ∧ ds ≡ corrupt os₂ · cs
  ∧ js ≡ out b · bs
{-# ATP definition ABP #-}

ABP' : D → D → D → D → D → D → D → D → D → D → Set
ABP' b i' is' os₁' os₂' as' bs' cs' ds' js' =
  ds' ≡ corrupt os₂' · (b ∷ cs')
  ∧ as' ≡ await b i' is' ds'  -- Typo in ds'.
  ∧ bs' ≡ corrupt os₁' · as'
  ∧ cs' ≡ ack (not b) · bs'
  ∧ js' ≡ out (not b) · bs'
{-# ATP definition ABP' #-}

-- Auxiliary bisimulation.
B : D → D → Set
B is js = ∃[ b ] ∃[ os₁ ] ∃[ os₂ ] ∃[ as ] ∃[ bs ] ∃[ cs ] ∃[ ds ]
            Stream is
            ∧ Bit b
            ∧ Fair os₁
            ∧ Fair os₂
            ∧ ABP b is os₁ os₂ as bs cs ds js
{-# ATP definition B #-}
