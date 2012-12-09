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
open import FOTC.Base.List
open import FOTC.Data.Bool
open import FOTC.Data.Stream
open import FOTC.Program.ABP.Fair
open import FOTC.Program.ABP.Terms

------------------------------------------------------------------------------
-- ABP equations

postulate
  send ack out corrupt : D
  await                : D → D → D → D → D

postulate send-eq : ∀ b i is ds →
                    send · b · (i ∷ is) · ds ≡ < i , b > ∷ await b i is ds
{-# ATP axiom send-eq #-}

postulate
  await-ok≡ : ∀ b b₀ i is ds →
              b ≡ b₀ →
              await b i is (ok b₀ ∷ ds) ≡ send · not b · is · ds

  await-ok≢ : ∀ b b₀ i is ds →
              b ≢ b₀ →
              await b i is (ok b₀ ∷ ds) ≡ < i , b > ∷ await b i is ds

  await-error : ∀ b i is ds →
                await b i is (error ∷ ds) ≡ < i , b > ∷ await b i is ds
{-# ATP axiom await-ok≡ await-ok≢ await-error #-}

postulate
  ack-ok≡ : ∀ b b₀ i bs →
            b ≡ b₀ →
            ack · b · (ok < i , b₀ > ∷ bs) ≡ b ∷ ack · not b · bs

  ack-ok≢ : ∀ b b₀ i bs →
            b ≢ b₀ →
            ack · b · (ok < i , b₀ > ∷ bs) ≡ not b ∷ ack · b · bs

  ack-error : ∀ b bs → ack · b · (error ∷ bs) ≡ not b ∷ ack · b · bs
{-# ATP axiom ack-ok≡ ack-ok≢ ack-error #-}

postulate
  out-ok≡ : ∀ b b₀ i bs →
            b ≡ b₀ →
            out · b · (ok < i , b₀ > ∷ bs) ≡ i ∷ out · not b · bs

  out-ok≢ : ∀ b b₀ i bs →
            b ≢ b₀ →
            out · b · (ok < i , b₀ > ∷ bs) ≡ out · b · bs

  out-error : ∀ b bs → out · b · (error ∷ bs) ≡ out · b · bs
{-# ATP axiom out-ok≡ out-ok≢ out-error #-}

postulate
  corrupt-T : ∀ fs x xs →
              corrupt · (T ∷ fs) · (x ∷ xs) ≡ ok x ∷ corrupt · fs · xs
  corrupt-F : ∀ fs x xs →
              corrupt · (F ∷ fs) · (x ∷ xs) ≡ error ∷ corrupt · fs · xs
{-# ATP axiom corrupt-T corrupt-F #-}

postulate has hbs hcs hds : D → D → D → D → D → D → D

postulate
  has-eq : ∀ f₁ f₂ f₃ g₁ g₂ is →
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
  genTransfer    : D → D → D → D → D → D → D
  genTransfer-eq : ∀ f₁ f₂ f₃ g₁ g₂ is →
                   genTransfer f₁ f₂ f₃ g₁ g₂ is ≡ f₃ · (hbs f₁ f₂ f₃ g₁ g₂ is)
{-# ATP axiom genTransfer-eq #-}

postulate
  transfer    : D → D → D → D → D
  transfer-eq : ∀ b fs₀ fs₁ is → transfer b fs₀ fs₁ is ≡
                genTransfer (send · b) (ack · b) (out · b)
                            (corrupt · fs₀) (corrupt · fs₁) is
{-# ATP axiom transfer-eq #-}

------------------------------------------------------------------------------
-- ABP relations

-- Abbreviation for the recursive equations of the alternating bit
-- protocol.
ABP : D → D → D → D → D → D → D → D → D → Set
ABP b is fs₀ fs₁ as bs cs ds js =
  as ≡ send · b · is · ds
  ∧ bs ≡ corrupt · fs₀ · as
  ∧ cs ≡ ack · b · bs
  ∧ ds ≡ corrupt · fs₁ · cs
  ∧ js ≡ out · b · bs
{-# ATP definition ABP #-}

ABP' : D → D → D → D → D → D → D → D → D → D → Set
ABP' b i' is' fs₀' fs₁' as' bs' cs' ds' js' =
  ds' ≡ corrupt · fs₁' · (b ∷ cs')
  ∧ as' ≡ await b i' is' ds'  -- Typo in ds'.
  ∧ bs' ≡ corrupt · fs₀' · as'
  ∧ cs' ≡ ack · not b · bs'
  ∧ js' ≡ out · not b · bs'
{-# ATP definition ABP' #-}

-- Auxiliary bisimulation.
B : D → D → Set
B is js = ∃[ b ] ∃[ fs₀ ] ∃[ fs₁ ] ∃[ as ] ∃[ bs ] ∃[ cs ] ∃[ ds ]
          Stream is
          ∧ Bit b
          ∧ Fair fs₀
          ∧ Fair fs₁
          ∧ ABP b is fs₀ fs₁ as bs cs ds js
{-# ATP definition B #-}
