------------------------------------------------------------------------------
-- ABP Lemma 1
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- From Dybjer and Sander's paper: The first lemma states that given a
-- start state S of the ABP, we will arrive at a state S', where the
-- message has been received by the receiver, but where the
-- acknowledgement has not yet been received by the sender.

module CombinedFOT.FOTC.Program.ABP.Lemma1NoHelper where

open import Combined.FOTC.Base
open import Combined.FOTC.Base.List
open import Combined.FOTC.Base.Loop
open import Combined.FOTC.Data.Bool
open import Combined.FOTC.Data.Bool.Properties using ( x≢not-x )
open import Combined.FOTC.Data.List
open import Combined.FOTC.Program.ABP.ABP
open import Combined.FOTC.Program.ABP.Fair.Type
open import Combined.FOTC.Program.ABP.Fair.Properties
open import Combined.FOTC.Program.ABP.Terms

------------------------------------------------------------------------------
-- 30 November 2013. If we don't have the following definitions
-- outside, the ATPs cannot prove the theorems.

as^ : ∀ b i' is' ds → D
as^ b i' is' ds = await b i' is' ds
{-# ATP definition as^ #-}

bs^ : D → D → D → D → D → D
bs^ b i' is' ds os₁^ = corrupt os₁^ · (as^ b i' is' ds)
{-# ATP definition bs^ #-}

cs^ : D → D → D → D → D → D
cs^ b i' is' ds os₁^ = ack b · (bs^ b i' is' ds os₁^)
{-# ATP definition cs^ #-}

ds^ : D → D → D → D → D → D → D
ds^ b i' is' ds os₁^ os₂^ = corrupt os₂^ · cs^ b i' is' ds os₁^
{-# ATP definition ds^ #-}

os₁^ : D → D → D
os₁^ os₁' ft₁^ = ft₁^ ++ os₁'
{-# ATP definition os₁^ #-}

os₂^ : D → D
os₂^ os₂ = tail₁ os₂
{-# ATP definition os₂^ #-}

------------------------------------------------------------------------------
-- From Dybjer and Sander's paper: From the assumption that os₁ ∈ Fair
-- and hence by unfolding Fair, we conclude that there are ft₁ :  F*T
-- and os₁' : Fair, such that os₁ = ft₁ ++ os₁'.
--
-- We proceed by induction on ft₁ : F*T using helper.

-- 26 January 2014. Pattern matching after a @with@ it is not accepted
-- by the termination checker. See Agda issue 59, comment 18.

{-# TERMINATING #-}
lemma₁ : ∀ b i' is' os₁ os₂ as bs cs ds js →
         Bit b →
         Fair os₁ →
         Fair os₂ →
         S b (i' ∷ is') os₁ os₂ as bs cs ds js →
         ∃[ os₁' ] ∃[ os₂' ] ∃[ as' ] ∃[ bs' ] ∃[ cs' ] ∃[ ds' ] ∃[ js' ]
           Fair os₁'
           ∧ Fair os₂'
           ∧ S' b i' is' os₁' os₂' as' bs' cs' ds' js'
           ∧ js ≡ i' ∷ js'
lemma₁ b i' is' os₁ os₂ as bs cs ds js Bb Fos₁ Fos₂ s with Fair-out Fos₁
... | .(true ∷ []) , os₁' , f*tnil , os₁≡ft₁++os₁' , Fos₁' = prf
  where
  postulate
    prf : ∃[ os₁' ] ∃[ os₂' ] ∃[ as' ] ∃[ bs' ] ∃[ cs' ] ∃[ ds' ] ∃[ js' ]
            Fair os₁'
            ∧ Fair os₂'
            ∧ (as' ≡ await b i' is' ds'
              ∧ bs' ≡ corrupt os₁' · as'
              ∧ cs' ≡ ack (not b) · bs'
              ∧ ds' ≡ corrupt os₂' · (b ∷ cs')
              ∧ js' ≡ out (not b) · bs')
            ∧ js ≡ i' ∷ js'
  {-# ATP prove prf #-}

... | .(F ∷ ft₁^) , os₁' , f*tcons {ft₁^} FTft₁ , os₁≡ft₁++os₁' , Fos₁' =
  lemma₁ b i' is'
         (ft₁^ ++ os₁')
         (tail₁ os₂)
         (await b i' is' ds)
         (corrupt (ft₁^ ++ os₁') · await b i' is' ds)
         (ack b · (corrupt (ft₁^ ++ os₁') · await b i' is' ds))
         (corrupt (tail₁ os₂) ·
           (ack b · (corrupt (ft₁^ ++ os₁') · await b i' is' ds)))
         js Bb (Fair-in (ft₁^ , os₁' , FTft₁ , refl , Fos₁')) (tail-Fair Fos₂) ihS
     where
     postulate os₁-eq-helper : os₁ ≡ F ∷ os₁^ os₁' ft₁^
     {-# ATP prove os₁-eq-helper #-}

     postulate as-eq : as ≡ < i' , b > ∷ (as^ b i' is' ds)
     {-# ATP prove as-eq #-}

     postulate bs-eq : bs ≡ error ∷ (bs^ b i' is' ds (os₁^ os₁' ft₁^))
     {-# ATP prove bs-eq os₁-eq-helper as-eq #-}

     postulate cs-eq : cs ≡ not b ∷ cs^ b i' is' ds (os₁^ os₁' ft₁^)
     {-# ATP prove cs-eq bs-eq #-}

     postulate ds-eq : ds ≡ ok (not b) ∷ ds^ b i' is' ds (os₁^ os₁' ft₁^) (os₂^ os₂)
                  ∨ ds ≡ error ∷ ds^ b i' is' ds (os₁^ os₁' ft₁^) (os₂^ os₂)
     {-# ATP prove ds-eq head-tail-Fair cs-eq #-}

     postulate
       as^-eq-helper₁ :
         ds ≡ ok (not b) ∷ ds^ b i' is' ds (os₁^ os₁' ft₁^) (os₂^ os₂) →
         as^ b i' is' ds ≡
           send b · (i' ∷ is') · ds^ b i' is' ds (os₁^ os₁' ft₁^) (os₂^ os₂)
     {-# ATP prove as^-eq-helper₁ x≢not-x #-}

     postulate
       as^-eq-helper₂ :
         ds ≡ error ∷ ds^ b i' is' ds (os₁^ os₁' ft₁^) (os₂^ os₂) →
         as^ b i' is' ds ≡
           send b · (i' ∷ is') · ds^ b i' is' ds (os₁^ os₁' ft₁^) (os₂^ os₂)
     {-# ATP prove as^-eq-helper₂ #-}

     as^-eq : as^ b i' is' ds ≡
              send b · (i' ∷ is') · ds^ b i' is' ds (os₁^ os₁' ft₁^) (os₂^ os₂)
     as^-eq = case as^-eq-helper₁ as^-eq-helper₂ ds-eq

     postulate js-eq : js ≡ out b · bs^ b i' is' ds (os₁^ os₁' ft₁^)
     {-# ATP prove js-eq bs-eq #-}

     ihS : S b
             (i' ∷ is')
             (os₁^ os₁' ft₁^)
             (os₂^ os₂)
             (as^ b i' is' ds)
             (bs^ b i' is' ds (os₁^ os₁' ft₁^))
             (cs^ b i' is' ds (os₁^ os₁' ft₁^))
             (ds^ b i' is' ds (os₁^ os₁' ft₁^) (os₂^ os₂))
             js
     ihS = as^-eq , refl , refl , refl , js-eq
