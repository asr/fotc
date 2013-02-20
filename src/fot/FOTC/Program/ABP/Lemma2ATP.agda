------------------------------------------------------------------------------
-- ABP lemma 2
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- From Dybjer and Sander's paper: The second lemma states that given
-- a state of the latter kind (see lemma 1) we will arrive at a new
-- start state, which is identical to the old start state except that
-- the bit has alternated and the first item in the input stream has
-- been removed.

module FOTC.Program.ABP.Lemma2ATP where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Base.Loop
open import FOTC.Data.Bool
open import FOTC.Data.Bool.PropertiesATP
open import FOTC.Data.List
open import FOTC.Program.ABP.ABP
open import FOTC.Program.ABP.Fair
open import FOTC.Program.ABP.Fair.PropertiesATP
open import FOTC.Program.ABP.Terms

------------------------------------------------------------------------------
-- Helper function for the ABP lemma 2

module Helper where
  -- We have these definitions outside the where clause to keep them
  -- simple for the ATPs.

  ds⁵ : D → D → D
  ds⁵ cs' os₁⁵ = corrupt · os₁⁵ · cs'
  {-# ATP definition ds⁵ #-}

  as⁵ : D → D → D → D → D → D
  as⁵ b i' is' cs' os₁⁵ = await b i' is' (ds⁵ cs' os₁⁵)
  {-# ATP definition as⁵ #-}

  bs⁵ : D → D → D → D → D → D → D
  bs⁵ b i' is' cs' os₀⁵ os₁⁵ = corrupt · os₀⁵ · as⁵ b i' is' cs' os₁⁵
  {-# ATP definition bs⁵ #-}

  cs⁵ : D → D → D → D → D → D → D
  cs⁵ b i' is' cs' os₀⁵ os₁⁵ = ack · not b · bs⁵ b i' is' cs' os₀⁵ os₁⁵
  {-# ATP definition cs⁵ #-}

  os₀⁵ : D → D
  os₀⁵ os₀' = tail₁ os₀'
  {-# ATP definition os₀⁵ #-}

  os₁⁵ : D → D → D
  os₁⁵ ft₁ os₁'' = ft₁ ++ os₁''
  {-# ATP definition os₁⁵ #-}

  helper : ∀ {b i' is' os₀' os₁' as' bs' cs' ds' js'} →
           Bit b →
           Fair os₀' →
           ABP' b i' is' os₀' os₁' as' bs' cs' ds' js' →
           ∀ ft₁ os₁'' → F*T ft₁ → Fair os₁'' → os₁' ≡ ft₁ ++ os₁'' →
           ∃[ os₀'' ] ∃[ os₁'' ] ∃[ as'' ] ∃[ bs'' ] ∃[ cs'' ] ∃[ ds'' ]
           Fair os₀''
           ∧ Fair os₁''
           ∧ ABP (not b) is' os₀'' os₁'' as'' bs'' cs'' ds'' js'
  helper {b} {i'} {is'} {js' = js'} Bb Fos₀' abp'
         .(T ∷ []) os₁'' f*tnil Fos₁'' os₁'-eq = prf
    where
    postulate
      prf : ∃[ os₀'' ] ∃[ os₁'' ] ∃[ as'' ] ∃[ bs'' ] ∃[ cs'' ] ∃[ ds'' ]
            Fair os₀''
            ∧ Fair os₁''
            ∧ as'' ≡ send · not b · is' · ds''
            ∧ bs'' ≡ corrupt · os₀'' · as''
            ∧ cs'' ≡ ack · not b · bs''
            ∧ ds'' ≡ corrupt · os₁'' · cs''
            ∧ js'  ≡ out · not b · bs''
    {-# ATP prove prf #-}

  helper {b} {i'} {is'} {os₀'} {os₁'} {as'} {bs'} {cs'} {ds'} {js'}
         Bb Fos₀' abp'
         .(F ∷ ft₁) os₁'' (f*tcons {ft₁} FTft₁) Fos₁'' os₁'-eq
         = helper Bb (tail-Fair Fos₀') ABP'IH ft₁ os₁'' FTft₁ Fos₁'' refl
    where
    postulate os₁'-eq-helper : os₁' ≡ F ∷ os₁⁵ ft₁ os₁''
    {-# ATP prove os₁'-eq-helper #-}

    postulate ds'-eq : ds' ≡ error ∷ ds⁵ cs' (os₁⁵ ft₁ os₁'')
    {-# ATP prove ds'-eq os₁'-eq-helper #-}

    postulate as'-eq : as' ≡ < i' , b > ∷ as⁵ b i' is' cs' (os₁⁵ ft₁ os₁'')
    {-# ATP prove as'-eq #-}

    postulate
      bs'-eq-helper₁ : os₀' ≡ T ∷ tail₁ os₀' →
                       bs' ≡ ok < i' , b > ∷ bs⁵ b i' is' cs' (os₀⁵ os₀') (os₁⁵ ft₁ os₁'')
    {-# ATP prove bs'-eq-helper₁ as'-eq #-}

    postulate
      bs'-eq-helper₂ : os₀' ≡ F ∷ tail₁ os₀' →
                       bs' ≡ error ∷ bs⁵ b i' is' cs' (os₀⁵ os₀') (os₁⁵ ft₁ os₁'')
    {-# ATP prove bs'-eq-helper₂ as'-eq #-}

    bs'-eq : bs' ≡ ok < i' , b > ∷ bs⁵ b i' is' cs' (os₀⁵ os₀') (os₁⁵ ft₁ os₁'')
             ∨ bs' ≡ error ∷ bs⁵ b i' is' cs' (os₀⁵ os₀') (os₁⁵ ft₁ os₁'')
    bs'-eq = case (λ h → inj₁ (bs'-eq-helper₁ h))
                  (λ h → inj₂ (bs'-eq-helper₂ h))
                  (head-tail-Fair Fos₀')

    postulate
      cs'-eq-helper₁ : bs' ≡ ok < i' , b > ∷ bs⁵ b i' is' cs' (os₀⁵ os₀') (os₁⁵ ft₁ os₁'') →
                       cs' ≡ b ∷ cs⁵ b i' is' cs' (os₀⁵ os₀') (os₁⁵ ft₁ os₁'')
    {-# ATP prove cs'-eq-helper₁ not-x≢x not-involutive #-}

    postulate
      cs'-eq-helper₂ : bs' ≡ error ∷ bs⁵ b i' is' cs' (os₀⁵ os₀') (os₁⁵ ft₁ os₁'') →
                       cs' ≡ b ∷ cs⁵ b i' is' cs' (os₀⁵ os₀') (os₁⁵ ft₁ os₁'')
    {-# ATP prove cs'-eq-helper₂ not-involutive #-}

    cs'-eq : cs' ≡ b ∷ cs⁵ b i' is' cs' (os₀⁵ os₀') (os₁⁵ ft₁ os₁'')
    cs'-eq = case cs'-eq-helper₁ cs'-eq-helper₂ bs'-eq

    postulate
      js'-eq-helper₁ : bs' ≡ ok < i' , b > ∷ bs⁵ b i' is' cs' (os₀⁵ os₀') (os₁⁵ ft₁ os₁'') →
                       js' ≡ out · not b
                                 · bs⁵ b i' is' cs' (os₀⁵ os₀') (os₁⁵ ft₁ os₁'')
    {-# ATP prove js'-eq-helper₁ not-x≢x #-}

    postulate
      js'-eq-helper₂ : bs' ≡ error ∷ bs⁵ b i' is' cs' (os₀⁵ os₀') (os₁⁵ ft₁ os₁'') →
                       js' ≡ out · not b
                                 · bs⁵ b i' is' cs' (os₀⁵ os₀') (os₁⁵ ft₁ os₁'')
    {-# ATP prove js'-eq-helper₂ #-}

    js'-eq : js' ≡ out · not b · bs⁵ b i' is' cs' (os₀⁵ os₀') (os₁⁵ ft₁ os₁'')
    js'-eq = case js'-eq-helper₁ js'-eq-helper₂ bs'-eq

    postulate ds⁵-eq : ds⁵ cs' (os₁⁵ ft₁ os₁'') ≡
                       corrupt · (os₁⁵ ft₁ os₁'')
                               · (b ∷ cs⁵ b i' is' cs' (os₀⁵ os₀') (os₁⁵ ft₁ os₁''))

    ABP'IH : ABP' b i' is'
                  (os₀⁵ os₀')
                  (os₁⁵ ft₁ os₁'')
                  (as⁵ b i' is' cs' (os₁⁵ ft₁ os₁''))
                  (bs⁵ b i' is' cs' (os₀⁵ os₀') (os₁⁵ ft₁ os₁''))
                  (cs⁵ b i' is' cs' (os₀⁵ os₀') (os₁⁵ ft₁ os₁''))
                  (ds⁵ cs' (os₁⁵ ft₁ os₁''))
                  js'
    ABP'IH = ds⁵-eq , refl , refl , refl , js'-eq

------------------------------------------------------------------------------
-- From Dybjer and Sander's paper: From the assumption that os₁ ∈
-- Fair, and hence by unfolding Fair we conclude that there are ft₁ :
-- F*T and os₁'' : Fair, such that os₁' = ft₁ ++ os₁''.
--
-- We proceed by induction on ft₁ : F*T using helper.

open Helper
lemma₂ : ∀ {b i' is' os₀' os₁' as' bs' cs' ds' js'} →
         Bit b →
         Fair os₀' →
         Fair os₁' →
         ABP' b i' is' os₀' os₁' as' bs' cs' ds' js' →
         ∃[ os₀'' ] ∃[ os₁'' ] ∃[ as'' ] ∃[ bs'' ] ∃[ cs'' ] ∃[ ds'' ]
         Fair os₀''
         ∧ Fair os₁''
         ∧ ABP (not b) is' os₀'' os₁'' as'' bs'' cs'' ds'' js'
lemma₂ Bb Fos₀' Fos₁' abp' with Fair-unf Fos₁'
... | ft , os₀'' , FTft , Fos₀'' , h =
  helper Bb Fos₀' abp' ft os₀'' FTft Fos₀'' h
