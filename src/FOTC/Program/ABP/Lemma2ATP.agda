------------------------------------------------------------------------------
-- ABP lemma 2
------------------------------------------------------------------------------

-- From the paper: The second lemma states that given a state of the
-- latter kind (see lemma 1) we will arrive at a new start state, which
-- is identical to the old start state except that the bit has alternated
-- and the first item in the input stream has been removed.

module FOTC.Program.ABP.Lemma2ATP where

open import FOTC.Base

open import Common.Function

open import FOTC.Data.Bool
open import FOTC.Data.Bool.PropertiesATP
open import FOTC.Data.List

open import FOTC.Program.ABP.ABP
open import FOTC.Program.ABP.Fair
open import FOTC.Program.ABP.Fair.PropertiesATP
open import FOTC.Program.ABP.Terms

------------------------------------------------------------------------------

-- TODO: These variables are outside the where clause due to an issue
-- in the translation.

ds⁵ : ∀ cs' os₁⁵ → D
ds⁵ cs' os₁⁵ = corrupt · os₁⁵ · cs'
{-# ATP definition ds⁵ #-}

as⁵ : ∀ b i' is' cs' os₁⁵ → D
as⁵ b i' is' cs' os₁⁵ = await b i' is' (ds⁵ cs' os₁⁵)
{-# ATP definition as⁵ #-}

bs⁵ : ∀ b i' is' cs' os₀⁵ os₁⁵ → D
bs⁵ b i' is' cs' os₀⁵ os₁⁵ = corrupt · os₀⁵ · as⁵ b i' is' cs' os₁⁵
{-# ATP definition bs⁵ #-}

cs⁵ : ∀ b i' is' cs' os₀⁵ os₁⁵ → D
cs⁵ b i' is' cs' os₀⁵ os₁⁵ = abpack · (not b) · bs⁵ b i' is' cs' os₀⁵ os₁⁵
{-# ATP definition cs⁵ #-}

os₀⁵ : ∀ os₀' → D
os₀⁵ os₀' = tail os₀'
{-# ATP definition os₀⁵ #-}

os₁⁵ : ∀ ol₁ os₁'' → D
os₁⁵ ol₁ os₁'' = ol₁ ++ os₁''
{-# ATP definition os₁⁵ #-}

lemma₂-helper : ∀ {b i' is' os₀' os₁' as' bs' cs' ds' js'} →
                Bit b →
                Fair os₀' →
                Abp' b i' is' os₀' os₁' as' bs' cs' ds' js' →
                ∀ {ol₁ os₁''-aux} →
                O*L ol₁ → Fair (os₁''-aux) → os₁' ≡ ol₁ ++ os₁''-aux →
                ∃ λ os₀'' → ∃ λ os₁'' →
                ∃ λ as'' → ∃ λ bs'' → ∃ λ cs'' → ∃ λ ds'' →
                Fair os₀''
                ∧ Fair os₁''
                ∧ Abp (not b) is' os₀'' os₁'' as'' bs'' cs'' ds'' js'
lemma₂-helper {b} {i'} {is'} {os₀'} {os₁'} {as'} {bs'} {cs'} {ds'} {js'}
              Bb Fos₀' h {os₁''-aux = os₁''} nilO*L Fos₁'' os₁'-eq = prf
  where
  postulate prf : ∃ (λ os₀'' → ∃ (λ os₁'' →
                  ∃ (λ as'' → ∃ (λ bs'' → ∃ (λ cs'' → ∃ (λ ds'' →
                  Fair os₀''
                  ∧ Fair os₁''
                  ∧ as'' ≡ abpsend · not b · is' · ds''
                  ∧ bs'' ≡ corrupt · os₀'' · as''
                  ∧ cs'' ≡ abpack · not b · bs''
                  ∧ ds'' ≡ corrupt · os₁'' · cs''
                  ∧ js' ≡ abpout · not b · bs''))))))
  {-# ATP prove prf #-}

lemma₂-helper {b} {i'} {is'} {os₀'} {os₁'} {as'} {bs'} {cs'} {ds'} {js'}
              Bb Fos₀' abp' -- (ds'Abp' , as'Abp , bs'Abp' , cs'Abp' , js'Abp')
              {os₁''-aux = os₁''} (consO*L ol₁ OLol₁)
              Fos₁'' os₁'-eq =
  lemma₂-helper Bb (tail-Fair Fos₀') Abp'IH OLol₁ Fos₁'' refl

  where
  postulate os₁'-eq-helper : os₁' ≡ O ∷ os₁⁵ ol₁ os₁''
  {-# ATP prove os₁'-eq-helper #-}

  postulate ds'-eq : ds' ≡ error ∷ ds⁵ cs' (os₁⁵ ol₁ os₁'')
  {-# ATP prove ds'-eq os₁'-eq-helper #-}

  postulate as'-eq : as' ≡ < i' , b > ∷ as⁵ b i' is' cs' (os₁⁵ ol₁ os₁'')
  {-# ATP prove as'-eq #-}

  postulate
    bs'-eq-helper₁ : os₀' ≡ L ∷ tail os₀' →
                     bs' ≡ ok < i' , b > ∷ bs⁵ b i' is' cs' (os₀⁵ os₀') (os₁⁵ ol₁ os₁'')
  {-# ATP prove bs'-eq-helper₁ as'-eq #-}

  postulate
    bs'-eq-helper₂ : os₀' ≡ O ∷ tail os₀' →
                     bs' ≡ error ∷ bs⁵ b i' is' cs' (os₀⁵ os₀') (os₁⁵ ol₁ os₁'')
  {-# ATP prove bs'-eq-helper₁ as'-eq #-}

  bs'-eq : bs' ≡ ok < i' , b > ∷ bs⁵ b i' is' cs' (os₀⁵ os₀') (os₁⁵ ol₁ os₁'')
           ∨ bs' ≡ error ∷ bs⁵ b i' is' cs' (os₀⁵ os₀') (os₁⁵ ol₁ os₁'')
  bs'-eq = [ (λ h → inj₁ (bs'-eq-helper₁ h))
           , (λ h → inj₂ (bs'-eq-helper₂ h))
           ] (head-tail-Fair Fos₀')

  postulate
    cs'-eq-helper₁ : bs' ≡ ok < i' , b > ∷ bs⁵ b i' is' cs' (os₀⁵ os₀') (os₁⁵ ol₁ os₁'') →
                     cs' ≡ b ∷ cs⁵ b i' is' cs' (os₀⁵ os₀') (os₁⁵ ol₁ os₁'')
  {-# ATP prove cs'-eq-helper₁ not-x≠x not² #-}

  postulate
    cs'-eq-helper₂ : bs' ≡ error ∷ bs⁵ b i' is' cs' (os₀⁵ os₀') (os₁⁵ ol₁ os₁'') →
                     cs' ≡ b ∷ cs⁵ b i' is' cs' (os₀⁵ os₀') (os₁⁵ ol₁ os₁'')
  {-# ATP prove cs'-eq-helper₂ not² #-}

  cs'-eq : cs' ≡ b ∷ cs⁵ b i' is' cs' (os₀⁵ os₀') (os₁⁵ ol₁ os₁'')
  cs'-eq = [ cs'-eq-helper₁ , cs'-eq-helper₂ ] bs'-eq

  postulate
    js'-eq-helper₁ : bs' ≡ ok < i' , b > ∷ bs⁵ b i' is' cs' (os₀⁵ os₀') (os₁⁵ ol₁ os₁'') →
                     js' ≡ abpout · (not b) · bs⁵ b i' is' cs' (os₀⁵ os₀') (os₁⁵ ol₁ os₁'')
  {-# ATP prove js'-eq-helper₁ not-x≠x #-}

  postulate
    js'-eq-helper₂ : bs' ≡ error ∷ bs⁵ b i' is' cs' (os₀⁵ os₀') (os₁⁵ ol₁ os₁'') →
                     js' ≡ abpout · (not b) · bs⁵ b i' is' cs' (os₀⁵ os₀') (os₁⁵ ol₁ os₁'')
  {-# ATP prove js'-eq-helper₂ #-}

  js'-eq : js' ≡ abpout · (not b) · bs⁵ b i' is' cs' (os₀⁵ os₀') (os₁⁵ ol₁ os₁'')
  js'-eq = [ js'-eq-helper₁ , js'-eq-helper₂ ] bs'-eq

  postulate
    ds⁵-eq : ds⁵ cs' (os₁⁵ ol₁ os₁'') ≡
             corrupt · (os₁⁵ ol₁ os₁'') · (b ∷ cs⁵ b i' is' cs' (os₀⁵ os₀') (os₁⁵ ol₁ os₁''))

  Abp'IH : Abp' b i' is'
                (os₀⁵ os₀')
                (os₁⁵ ol₁ os₁'')
                (as⁵ b i' is' cs' (os₁⁵ ol₁ os₁''))
                (bs⁵ b i' is' cs' (os₀⁵ os₀') (os₁⁵ ol₁ os₁''))
                (cs⁵ b i' is' cs' (os₀⁵ os₀') (os₁⁵ ol₁ os₁''))
                (ds⁵ cs' (os₁⁵ ol₁ os₁''))
                js'
  Abp'IH = ds⁵-eq , refl , refl , refl , js'-eq

-- From the paper: From the assumption that os₁ ∈ Fair, and hence by
-- unfolding Fair we conclude that there are ol₁ : O*L and os₁'' :
-- Fair, such that
--
-- os₁' = ol₁ ++ os₁''.
--
-- We proceed by induction on ol₁ : O*L using lemma₂-helper.

lemma₂ : ∀ {b i' is' os₀' os₁' as' bs' cs' ds' js'} →
         Bit b →
         Fair os₀' →
         Fair os₁' →
         Abp' b i' is' os₀' os₁' as' bs' cs' ds' js' →
         ∃ λ os₀'' → ∃ λ os₁'' →
         ∃ λ as'' → ∃ λ bs'' → ∃ λ cs'' → ∃ λ ds'' →
         Fair os₀''
         ∧ Fair os₁''
         ∧ Abp (not b) is' os₀'' os₁'' as'' bs'' cs'' ds'' js'
lemma₂ {os₁' = os₁'} Bb Fos₀' Fos₁' h =
  lemma₂-helper Bb Fos₀' h OLol₀ Fos₁'' os₁'-eq

  where
  unfold-os₁' : ∃ λ ol₁ → ∃ λ os₁'' → O*L ol₁ ∧ Fair os₁'' ∧ os₁' ≡ ol₁ ++ os₁''
  unfold-os₁' = Fair-gfp₁ Fos₁'

  ol₁ : D
  ol₁ = ∃-proj₁ unfold-os₁'

  os₁'' : D
  os₁'' = ∃-proj₁ (∃-proj₂ unfold-os₁')

  OLol₀ : O*L ol₁
  OLol₀ = ∧-proj₁ (∃-proj₂ (∃-proj₂ unfold-os₁'))

  Fos₁'' : Fair os₁''
  Fos₁'' = ∧-proj₁ (∧-proj₂ (∃-proj₂ (∃-proj₂ unfold-os₁')))

  os₁'-eq : os₁' ≡ ol₁ ++ os₁''
  os₁'-eq = ∧-proj₂ (∧-proj₂ (∃-proj₂ (∃-proj₂ unfold-os₁')))
