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
  using ( not-x≢x
        ; not-involutive
        )
open import FOTC.Data.List
open import FOTC.Program.ABP.ABP
open import FOTC.Program.ABP.Fair.Type
open import FOTC.Program.ABP.Fair.PropertiesATP
open import FOTC.Program.ABP.Terms

------------------------------------------------------------------------------
-- 30 November 2013. If we don't have the following definitions
-- outside the where clause, the ATPs cannot prove the theorems.

ds^ : D → D → D
ds^ cs' os₂^ = corrupt os₂^ · cs'
{-# ATP definition ds^ #-}

as^ : D → D → D → D → D → D
as^ b i' is' cs' os₂^ = await b i' is' (ds^ cs' os₂^)
{-# ATP definition as^ #-}

bs^ : D → D → D → D → D → D → D
bs^ b i' is' cs' os₁^ os₂^ = corrupt os₁^ · as^ b i' is' cs' os₂^
{-# ATP definition bs^ #-}

cs^ : D → D → D → D → D → D → D
cs^ b i' is' cs' os₁^ os₂^ = ack (not b) · bs^ b i' is' cs' os₁^ os₂^
{-# ATP definition cs^ #-}

os₁^ : D → D
os₁^ os₁' = tail₁ os₁'
{-# ATP definition os₁^ #-}

os₂^ : D → D → D
os₂^ ft₂ os₂'' = ft₂ ++ os₂''
{-# ATP definition os₂^ #-}

-- Helper function for the lemma 2.
helper : ∀ {b i' is' os₁' os₂' as' bs' cs' ds' js'} →
         Bit b →
         Fair os₁' →
         S' b i' is' os₁' os₂' as' bs' cs' ds' js' →
         ∀ ft₂ os₂'' → F*T ft₂ → Fair os₂'' → os₂' ≡ ft₂ ++ os₂'' →
         ∃[ os₁'' ] ∃[ os₂'' ] ∃[ as'' ] ∃[ bs'' ] ∃[ cs'' ] ∃[ ds'' ]
           Fair os₁''
           ∧ Fair os₂''
           ∧ S (not b) is' os₁'' os₂'' as'' bs'' cs'' ds'' js'
helper {b} {i'} {is'} {js' = js'} Bb Fos₁' s'
       .(T ∷ []) os₂'' f*tnil Fos₂'' os₂'-eq = prf
  where
  postulate
    prf : ∃[ os₁'' ] ∃[ os₂'' ] ∃[ as'' ] ∃[ bs'' ] ∃[ cs'' ] ∃[ ds'' ]
          Fair os₁''
          ∧ Fair os₂''
          ∧ as'' ≡ send (not b) · is' · ds''
          ∧ bs'' ≡ corrupt os₁'' · as''
          ∧ cs'' ≡ ack (not b) · bs''
          ∧ ds'' ≡ corrupt os₂'' · cs''
          ∧ js'  ≡ out (not b) · bs''
  {-# ATP prove prf #-}

helper {b} {i'} {is'} {os₁'} {os₂'} {as'} {bs'} {cs'} {ds'} {js'}
       Bb Fos₁' s'
       .(F ∷ ft₂) os₂'' (f*tcons {ft₂} FTft₂) Fos₂'' os₂'-eq =
       helper Bb (tail-Fair Fos₁') ihS' ft₂ os₂'' FTft₂ Fos₂'' refl
  where
  postulate os₂'-eq-helper : os₂' ≡ F ∷ os₂^ ft₂ os₂''
  {-# ATP prove os₂'-eq-helper #-}

  postulate ds'-eq : ds' ≡ error ∷ ds^ cs' (os₂^ ft₂ os₂'')
  {-# ATP prove ds'-eq os₂'-eq-helper #-}

  postulate as'-eq : as' ≡ < i' , b > ∷ as^ b i' is' cs' (os₂^ ft₂ os₂'')
  {-# ATP prove as'-eq #-}

  postulate
    bs'-eq : bs' ≡ ok < i' , b > ∷ bs^ b i' is' cs' (os₁^ os₁') (os₂^ ft₂ os₂'')
               ∨ bs' ≡ error ∷ bs^ b i' is' cs' (os₁^ os₁') (os₂^ ft₂ os₂'')
  {-# ATP prove bs'-eq as'-eq head-tail-Fair #-}

  postulate
    cs'-eq-helper₁ :
      bs' ≡ ok < i' , b > ∷ bs^ b i' is' cs' (os₁^ os₁') (os₂^ ft₂ os₂'') →
      cs' ≡ b ∷ cs^ b i' is' cs' (os₁^ os₁') (os₂^ ft₂ os₂'')
  {-# ATP prove cs'-eq-helper₁ not-x≢x not-involutive #-}

  postulate
    cs'-eq-helper₂ :
      bs' ≡ error ∷ bs^ b i' is' cs' (os₁^ os₁') (os₂^ ft₂ os₂'') →
      cs' ≡ b ∷ cs^ b i' is' cs' (os₁^ os₁') (os₂^ ft₂ os₂'')
  {-# ATP prove cs'-eq-helper₂ not-involutive #-}

  cs'-eq : cs' ≡ b ∷ cs^ b i' is' cs' (os₁^ os₁') (os₂^ ft₂ os₂'')
  cs'-eq = case cs'-eq-helper₁ cs'-eq-helper₂ bs'-eq

  postulate
    js'-eq : js' ≡ out (not b) · bs^ b i' is' cs' (os₁^ os₁') (os₂^ ft₂ os₂'')
  {-# ATP prove js'-eq not-x≢x bs'-eq #-}

  postulate
    ds^-eq : ds^ cs' (os₂^ ft₂ os₂'') ≡
             corrupt (os₂^ ft₂ os₂'') ·
               (b ∷ cs^ b i' is' cs' (os₁^ os₁') (os₂^ ft₂ os₂''))
  {-# ATP prove ds^-eq cs'-eq #-}

  ihS' : S' b i' is'
            (os₁^ os₁')
            (os₂^ ft₂ os₂'')
            (as^ b i' is' cs' (os₂^ ft₂ os₂''))
            (bs^ b i' is' cs' (os₁^ os₁') (os₂^ ft₂ os₂''))
            (cs^ b i' is' cs' (os₁^ os₁') (os₂^ ft₂ os₂''))
            (ds^ cs' (os₂^ ft₂ os₂''))
            js'
  ihS' = refl , refl , refl , ds^-eq , js'-eq

-- From Dybjer and Sander's paper: From the assumption that
-- os₂' ∈ Fair and hence by unfolding Fair, we conclude that there are
-- ft₂ : F*T and os₂'' : Fair, such that os₂' = ft₂ ++ os₂''.
--
-- We proceed by induction on ft₂ : F*T using helper.

lemma₂ : ∀ {b i' is' os₁' os₂' as' bs' cs' ds' js'} →
         Bit b →
         Fair os₁' →
         Fair os₂' →
         S' b i' is' os₁' os₂' as' bs' cs' ds' js' →
         ∃[ os₁'' ] ∃[ os₂'' ] ∃[ as'' ] ∃[ bs'' ] ∃[ cs'' ] ∃[ ds'' ]
           Fair os₁''
           ∧ Fair os₂''
           ∧ S (not b) is' os₁'' os₂'' as'' bs'' cs'' ds'' js'
lemma₂ Bb Fos₁' Fos₂' s' with Fair-out Fos₂'
... | ft , os₁'' , FTft , prf , Fos₁'' =
  helper Bb Fos₁' s' ft os₁'' FTft Fos₁'' prf
