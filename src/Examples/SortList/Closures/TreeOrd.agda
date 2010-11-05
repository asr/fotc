------------------------------------------------------------------------------
-- Closures properties respect to TreeOrd
------------------------------------------------------------------------------

module Examples.SortList.Closures.TreeOrd where

open import LTC.Base

open import Examples.SortList.SortList
  using ( ≤-TreeItem-node
        ; ≤-ItemTree-node
        ; isTreeOrd
        ; LE-ItemTree
        ; LE-TreeItem
        ; makeTree
        ; nilTree ; node ; tip
        ; toTree
        ; Tree ; nilT ; nodeT ; tipT  -- The LTC tree type.
        ; TreeOrd
        )
open import Examples.SortList.Closures.Bool
  using ( ≤-ItemTree-Bool
        ; ≤-TreeItem-Bool
        ; isTreeOrd-Bool
        )
open import Examples.SortList.Closures.Tree using ( makeTree-Tree )

-- TODO: There is a bug with the importation in agda2atp.
open import LTC.Data.Bool using ()
open import LTC.Data.List using ()

open import LTC.Data.Bool.Properties
  using ( &&-Bool
        ; x&&y≡true→x≡true
        ; x&&y≡true→y≡true
        ; w&&x&&y&&z≡true→y≡true
        ; w&&x&&y&&z≡true→z≡true
        )
open import LTC.Data.Nat.Inequalities using ( GT ; LE )
open import LTC.Data.Nat.Inequalities.Properties
  using ( x<y→x≤y
        ; x>y→x≰y
        ; x>y∨x≤y
        ; x≤x
        )
open import LTC.Data.Nat.List.Type
  using ( ListN ; consLN ; nilLN  -- The LTC list of natural numbers type.
        )
open import LTC.Data.Nat.Type using ( N )

------------------------------------------------------------------------------
-- Subtrees

-- If (node t₁ i t₂) is ordered then t₁ is ordered.
postulate
  leftSubTree-TreeOrd : {t₁ i t₂ : D} → Tree t₁ → N i → Tree t₂ →
                        TreeOrd (node t₁ i t₂) → TreeOrd t₁
-- E 1.2 no-success due to timeout (180 sec).
{-# ATP prove leftSubTree-TreeOrd ≤-ItemTree-Bool ≤-TreeItem-Bool &&-Bool
                                  isTreeOrd-Bool x&&y≡true→x≡true
#-}

-- If (node t₁ i t₂) is ordered then t₂ is ordered.
postulate
  rightSubTree-TreeOrd : {t₁ i t₂ : D} → Tree t₁ → N i → Tree t₂ →
                         TreeOrd (node t₁ i t₂) → TreeOrd t₂
-- Equinox 5.0alpha (2010-03-29) need --time=720 for to prove this postulate.
-- E 1.2 no-success due to timeout (180 sec).
-- {-# ATP prove rightSubTree-TreeOrd ≤-ItemTree-Bool ≤-TreeItem-Bool &&-Bool
--                                   isTreeOrd-Bool x&&y≡true→x≡true
--                                   x&&y≡true→y≡true
-- #-}

------------------------------------------------------------------------------
-- Auxiliar functions

toTree-TreeOrd-aux₁ : {i₁ i₂ : D} → N i₁ → N i₂ → GT i₁ i₂ →
                      {t : D} → Tree t →
                      LE-TreeItem t i₁ →
                      LE-TreeItem (toTree ∙ i₂ ∙ t) i₁
toTree-TreeOrd-aux₁ {i₁} {i₂} Ni₁ Ni₂ i₁>i₂ .{nilTree} nilT t≤i₁ = prf
  where
    postulate prf : LE-TreeItem (toTree ∙ i₂ ∙ nilTree) i₁
    {-# ATP prove prf x<y→x≤y #-}

toTree-TreeOrd-aux₁ {i₁} {i₂} Ni₁ Ni₂ i₁>i₂ (tipT {j} Nj) t≤i₁ =
  [ prf₁ , prf₂ ] (x>y∨x≤y Nj Ni₂)
  where
    postulate prf₁ : GT j i₂ → LE-TreeItem (toTree ∙ i₂ ∙ tip j) i₁
    -- E 1.2 no-success due to timeout (180 sec).
    {-# ATP prove prf₁ x>y→x≰y x<y→x≤y #-}

    postulate prf₂ : LE j i₂ → LE-TreeItem (toTree ∙ i₂ ∙ tip j) i₁
    -- E 1.2 no-success due to timeout (180 sec).
    {-# ATP prove prf₂ x<y→x≤y #-}

toTree-TreeOrd-aux₁ {i₁} {i₂} Ni₁ Ni₂ i₁>i₂
                    (nodeT {t₁} {j} {t₂} Tt₁ Nj Tt₂) t≤i₁ =
  [ prf₁ (toTree-TreeOrd-aux₁ Ni₁ Ni₂ i₁>i₂ Tt₁
           (x&&y≡true→x≡true (≤-TreeItem-Bool Tt₁ Ni₁)
                             (≤-TreeItem-Bool Tt₂ Ni₁)
                             (trans (sym (≤-TreeItem-node t₁ j t₂ i₁))
                                    t≤i₁)))

  , prf₂ (toTree-TreeOrd-aux₁ Ni₁ Ni₂ i₁>i₂ Tt₂
           (x&&y≡true→y≡true (≤-TreeItem-Bool Tt₁ Ni₁)
                             (≤-TreeItem-Bool Tt₂ Ni₁)
                             (trans (sym (≤-TreeItem-node t₁ j t₂ i₁))
                                    t≤i₁)))
  ] (x>y∨x≤y Nj Ni₂)
  where
    postulate prf₁ : LE-TreeItem (toTree ∙ i₂ ∙ t₁) i₁ →  -- IH.
                     GT j i₂ →
                     LE-TreeItem (toTree ∙ i₂ ∙ node t₁ j t₂) i₁
    -- E 1.2 no-success due to timeout (180 sec).
    {-# ATP prove prf₁ x>y→x≰y x&&y≡true→y≡true ≤-TreeItem-Bool #-}

    postulate prf₂ : LE-TreeItem (toTree ∙ i₂ ∙ t₂) i₁ →  --IH.
                     LE j i₂ →
                     LE-TreeItem (toTree ∙ i₂ ∙ node t₁ j t₂) i₁
    -- E 1.2 no-success due to timeout (180 sec).
    {-# ATP prove prf₂ x&&y≡true→x≡true ≤-TreeItem-Bool #-}

toTree-TreeOrd-aux₂ : {i₁ i₂ : D} → N i₁ → N i₂ → LE i₁ i₂ →
                      {t : D} → Tree t →
                      LE-ItemTree i₁ t →
                      LE-ItemTree i₁ (toTree ∙ i₂ ∙ t)
toTree-TreeOrd-aux₂ {i₁} {i₂} _ _ i₁≤i₂ .{nilTree} nilT _ = prf
  where
    postulate prf : LE-ItemTree i₁ (toTree ∙ i₂ ∙ nilTree)
    {-# ATP prove prf #-}

toTree-TreeOrd-aux₂ {i₁} {i₂} Ni₁ Ni₂ i₁≤i₂ (tipT {j} Nj) i₁≤t =
  [ prf₁ , prf₂ ] (x>y∨x≤y Nj Ni₂)
  where
    postulate prf₁ : GT j i₂ → LE-ItemTree i₁ (toTree ∙ i₂ ∙ tip j)
    -- E 1.2 no-success due to timeout (180 sec).
    {-# ATP prove prf₁ x>y→x≰y #-}

    postulate prf₂ : LE j i₂ → LE-ItemTree i₁ (toTree ∙ i₂ ∙ tip j)
    -- E 1.2 no-success due to timeout (180 sec).
    {-# ATP prove prf₂ #-}

toTree-TreeOrd-aux₂ {i₁} {i₂} Ni₁ Ni₂ i₁≤i₂
                    (nodeT {t₁} {j} {t₂} Tt₁ Nj Tt₂) i₁≤t =
  [ prf₁ (toTree-TreeOrd-aux₂ Ni₁ Ni₂ i₁≤i₂ Tt₁
           (x&&y≡true→x≡true (≤-ItemTree-Bool Ni₁ Tt₁)
                             (≤-ItemTree-Bool Ni₁ Tt₂)
                             (trans (sym (≤-ItemTree-node i₁ t₁ j t₂))
                                    i₁≤t)))

  , prf₂ (toTree-TreeOrd-aux₂ Ni₁ Ni₂ i₁≤i₂ Tt₂
           (x&&y≡true→y≡true (≤-ItemTree-Bool Ni₁ Tt₁)
                             (≤-ItemTree-Bool Ni₁ Tt₂)
                             (trans (sym (≤-ItemTree-node i₁ t₁ j t₂))
                                    i₁≤t)))
  ] (x>y∨x≤y Nj Ni₂)
  where
    postulate prf₁ : LE-ItemTree i₁ (toTree ∙ i₂ ∙ t₁) →  -- IH.
                     GT j i₂ →
                     LE-ItemTree i₁ (toTree ∙ i₂ ∙ node t₁ j t₂)
    -- E 1.2 no-success due to timeout (180 sec).
    {-# ATP prove prf₁ ≤-ItemTree-Bool x>y→x≰y x&&y≡true→y≡true #-}

    postulate prf₂ : LE-ItemTree i₁ (toTree ∙ i₂ ∙ t₂) →  --IH.
                     LE j i₂ →
                     LE-ItemTree i₁ (toTree ∙ i₂ ∙ node t₁ j t₂)
    -- E 1.2 no-success due to timeout (180 sec).
    {-# ATP prove prf₂ ≤-ItemTree-Bool x&&y≡true→x≡true #-}

------------------------------------------------------------------------------
-- If t is ordered then (toTree i t) is ordered.
toTree-TreeOrd : {item t : D} → N item → Tree t → TreeOrd t →
                 TreeOrd (toTree ∙ item ∙ t)
toTree-TreeOrd {item} Nitem nilT _ = prf
  where
    postulate prf : TreeOrd (toTree ∙ item ∙ nilTree)
    {-# ATP prove prf #-}

toTree-TreeOrd {item} Nitem (tipT {i} Ni) TOtipT =
  [ prf₁ , prf₂ ] (x>y∨x≤y Ni Nitem)
  where
    postulate prf₁ : GT i item → TreeOrd (toTree ∙ item ∙ tip i)
    -- E 1.2 no-success due to timeout (180 sec).
    {-# ATP prove prf₁ x≤x x<y→x≤y x>y→x≰y #-}

    postulate prf₂ : LE i item → TreeOrd (toTree ∙ item ∙ tip i)
    -- E 1.2 no-success due to timeout (180 sec).
    {-# ATP prove prf₂ x≤x #-}

toTree-TreeOrd {item} Nitem (nodeT {t₁} {i} {t₂} Tt₁ Ni Tt₂) TOnodeT =
  [ prf₁ (toTree-TreeOrd Nitem Tt₁ (leftSubTree-TreeOrd Tt₁ Ni Tt₂ TOnodeT))
         (rightSubTree-TreeOrd Tt₁ Ni Tt₂ TOnodeT)
  , prf₂ (toTree-TreeOrd Nitem Tt₂ (rightSubTree-TreeOrd Tt₁ Ni Tt₂ TOnodeT))
         (leftSubTree-TreeOrd Tt₁ Ni Tt₂ TOnodeT)
  ] (x>y∨x≤y Ni Nitem)
  where
    postulate prf₁ : isTreeOrd (toTree ∙ item ∙ t₁) ≡ true →  -- IH.
                     TreeOrd t₂ →
                     GT i item →
                     TreeOrd (toTree ∙ item ∙ node t₁ i t₂)
    -- E 1.2 no-success due to timeout (180 sec).
    {-# ATP prove prf₁ ≤-ItemTree-Bool ≤-TreeItem-Bool isTreeOrd-Bool
                       x>y→x≰y w&&x&&y&&z≡true→y≡true w&&x&&y&&z≡true→z≡true
                       isTreeOrd-Bool toTree-TreeOrd-aux₁
    #-}

    postulate prf₂ : isTreeOrd (toTree ∙ item ∙ t₂) ≡ true → -- IH.
                     TreeOrd t₁ →
                     LE i item →
                     TreeOrd (toTree ∙ item ∙ node t₁ i t₂)
    -- E 1.2 no-success due to timeout (180 sec).
    {-# ATP prove prf₂ ≤-ItemTree-Bool ≤-TreeItem-Bool isTreeOrd-Bool
                       w&&x&&y&&z≡true→y≡true w&&x&&y&&z≡true→z≡true
                       toTree-TreeOrd-aux₂
    #-}

------------------------------------------------------------------------------
-- The function makeTree generates an ordered tree.
makeTree-TreeOrd : {is : D} → ListN is → TreeOrd (makeTree is)
makeTree-TreeOrd nilLN = prf
  where
    postulate prf : TreeOrd (makeTree [])
    {-# ATP prove prf #-}

makeTree-TreeOrd (consLN {i} {is} Ni Lis) = prf (makeTree-TreeOrd Lis)
  where
    postulate prf : TreeOrd (makeTree is) →  -- IH.
                    TreeOrd (makeTree (i ∷ is))
    -- E 1.2 no-success due to timeout (180 sec).
    {-# ATP prove prf makeTree-Tree toTree-TreeOrd #-}
