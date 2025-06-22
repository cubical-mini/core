{-# OPTIONS --safe --erased-cubical #-}
module Foundations.Quiver.Univalent where

open import Prim.Kan

open import Foundations.Quiver.Base

open import Notation.Refl

module _ {n : ℕ} {ℓ-obω : ℓ-sig n} {ℓ-homω : ℓ-sig² n}
  (C : Quiverω n ℓ-obω ℓ-homω) (open Quiverω C) ⦃ _ : Reflω C ⦄ where

  record is-univalent ls : Typeω where
    no-eta-equality
    field
      to-path : {x y : Ob ls} → Hom x y → x ＝ y
      to-path-over : {x y : Ob ls} (p : Hom x y)
                   → Pathᴾ (λ i → Hom x (to-path p i)) refl p

  is-univalentω : Typeω
  is-univalentω = ∀{ls} → is-univalent ls
