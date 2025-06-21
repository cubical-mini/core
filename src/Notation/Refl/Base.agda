{-# OPTIONS --safe #-}
module Notation.Refl.Base where

open import Notation.Base

module _ {n : ℕ} {ℓ-obω : ℓ-sig n} {ℓ-homω : ℓ-sig² n}
  (C : Quiverω n ℓ-obω ℓ-homω) (open Quiverω C) where

  record Refl (ls : Levels n) : Type (ℓ-ob ℓ-obω ls ⊔ ℓ-hom ℓ-obω ℓ-obω ℓ-homω ls ls) where
    no-eta-equality
    field refl : ∀ x → Hom {lys = ls} x x

  Reflω : Typeω
  Reflω = ∀ {ls} → Refl ls

open Refl ⦃ ... ⦄ public
{-# DISPLAY Refl.refl _ = refl #-}


module _ {n : ℕ} {ℓ-obω : ℓ-sig n} {ℓ-homω : ℓ-sig² n}
  (C : Quiverω n ℓ-obω ℓ-homω) (open Quiverω C)
  {m : ℕ} {ℓ-obωᵈ : ℓ-sig (n + m)} {ℓ-homωᵈ : ℓ-sig² (n + m)}
  (D : Quiverωᵈ C m ℓ-obωᵈ ℓ-homωᵈ) (open Quiverωᵈ D)
  (ls : Levels n) ⦃ _ : Refl C ls ⦄
  where

  record Reflᵈ (lsᵈ : Levels m) : Type
    ( ℓ-ob ℓ-obω ls ⊔ ℓ-obᵈ ℓ-obω ℓ-obωᵈ ls lsᵈ
    ⊔ ℓ-homᵈ ℓ-obω ℓ-obω ℓ-homω ℓ-obωᵈ ℓ-obωᵈ ℓ-homωᵈ ls ls lsᵈ lsᵈ) where
    no-eta-equality
    field reflᵈ : ∀{x} (x′ : Ob[ x ] lsᵈ) → Hom[ refl x ] x′ x′

  Reflωᵈ = ∀ {lsᵈ} → Reflᵈ lsᵈ

open Reflᵈ ⦃ ... ⦄ public
{-# DISPLAY Reflᵈ.reflᵈ _ = reflᵈ #-}


-- displayed quiver over a reflexive quiver begets a family of _small_ quivers
module _ {n : ℕ} {ℓ-obω : ℓ-sig n} {ℓ-homω : ℓ-sig² n}
  {C : Quiverω n ℓ-obω ℓ-homω} (open Quiverω C)
  {m : ℕ} {ℓ-obωᵈ : ℓ-sig (n + m)} {ℓ-homωᵈ : ℓ-sig² (n + m)}
  (D : Quiverωᵈ C m ℓ-obωᵈ ℓ-homωᵈ) (open Quiverωᵈ D)
  where

  module _ {ls : Levels n} ⦃ _ : Refl C ls ⦄ (t : Ob ls) (lsᵈ : Levels m) where
    Component : Quiverω 0 (ℓ-obᵈ ℓ-obω ℓ-obωᵈ ls lsᵈ) (ℓ-homᵈ ℓ-obω ℓ-obω ℓ-homω ℓ-obωᵈ ℓ-obωᵈ ℓ-homωᵈ ls ls lsᵈ lsᵈ) 
    Component .Quiverω.Obω .lowerω = Ob[ t ] lsᵈ
    Component .Quiverω.Homω .lowerω = Hom[ refl t ]
