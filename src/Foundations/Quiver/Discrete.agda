{-# OPTIONS --safe --erased-cubical #-}
module Foundations.Quiver.Discrete where

open import Prim.Interval public
open import Prim.Kan public

open import Foundations.Quiver.Base

open import Notation.Extend
open import Notation.Refl

module _ {ℓ} (A : I → Type ℓ) where
  Δ : Quiver-onω 0 0 (λ _ → A i0) (λ _ → A i1) (λ _ _ → ℓ)
  Δ .Quiver-onω.Het = Pathᴾ A

  ∇ : Quiver-onω 0 0 (λ _ → A i0) (λ _ → A i1) (λ _ _ → lzero)
  ∇ .Quiver-onω.Het _ _ = ⊤

Disc : ∀{ℓ} (A : Type ℓ) → HQuiver-onω 0 (λ _ → A) (λ _ _ → ℓ)
Disc A = Δ λ _ → A

Codisc : ∀{ℓ} (A : Type ℓ) → HQuiver-onω 0 (λ _ → A) (λ _ _ → lzero)
Codisc A = ∇ λ _ → A

instance
  Disc-Refl : ∀{ℓ} {A : Type ℓ} → Reflω (Disc A)
  Disc-Refl .refl {x} _ = x

  Codisc-Refl : ∀{ℓ} {A : Type ℓ} → Reflω (Codisc A)
  Codisc-Refl .refl = tt

module _ {ℓa} {A : Type ℓa} {m′} {ℓ-obᵈ ℓ-homᵈ} {Ob[_] : ob-sigᵈ {m = 0} (λ _ → A) ℓ-obᵈ}
  {D : HQuiver-onωᵈ {m = 0} (λ _ → A) _＝_ m′ Ob[_] ℓ-homᵈ} (open Quiver-onωᵈ D renaming (Het[_] to Hom[_]))
  {f : ∀{lsᵈ} (x : A) → Ob[ x ] lsᵈ} where instance

  -- TODO do not use builtin transport
  Disc-Extend : Extendω (Disc A) m′ (λ {x = x} {y = y} p lsᵈ → Hom[ p ] (f x) (f y))
  Disc-Extend {lfs} .extend-l {x} {y} p =
    transp (λ i → Hom[ (λ j → p (  i ∧ j)) ] {lfs} {lfs} (f x)         (f (p i))) i0
  Disc-Extend {lfs} .extend-r {x} {y} p =
    transp (λ i → Hom[ (λ j → p (~ i ∨ j)) ] {lfs} {lfs} (f (p (~ i))) (f y))     i0
