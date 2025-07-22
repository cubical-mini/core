{-# OPTIONS --safe --erased-cubical #-}
module Foundations.Quiver.Discrete.Lens where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Discrete.Base
open import Foundations.Quiver.Discrete.Groupoid

open import Notation.Extend
open import Notation.Pull
open import Notation.Push

-- those are bad, use as a last resort
module _ {ℓa} {A : Type ℓa} {m′} {ℓ-obᵈ : ℓ-sig 2 (0 , m′ , _)}
  {F : ob-sigᵈ {m = 0} (λ _ → A) ℓ-obᵈ} where instance

  Disc-Push : HPushω (Disc A) m′ F
  Disc-Push {lfs} .push p = transp (λ i → F (p i) lfs) i0

  Disc-Pull : HPullω (Disc A) m′ F
  Disc-Pull {lfs} .pull p = transp (λ i → F (p (~ i)) lfs) i0

{-# INCOHERENT Disc-Push Disc-Pull #-}

-- FIXME `f` is never inferred
module _ {ℓa} {A : Type ℓa} {m′} {ℓ-obᵈ ℓ-homᵈ} {Ob[_] : ob-sigᵈ {m = 0} (λ _ → A) ℓ-obᵈ}
  {D : HQuiver-onωᵈ {m = 0} (λ _ → A) _＝_ m′ Ob[_] ℓ-homᵈ} (open Quiver-onωᵈ D renaming (Het[_] to Hom[_]))
  {f : ∀{lsᵈ} (x : A) → Ob[ x ] lsᵈ} where instance

  Disc-Extend : Extendω (Disc A) m′ (λ {x = x} {y = y} p lsᵈ → Hom[ p ] (f x) (f y))
  Disc-Extend {lfs} .extend-l {x} {y} p =
    transp (λ i → Hom[ (λ j → p (  i ∧ j)) ] {lfs} {lfs} (f x)         (f (p i))) i0
  Disc-Extend {lfs} .extend-r {x} {y} p =
    transp (λ i → Hom[ (λ j → p (~ i ∨ j)) ] {lfs} {lfs} (f (p (~ i))) (f y))     i0
