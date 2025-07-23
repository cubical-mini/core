{-# OPTIONS --safe --erased-cubical #-}
module Foundations.Quiver.Discrete.Lens where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Discrete.Base
open import Foundations.Quiver.Discrete.Groupoid

open import Notation.Extend
open import Notation.Pull
open import Notation.Push

-- those are bad, use as a last resort
module _ {ℓa ℓb} {A : Type ℓa} {B : A → Type ℓb} where instance

  Disc-Push : HPush (Disc A) 0 (λ t → Disc (B t))
  Disc-Push .push p = transp (λ i → B (p i)) i0
  Disc-Push .push-refl {x} {u} i = transp (λ j → B x) (~ i) u

  Disc-Pull : HPull (Disc A) 0 λ t → Disc (B t)
  Disc-Pull .pull p = transp (λ i → B (p (~ i))) i0
  Disc-Pull .pull-refl {y} {v} i = transp (λ j → B y) i v

{-# INCOHERENT Disc-Push Disc-Pull #-}

-- FIXME restore
-- -- FIXME `f` is never inferred
-- module _ {ℓa} {A : Type ℓa} {m′} {ℓ-obᵈ} {Ob[_] : ob-sigᵈ {m = 0} (λ _ → A) ℓ-obᵈ} {ℓ-homᵈ}
--   {D : HQuiver-onωᵈ (Disc A) m′ Ob[_] ℓ-homᵈ} (open Quiver-onωᵈ D renaming (Het[_] to Hom[_]))
--   {f : ∀{lsᵈ} (x : A) → Ob[ x ] lsᵈ} where instance

-- --   Disc-Extend : Extend (Disc A) m′ (λ {x = x} {y = y} p lsᵈ → Hom[ p ] (f x) (f y))
-- --   Disc-Extend {lfs} .extend-l {x} {y} p =
-- --     transp (λ i → Hom[ (λ j → p (  i ∧ j)) ] {lfs} {lfs} (f x)         (f (p i))) i0
-- --   Disc-Extend {lfs} .extend-r {x} {y} p =
-- --     transp (λ i → Hom[ (λ j → p (~ i ∨ j)) ] {lfs} {lfs} (f (p (~ i))) (f y))     i0
