{-# OPTIONS --safe #-}
module Foundations.Quiver.Lens.Push.Universal.Element where

open import Foundations.HLevel.Base
open import Foundations.Quiver.Base
open import Foundations.Quiver.Lens.Push.Base

module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom}
  {C : HQuiver-onω m Ob ℓ-hom} (open Quiver-onω C renaming (Het to Hom))
  {k} {ℓ-obᶠ} {F : ob-sigᵈ Ob ℓ-obᶠ}
  {ℓ-homᶠ : ℓ-sig 3 (m , k , k , _)}
  {α : ∀{ls} (t : Ob ls) → HQuiver-onω k (F t) (ℓ-homᶠ ls)}
  (hp : Push C k α) where
  private module α {ls} t = Quiver-onω (α {ls} t) renaming (Het to Hom)
  private instance _ = hp

  record Universal⁺ {lxs lfs} {x : Ob lxs} (u : F x lfs) lys : Typeω where
    no-eta-equality
    field
      unpush        : {y : Ob lys} (v : F y lfs) → Hom x y
      θ⁺            : {y : Ob lys} (v : F y lfs) → α.Hom y v (u ▷ unpush v)
      unpush-unique : {y : Ob lys} (v : F y lfs) → is-central⁺ (Σₜ (Hom x y) (λ f → α.Hom y v (u ▷ f))) (unpush v , θ⁺ v)

  Universalω⁺ : ∀{lxs lfs} {x : Ob lxs} (u : F x lfs) → Typeω
  Universalω⁺ u = ∀{lys} → Universal⁺ u lys
