{-# OPTIONS --safe #-}
module Foundations.Lens.Push.Universal where

open import Foundations.Base
open import Foundations.Cubical.HLevel.Base
open import Foundations.Lens.Push.Base

open import Notation.Refl

module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom}
  {C : HQuiver-onω m Ob ℓ-hom} (open Quiver-onω C renaming (Het to Hom))
  {k} {ℓ-obᶠ} {F : ob-sigᵈ Ob ℓ-obᶠ}
  {ℓ-homᶠ : ℓ-sig 3 (m , k , k , _)}
  {α : ∀{ls} (t : Ob ls) → HQuiver-onω k (F t) (ℓ-homᶠ ls)}
  ⦃ _ : Refl C ⦄ (hp : Push C k α) where
  private module α {ls} t = Quiver-onω (α {ls} t) renaming (Het to Hom)
  private instance _ = hp

  record is-universal⁺ {lxs lfs} {x : Ob lxs} (u : F x lfs) lys : Type
    (ℓ-ob lys ⊔ ℓ-hom lxs lys ⊔ ℓ-obᶠ lys lfs ⊔ ℓ-obᶠ lys lfs ⊔ ℓ-homᶠ lys lfs lfs) where
    no-eta-equality
    field
      unpush        : {y : Ob lys} (v : F y lfs) → Hom x y
      θ⁺            : {y : Ob lys} (v : F y lfs) → α.Hom y v (u ▷ unpush v)
      unpush-unique : {y : Ob lys} (v : F y lfs) → is-central {A = Σₜ (Hom x y) (λ f → α.Hom y v (u ▷ f))} (unpush v , θ⁺ v)

  is-universalω⁺ : ∀{lxs lfs} {x : Ob lxs} (u : F x lfs) → Typeω
  is-universalω⁺ u = ∀{lys} → is-universal⁺ u lys
