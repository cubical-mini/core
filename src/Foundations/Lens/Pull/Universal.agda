{-# OPTIONS --safe #-}
module Foundations.Lens.Pull.Universal where

open import Foundations.Base
open import Foundations.Cubical.HLevel.Base
open import Foundations.Lens.Pull.Base

open import Notation.Refl

module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom}
  {C : HQuiver-onω m Ob ℓ-hom} (open Quiver-onω C renaming (Het to Hom))
  {k} {ℓ-obᶠ} {F : ob-sigᵈ Ob ℓ-obᶠ}
  {ℓ-homᶠ : ℓ-sig 3 (m , k , k , _)}
  {α : ∀{ls} (t : Ob ls) → HQuiver-onω k (F t) (ℓ-homᶠ ls)}
  ⦃ _ : Refl C ⦄ (hp : Pull C k α) where
  private module α {ls} t = Quiver-onω (α {ls} t) renaming (Het to Hom)
  private instance _ = hp

  record is-universal⁻ {lys lfs} {y : Ob lys} (v : F y lfs) lxs : Type
    (ℓ-ob lxs ⊔ ℓ-hom lxs lys ⊔ ℓ-obᶠ lxs lfs ⊔ ℓ-homᶠ lxs lfs lfs) where
    no-eta-equality
    field
      unpull        : {x : Ob lxs} (u : F x lfs) → Hom x y
      θ⁻            : {x : Ob lxs} (u : F x lfs) → α.Hom x (unpull u ◁ v) u
      unpull-unique : {x : Ob lxs} (u : F x lfs) → is-central⁻ (Σₜ (Hom x y) (λ f → α.Hom x (f ◁ v) u)) (unpull u , θ⁻ u)

  is-universalω⁻ : ∀{lys lfs} {y : Ob lys} (v : F y lfs) → Typeω
  is-universalω⁻ v = ∀{lxs} → is-universal⁻ v lxs
