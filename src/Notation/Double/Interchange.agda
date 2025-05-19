{-# OPTIONS --safe #-}
module Notation.Double.Interchange where

open import Prim.Type

open import Notation.Composition
open import Notation.Double.Composition
open import Notation.Double.Quiver
open import Notation.Quiver

module _ {ℓ-ob : ℓ-ob-sig} (Ob : ob-sig ℓ-ob) {ℓ-hom□ : ℓ-square-sig}
  {Homₕ : hom-sig Ob (ℓ-homₕ ℓ-hom□)} ⦃ _ : Comp Ob Homₕ ⦄
  {Homᵥ : hom-sig Ob (ℓ-homᵥ ℓ-hom□)} ⦃ _ : Comp Ob Homᵥ ⦄
  (Hom□ : square-sig Ob Homₕ Homᵥ ℓ-hom□) ⦃ _ : ℂomp Ob Hom□ ⦄
  (_~_ : {ℓw ℓx ℓy ℓz : Level} {w : Ob ℓw} {x : Ob ℓx} {f : Homₕ w x} {y : Ob ℓy} {g : Homᵥ w y} {z : Ob ℓz} {h : Homᵥ x z} {k : Homₕ y z} (α β : Hom□ f g h k) → Type (ℓ-hom□ ℓw ℓx ℓy ℓz)) where

  record 𝕀nterchange : Typeω where
    no-eta-equality
    field
      interchange : {ℓa ℓb ℓc ℓd ℓe ℓf ℓg ℓh ℓk : Level}
                    {A : Ob ℓa} {B : Ob ℓb} {f : Homₕ A B} {C : Ob ℓc} {g : Homᵥ A C} {D : Ob ℓd}
                    {h : Homᵥ B D} {k : Homₕ C D} (α : Hom□ f g h k)
                    {E : Ob ℓe} {l : Homₕ B E} {F : Ob ℓf}
                    {m : Homᵥ E F} {n : Homₕ D F} (β : Hom□ l h m n)
                    {G : Ob ℓg} {o : Homᵥ C G} {H : Ob ℓh}
                    {p : Homᵥ D H} {q : Homₕ G H} (γ : Hom□ k o p q)
                    {K : Ob ℓk} {r : Homᵥ F K} {s : Homₕ H K} (δ : Hom□ n p r s)
                  → (α ∙ᵥ γ) ∙ₕ (β ∙ᵥ δ) ~ (α ∙ₕ β) ∙ᵥ (γ ∙ₕ δ)

open 𝕀nterchange ⦃ ... ⦄ public

{-# DISPLAY 𝕀nterchange.interchange _ α β γ δ = interchange α β γ δ #-}
