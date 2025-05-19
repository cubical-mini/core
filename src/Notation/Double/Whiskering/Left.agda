{-# OPTIONS --safe #-}
module Notation.Double.Whiskering.Left where

open import Prim.Type

open import Notation.Composition
open import Notation.Double.Composition
open import Notation.Double.Quiver
open import Notation.Quiver
open import Notation.Reflexivity

module _ {ℓ-ob : ℓ-ob-sig} (Ob : ob-sig ℓ-ob) {ℓ-hom□ : ℓ-square-sig}
  {Homₕ : hom-sig Ob (ℓ-homₕ ℓ-hom□)} ⦃ _ : Comp Ob Homₕ ⦄
  {Homᵥ : hom-sig Ob (ℓ-homᵥ ℓ-hom□)} ⦃ _ : Refl Ob Homᵥ ⦄
  (Hom□ : square-sig Ob Homₕ Homᵥ ℓ-hom□)
  where

  record 𝕎hisker-l : Typeω where
    no-eta-equality
    infixr 24 _◁_
    field _◁_ : {ℓw ℓx ℓy ℓz : Level} {w : Ob ℓw} {x : Ob ℓx} (f : Homₕ w x)
                {y : Ob ℓy} {g : Homₕ x y} {z : Ob ℓz} {h : Homᵥ y z} {k : Homₕ x z}
              → Hom□ g refl h k
              → Hom□ (f ∙ g) refl h (f ∙ k)

open 𝕎hisker-l ⦃ ... ⦄ public

{-# DISPLAY 𝕎hisker-l._◁_ _ f α = f ◁ α #-}

-- TODO composition -> whiskering
