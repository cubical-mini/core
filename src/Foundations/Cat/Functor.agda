{-# OPTIONS --safe #-}
module Control.Functor where

open import Lib.Base

module _ {C D : Quiver} where
  module C = Quiver C
  module D = Quiver D

  record QFunctor : Typeω where
    no-eta-equality
    field
      F₀ : ∀ {ℓ} → C.Ob ℓ → D.Ob ℓ
      F₁ : {ℓx ℓy : Level} {x : C.Ob ℓx} {y : C.Ob ℓy} → C.Hom x y → D.Hom (F₀ x) (F₀ y)

  module _ ⦃ _ : Comp C ⦄ ⦃ _ : Comp D ⦄ where
    record Semifunctorial (F : QFunctor) : Typeω where
      no-eta-equality
      open QFunctor F
      field pres-∙ : {ℓx ℓy ℓz : Level} {x : C.Ob ℓx} {y : C.Ob ℓy} {z : C.Ob ℓz}
                     (f : C.Hom x y) (g : C.Hom y z)
                   → F₁ (f ∙ g) ≡ F₁ f ∙ F₁ g
