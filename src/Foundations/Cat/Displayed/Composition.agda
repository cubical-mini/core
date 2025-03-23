{-# OPTIONS --safe #-}
module Control.Displayed.Composition where

open import Prim.Type

open import Control.Structures.Quiver
open import Control.Composition

module _ {Q : Quiver} ⦃ _ : Comp Q ⦄ where
  open Quiver Q

  module _
    {ob-lvlᴰ : Level → Level }
    {hom-lvlᴰ : Level → Level → Level }
    (Ob[_] : ∀ {ℓ} → Ob ℓ → Type (ob-lvlᴰ ℓ))
    (Hom[_] : {ℓx ℓy : Level} {x : Ob ℓx} {y : Ob ℓy} → Hom x y → Ob[ x ] → Ob[ y ] → Type (hom-lvlᴰ ℓx ℓy))
    where

    record Compᴰ : Typeω where
      no-eta-equality
      infixl 90 _∙ᴰ_
      field _∙ᴰ_ : {ℓx ℓy ℓz : Level} {x : Ob ℓx} {y : Ob ℓy} {z : Ob ℓz}
                   {f : Hom x y} {g : Hom y z}
                   {x′ : Ob[ x ]} {y′ : Ob[ y ]} {z′ : Ob[ z ]}
                 → Hom[ f ] x′ y′ → Hom[ g ] y′ z′ → Hom[ f ∙ g ] x′ z′

      infixr 90 _∘ᴰ_
      _∘ᴰ_ : {ℓx ℓy ℓz : Level} {x : Ob ℓx} {y : Ob ℓy} {z : Ob ℓz}
             {f : Hom x y} {g : Hom y z}
             {x′ : Ob[ x ]} {y′ : Ob[ y ]} {z′ : Ob[ z ]}
           → Hom[ g ] y′ z′ → Hom[ f ] x′ y′ → Hom[ g ∘ f ] x′ z′
      f ∘ᴰ g = g ∙ᴰ f

open Compᴰ ⦃ ... ⦄ public

{-# DISPLAY Compᴰ._∙ᴰ_ _ f g = f ∙ᴰ g #-}
{-# DISPLAY Compᴰ._∘ᴰ_ _ f g = f ∘ᴰ g #-} -- remove?
