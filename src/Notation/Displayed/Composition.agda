{-# OPTIONS --safe #-}
module Notation.Displayed.Composition where

open import Prim.Type

open import Notation.Base
open import Notation.Composition
open import Notation.Displayed.Base

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig} (C : Quiver-on Ob ℓ-hom) (open Quiver-on C)
  {ℓ-obᵈ : ℓ-ob-sig} {Ob[_] : ob-sigᵈ Ob ℓ-obᵈ} {ℓ-homᵈ : ℓ-hom-sig} (D : Quiver-onᵈ C Ob[_] ℓ-homᵈ) (open Quiver-onᵈ D)
  ⦃ _ : Compω C ⦄
  where

 record Compᵈ ℓx ℓy ℓz
   : Type ( ℓ-ob ℓx l⊔ ℓ-ob ℓy l⊔ ℓ-ob ℓz l⊔ ℓ-hom ℓx ℓy l⊔ ℓ-hom ℓy ℓz
          l⊔ ℓ-obᵈ ℓx l⊔ ℓ-obᵈ ℓy l⊔ ℓ-obᵈ ℓz l⊔ ℓ-homᵈ ℓx ℓy
          l⊔ ℓ-homᵈ ℓx ℓz l⊔ ℓ-homᵈ ℓy ℓz) where
    no-eta-equality    
    infixl 90 _∙ᵈ_
    field _∙ᵈ_ : {x : Ob ℓx} {y : Ob ℓy} {z : Ob ℓz}
                 {f : Hom x y} {g : Hom y z}
                 {x′ : Ob[ x ]} {y′ : Ob[ y ]} {z′ : Ob[ z ]}
               → Hom[ f ] x′ y′ → Hom[ g ] y′ z′ → Hom[ f ∙ g ] x′ z′

open Compᵈ ⦃ ... ⦄ public

{-# DISPLAY Compᵈ._∙ᵈ_ _ f g = f ∙ᵈ g #-}
