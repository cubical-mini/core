{-# OPTIONS --safe #-}
module Notation.Displayed.Symmetry where

open import Prim.Type

open import Notation.Base
open import Notation.Symmetry
open import Notation.Displayed.Base

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig} (C : Quiver-on Ob ℓ-hom) (open Quiver-on C)
  {ℓ-obᵈ : ℓ-ob-sig} {Ob[_] : ob-sigᵈ Ob ℓ-obᵈ} {ℓ-homᵈ : ℓ-hom-sig} (D : Quiver-onᵈ C Ob[_] ℓ-homᵈ) (open Quiver-onᵈ D)
  ⦃ _ : Symmetryω C ⦄
  where

 record Symᵈ ℓx ℓy
   : Type ( ℓ-ob ℓx l⊔ ℓ-ob ℓy l⊔ ℓ-hom ℓx ℓy l⊔ ℓ-obᵈ ℓx l⊔ ℓ-obᵈ ℓy
          l⊔ ℓ-homᵈ ℓx ℓy l⊔ ℓ-homᵈ ℓy ℓx) where
    no-eta-equality    
    field symᵈ : {x : Ob ℓx} {y : Ob ℓy}
                 {f : Hom x y}
                 {x′ : Ob[ x ]} {y′ : Ob[ y ]}
               → Hom[ f ] x′ y′ → Hom[ sym f ] y′ x′

open Symᵈ ⦃ ... ⦄ public

{-# DISPLAY Symᵈ.symᵈ _ f = symᵈ f #-}
