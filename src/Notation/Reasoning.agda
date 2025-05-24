{-# OPTIONS --safe #-}
module Notation.Reasoning where

open import Prim.Type

open import Notation.Base
open import Notation.Composition
open import Notation.Reflexivity
open import Notation.Symmetry

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} {C : Quiver-on Ob ℓ-hom} (open Quiver-on C) where

  infix 30 _∎
  _∎
    : {ℓ : Level} ⦃ _ : Refl C ℓ ⦄
      (x : Ob ℓ) → Hom x x
  _ ∎ = refl

  infixr 20 _~⟨⟩_
  _~⟨⟩_
    : ⦃ _ : Reflω C ⦄ -- for inference TODO check
      {ℓx ℓy : Level} (x : Ob ℓx) {y : Ob ℓy} → Hom x y → Hom x y
  _~⟨⟩_ _ xy = xy

  infixr 20 _~⟨_⟩_
  _~⟨_⟩_
    : {ℓx ℓy ℓz : Level} ⦃ _ : Comp C ℓx ℓy ℓz ⦄
      (x : Ob ℓx) {y : Ob ℓy} {z : Ob ℓz}
    → Hom x y → Hom y z → Hom x z
  _ ~⟨ x~y ⟩ y~z = x~y ∙ y~z

  infixr 20 _~⟨_⟨_
  _~⟨_⟨_
    : {ℓx ℓy ℓz : Level} ⦃ _ : Comp C ℓx ℓy ℓz ⦄ ⦃ _ : Symmetry C ℓy ℓx ⦄
      (x : Ob ℓx) {y : Ob ℓy} {z : Ob ℓz}
    → Hom y x → Hom y z → Hom x z
  x ~⟨ p ⟨ q = sym p ∙ q
