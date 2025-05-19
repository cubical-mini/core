{-# OPTIONS --safe #-}
module Notation.Invertibility.Section where

open import Prim.Kan
open import Prim.Type

open import Notation.Composition
open import Notation.Quiver
open import Notation.Reflexivity

module _ {ℓ-ob : ℓ-ob-sig} (Ob : ob-sig ℓ-ob)
  {ℓ-hom : ℓ-hom-sig} (Hom : hom-sig Ob ℓ-hom) ⦃ _ : Refl Ob Hom ⦄ ⦃ _ : Comp Ob Hom ⦄
  (_~_ : {ℓx ℓy : Level} {x : Ob ℓx} {y : Ob ℓy} (f g : Hom x y) → Type (ℓ-hom ℓx ℓy)) where

  weak-section : {ℓx ℓy : Level} {x : Ob ℓx} {y : Ob ℓy} (s : Hom x y) (r : Hom y x) → Type (ℓ-hom ℓx ℓx)
  weak-section s r = s ∙ r ＝ refl

  record has-weak-section {ℓx ℓy : Level} {x : Ob ℓx} {y : Ob ℓy} (r : Hom x y) : Type (ℓ-hom ℓy ℓx l⊔ ℓ-hom ℓy ℓy) where
    no-eta-equality
    field
      section    : Hom y x
      is-section : weak-section section r


module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} {Hom : hom-sig Ob ℓ-hom} ⦃ _ : Refl Ob Hom ⦄ ⦃ _ : Comp Ob Hom ⦄ where
  _section-of_ : {ℓx ℓy : Level} {x : Ob ℓx} {y : Ob ℓy} (s : Hom x y) (r : Hom y x) → Type (ℓ-hom ℓx ℓx)
  s section-of r = weak-section Ob Hom _＝_ s r
  {-# NOINLINE _section-of_ #-}

  has-section : {ℓx ℓy : Level} {x : Ob ℓx} {y : Ob ℓy} (r : Hom x y) → Type (ℓ-hom ℓy ℓx l⊔ ℓ-hom ℓy ℓy)
  has-section = has-weak-section Ob Hom _＝_
  {-# NOINLINE has-section #-}
