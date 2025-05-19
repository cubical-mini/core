{-# OPTIONS --safe #-}
module Notation.Invertibility.Retraction where

open import Prim.Kan
open import Prim.Type

open import Notation.Composition
open import Notation.Quiver
open import Notation.Reflexivity

module _ {ℓ-ob : ℓ-ob-sig} (Ob : ob-sig ℓ-ob)
  {ℓ-hom : ℓ-hom-sig} (Hom : hom-sig Ob ℓ-hom) ⦃ _ : Refl Ob Hom ⦄ ⦃ _ : Comp Ob Hom ⦄
  (_~_ : {ℓx ℓy : Level} {x : Ob ℓx} {y : Ob ℓy} (f g : Hom x y) → Type (ℓ-hom ℓx ℓy)) where

  weak-retraction : {ℓx ℓy : Level} {x : Ob ℓx} {y : Ob ℓy} (r : Hom x y) (s : Hom y x) → Type (ℓ-hom ℓy ℓy)
  weak-retraction r s = s ∙ r ~ refl

  record has-weak-retraction {ℓx ℓy : Level} {x : Ob ℓx} {y : Ob ℓy} (s : Hom x y) : Type (ℓ-hom ℓy ℓx l⊔ ℓ-hom ℓx ℓx) where
    no-eta-equality
    field
      retraction    : Hom y x
      is-retraction : weak-retraction retraction s


module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob}
  {ℓ-hom : ℓ-hom-sig} {Hom : hom-sig Ob ℓ-hom} ⦃ _ : Refl Ob Hom ⦄ ⦃ _ : Comp Ob Hom ⦄ where
  _retraction-of_ : {ℓx ℓy : Level} {x : Ob ℓx} {y : Ob ℓy} (r : Hom x y) (s : Hom y x) → Type (ℓ-hom ℓy ℓy)
  r retraction-of s = weak-retraction Ob Hom _＝_ r s
  {-# NOINLINE _retraction-of_ #-}

  has-retraction : {ℓx ℓy : Level} {x : Ob ℓx} {y : Ob ℓy} (s : Hom x y) → Type (ℓ-hom ℓy ℓx l⊔ ℓ-hom ℓx ℓx)
  has-retraction = has-weak-retraction Ob Hom _＝_
  {-# NOINLINE has-retraction #-}
