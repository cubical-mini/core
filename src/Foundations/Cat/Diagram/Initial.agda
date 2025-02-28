{-# OPTIONS --safe #-}
module Foundations.Cat.Diagram.Initial where

open import Foundations.Prim.Kan
open import Foundations.Prim.Type

open import Foundations.Cat.Composition
open import Foundations.Cat.Reflexivity

module _
  {ob-lvl : Level → Level}
  {hom-lvl : Level → Level → Level}
  (Ob  : (ℓ : Level) → Type (ob-lvl ℓ))
  (Hom : {ℓx ℓy : Level} → Ob ℓx → Ob ℓy → Type (hom-lvl ℓx ℓy))
  {ℓi : Level}
  where

  is-initial : {ℓ : Level} → Ob ℓi → Type (ob-lvl ℓ l⊔ hom-lvl ℓi ℓ)
  is-initial {ℓ} i = (x : Ob ℓ) → is-contr (Hom i x)

  record Initial : Typeω where
    no-eta-equality
    constructor mk-initial
    field
      ⊥           : Ob ℓi
      has-is-init : {ℓ : Level} → is-initial {ℓ} ⊥

    ¡ : {ℓ : Level} {x : Ob ℓ} → Hom ⊥ x
    ¡ {x} = has-is-init x .centre

{-# INLINE mk-initial #-}
open Initial ⦃ ... ⦄ public
  using (⊥; ¡)

{-# DISPLAY Initial.⊥ _ = ⊥ #-}


module _
  {ob-lvl : Level → Level}
  {hom-lvl : Level → Level → Level}
  {Ob  : (ℓ : Level) → Type (ob-lvl ℓ)}
  {Hom : {ℓx ℓy : Level} → Ob ℓx → Ob ℓy → Type (hom-lvl ℓx ℓy)}
  ⦃ _ : Refl Ob Hom ⦄ ⦃ _ : Comp Ob Hom ⦄
  {ℓi : Level} ⦃ _ : Initial Ob Hom {ℓi} ⦄
  where

  infixr 0 ¬_
  ¬_ : {ℓa : Level} → Ob ℓa → Type (hom-lvl ℓa ℓi)
  ¬ A = Hom A ⊥
