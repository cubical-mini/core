{-# OPTIONS --safe #-}
module Control.Diagram.Initial where

open import Prim.Kan
open import Prim.Type

open import Control.Composition
open import Control.Reflexivity
open import Control.Structures.Quiver

module _ (C : Quiver) {ℓi : Level} where
  open Quiver C

  is-initial : ∀ {ℓ} → Ob ℓi → Type (ob-lvl ℓ ⊔ hom-lvl ℓi ℓ)
  is-initial {ℓ} i = (x : Ob ℓ) → is-contr (Hom i x)

  record Initial : Typeω where
    no-eta-equality
    constructor mk-initial
    field
      ⊥           : Ob ℓi
      has-is-init : ∀ {ℓ} → is-initial {ℓ} ⊥

    ¡ : ∀ {ℓ} {x : Ob ℓ} → Hom ⊥ x
    ¡ {x} = has-is-init x .centre

{-# INLINE mk-initial #-}
open Initial ⦃ ... ⦄ public
  using (⊥; ¡)

{-# DISPLAY Initial.⊥ _ = ⊥ #-}


module _
  {C : Quiver} ⦃ _ : Refl C ⦄ ⦃ _ : Comp C ⦄
  {ℓi : Level} ⦃ _ : Initial C {ℓi} ⦄
  where
  open Quiver C

  infixr 0 ¬_
  ¬_ : {u : Level} → Ob u → Type (hom-lvl u ℓi)
  ¬ A = Hom A ⊥
