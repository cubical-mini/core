{-# OPTIONS --safe #-}
module Yoneda where

open import Prim.Kan
open import Prim.Type

open import Notation.Associativity
open import Notation.Base
open import Notation.Composition
open import Notation.Reflexivity
open import Notation.Symmetry
open import Notation.Unitality.Inner
open import Notation.Unitality.Outer

open import Foundations.Path.Groupoid
open import Foundations.Pi.Category
open import Foundations.Representable

module _ {ℓo ℓh : Level} {Ob : Type ℓo}
  (C : Small-quiver-on Ob ℓh) (open Small-quiver-on C)
  ⦃ _ : Refl (Enlarge C) lzero ⦄ ⦃ _ : Comp (Enlarge C) lzero lzero lzero ⦄ ⦃ pa : Parametric C ⦄ where

  Yoneda-Hom : (x y : Ob) → Type (ℓo l⊔ ℓh)
  Yoneda-Hom = Hom-action C

  Yo : Small-quiver-on Ob (ℓo l⊔ ℓh)
  Yo .Small-quiver-on.Hom x y = Yoneda-Hom x y

  reflʸ : {x : Ob}
        → Yoneda-Hom x x
  reflʸ = λ _ f → f

  _∙ʸ_ : {x y z : Ob}
       → Yoneda-Hom x y → Yoneda-Hom y z → Yoneda-Hom x z
  α ∙ʸ β = λ t f → β t (α t f)

  instance
    Yo-Refl : Reflω (Enlarge Yo)
    Yo-Refl .refl = reflʸ

    Yo-Comp : Compω (Enlarge Yo)
    Yo-Comp ._∙_ = _∙ʸ_

    Yo-Assoc : Assocω (Enlarge Yo) Strictω
    Yo-Assoc .assoc _ _ _ = reflₚ

    Yo-Unit-i : Unit-iω (Enlarge Yo) Strictω
    Yo-Unit-i .id-i _ = reflₚ

    Yo-Unit-o : Unit-oω (Enlarge Yo) Strictω
    Yo-Unit-o .id-o _ = reflₚ
    {-# OVERLAPPING
      Yo-Refl Yo-Comp
      Yo-Assoc Yo-Unit-i Yo-Unit-o
    #-}

  inject : {x y : Ob}
         → Hom x y
         → Yoneda-Hom x y
  inject f _ = _∙ f

  extract : {x y : Ob}
          → Yoneda-Hom x y
          → Hom x y
  extract {x} h = h x refl

  one-two : {x y : Ob}
            ⦃ _ : Unit-i (Enlarge C) Strictω lzero lzero ⦄
          → (f : Hom x y)
          → extract (inject f) ＝ f
  one-two = id-i

  two-one : {x y : Ob}
          → (h : Yoneda-Hom x y)
          → inject (extract h) ＝ h
  two-one h = fun-ext λ a → fun-ext (pa .param h)


module Strictification {ℓ : Level} {Ob : Type ℓ}
  (C : Small-quiver-on Ob ℓ) (open Small-quiver-on C)
  ⦃ _ : Refl (Enlarge C) lzero ⦄ ⦃ _ : Comp (Enlarge C) lzero lzero lzero ⦄ ⦃ pa : Parametric C ⦄ where
  open import Foundations.Path.Transport

  -- at last
  -- strictify : ∀{ℓp} (P : Small-quiver-on Ob ℓ → Type ℓp) → P (Yo C) → P C
  -- strictify P = subst P {!!}
