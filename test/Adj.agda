{-# OPTIONS --safe #-}
module Adj where

open import Prim.Interval
open import Prim.Kan
open import Prim.Type

open import Notation.Associativity
open import Notation.Adjoint
open import Notation.Base
open import Notation.Composition
open import Notation.Reasoning.Base
open import Notation.Reflexivity
open import Notation.Strict
open import Notation.Symmetry
open import Notation.Section
open import Notation.Split
open import Notation.Unitality.Inner
open import Notation.Unitality.Outer
open import Notation.Whiskering.Left
open import Notation.Whiskering.Right

open import Foundations.Pi.Interface
open import Foundations.Path.Interface

open Fun-cat
open Path-gpd
open Path-gpd0
module _ {ℓa ℓb} {A : Type ℓa} {B : Type ℓb} {f : A → B} {g : B → A} {θ : f ⊣ g} where
  η : idₜ ＝ g ∘ₜ f
  η = θ .Adjoint.η

  ε : f ∘ₜ g ＝ idₜ
  ε = θ .Adjoint.ε

  opaque
   unfolding _∙ₚ_
   zig : (x : A) → ap f (happly η x) ∙ happly ε (f x) ＝ refl
   zig x =
     ap f (happly η x) ∙ happly ε (f x)                       ~⟨ id-o _ ▷ happly ε (f x) ⟩
     ap f (happly η x) ∙ refl ∙ happly ε (f x)                ~⟨ id-i _ ⟩
     refl ∙ (ap f (happly η x) ∙ refl ∙ happly ε (f x))       ~⟨ assoc _ _ _ ∙ (assoc _ _ _ ▷ happly ε (f x)) ⟩
     refl ∙ ap f (happly η x) ∙ refl ∙ happly ε (f x)         ~⟨ id-o _ ⟩
     refl ∙ ap f (happly η x) ∙ refl ∙ happly ε (f x) ∙ refl  ~⟨ (λ i j → θ .Adjoint.zig i j x) ⟩
     refl                                                     ∎

  zig′ : (x : A) → sym (ap f (happly η x)) ＝ happly ε (f x)
  zig′ x =
    sym (ap f (happly η x))                                         ~⟨ id-o _ ⟩
    sym (ap f (happly η x)) ∙ refl                                  ~⟨ sym (ap f (happly η x)) ◁ zig x ⟨
    sym (ap f (happly η x)) ∙ (ap f (happly η x) ∙ happly ε (f x))  ~⟨ assoc _ _ _ ⟩
    sym (ap f (happly η x)) ∙ ap f (happly η x) ∙ happly ε (f x)    ~⟨ split ▷ happly ε (f x) ⟩
    refl ∙ happly ε (f x)                                           ~⟨ id-i _ ⟩
    happly ε (f x)                                                  ∎

  opaque
    unfolding _∙ₚ_
    zag : (y : B) → happly η (g y) ∙ ap g (happly ε y) ＝ refl
    zag y =
      happly η (g y) ∙ ap g (happly ε y)                       ~⟨ id-o _ ▷ ap g (happly ε y) ⟩
      happly η (g y) ∙ refl ∙ ap g (happly ε y)                ~⟨ id-i _ ⟩
      refl ∙ (happly η (g y) ∙ refl ∙ ap g (happly ε y))       ~⟨ assoc _ _ _ ∙ (assoc _ _ _ ▷ ap g (happly ε y)) ⟩
      refl ∙ happly η (g y) ∙ refl ∙ ap g (happly ε y)         ~⟨ id-o _ ⟩
      refl ∙ happly η (g y) ∙ refl ∙ ap g (happly ε y) ∙ refl  ~⟨ (λ i j → θ .Adjoint.zag i j y) ⟩
      refl                                                     ∎

  zag′ : (y : B) → ap g (happly ε y) ＝ sym (happly η (g y))
  zag′ y =
    ap g (happly ε y)                                            ~⟨ id-i _ ⟩
    refl ∙ ap g (happly ε y)                                     ~⟨ split ▷ ap g (happly ε y) ⟨
    sym (happly η (g y)) ∙ happly η (g y) ∙ ap g (happly ε y)    ~⟨ assoc _ _ _ ⟩
    sym (happly η (g y)) ∙ (happly η (g y) ∙ ap g (happly ε y))  ~⟨ sym (happly η (g y)) ◁ zag y ⟩
    sym (happly η (g y)) ∙ refl                                  ~⟨ id-o _ ⟩
    sym (happly η (g y))                                         ∎

-- module _ {ℓa ℓb} {A : Type ℓa} {B : Type ℓb} {f : A → B} {g : B → A}
--   {lr : f ∙ g ＝ refl} {rl : g ∙ f ＝ refl} where

--   -- funny af
--   kek : f ⊣ g
--   kek .Adjoint.η = sym lr
--   kek .Adjoint.ε = rl
--   kek .Adjoint.zig =
--     id-i f ∙ (sym lr ▷ f) ∙ assoc f g f ∙ (f ◁ rl) ∙ id-o f  ~⟨ id-o _ ⟩
--     id-i f ∙ (sym lr ▷ f) ∙ assoc f g f ∙ (f ◁ rl)           ~⟨ (sym (assoc _ _ _) ▷ f ◁ rl) ∙ assoc _ _ _ ⟩
--     id-i f ∙ ((sym lr ▷ f) ∙ assoc f g f ∙ (f ◁ rl))         ~⟨ id-i _ ⟩
--     (sym lr ▷ f) ∙ assoc f g f ∙ (f ◁ rl)                    ~⟨ id-o _ ▷ f ◁ rl ⟩
--     (sym lr ▷ f) ∙ (f ◁ rl)                                  ~⟨ {!!} ⟩
--     refl                                                     ∎
--   kek .Adjoint.zag = {!!}
