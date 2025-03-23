{-# OPTIONS --safe #-}

module Control.Nat.Base where

open import Prim.Type
open import Prim.Interval

open import Control.Functor.Base

_[_↦_] : ∀ {𝓤 𝓥} {A : Type 𝓤} (B : A → Type 𝓥) → A → A → Type 𝓥
B [ x ↦ y ] = B x → B y

NatT : ∀ {𝓤 𝓥 𝓦} {X : Type 𝓤}
     → (X → Type 𝓥) → (X → Type 𝓦) → Type (𝓤 ⊔ 𝓥 ⊔ 𝓦)
NatT A B = ∀ x → A x → B x

record NaturalTransformation {𝓤 𝓥 𝓦} {X : Type 𝓤}
  (A : X → Type 𝓥)
  (B : X → Type 𝓦)
  : Type (𝓤 ⊔ 𝓥 ⊔ 𝓦)
  where
  field
    η : ∀ x → A x → B x
    η₁ : ∀ {x y} → A [ x ↦ y ] → B [ x ↦ y ]
    η₁-coh : ∀ {x y} (F : A [ x ↦ y ])
           → η y ∘ F ≡ η₁ F ∘ η x
