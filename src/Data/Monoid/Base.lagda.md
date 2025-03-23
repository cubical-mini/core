```agda

module Data.Monoid.Base where

open import Prim.Base.Type
open import Prim.Pi renaming (comp to _∘_)
open import Prim.Path using ( _≡_ )

record Functor {𝓤 𝓥} (F : Type 𝓤 → Type 𝓥) : Type (𝓤 ₊ ⊔ 𝓥) where
  field
    fmap : ∀ {A B} → (A → B) → F A → F B
    fmap-idn : ∀ {A} → fmap (idfun A) ≡ idfun (F A)
    fmap-hom : ∀ {A B C} (f : A → B) (g : B → C)
             → fmap (g ∘ f) ≡ fmap g ∘ fmap f
