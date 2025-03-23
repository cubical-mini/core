```agda

{-# OPTIONS --safe #-}

module Prim.Glue where

open import Prim.Base
  using ( Type; I; i0; i1; 1=1; Partial; PartialP; _≃ᶠ_; module Prim )
open import Prim.Kan using ( _[_↦_]; outS )
open import Prim.Data.Sigma using ( Sigma; fst; snd )

open Prim public
  using ()
  renaming ( prim^glue to glue )

-- Uncurry Glue to make it more pleasant to use
@0 Glue : ∀ {ℓ ℓ'} (A : Type ℓ)
          {φ : I}
        → (Te : Partial φ (Sigma (Type ℓ') λ T → T ≃ᶠ A))
        → Type ℓ'
Glue A Te = Prim.primGlue A (λ x → Te x .fst) (λ x → Te x .snd)

-- Make the φ argument of prim^unglue explicit
@0 unglue : ∀ {ℓ ℓ'} {A : Type ℓ} (φ : I) {T : Partial φ (Type ℓ')}
            {e : PartialP φ (λ o → T o ≃ᶠ A)}
          → Prim.primGlue A T e → A
unglue φ = Prim.prim^unglue {φ = φ}

@0 glue-inc : ∀ {ℓ ℓ'} {A : Type ℓ} (φ : I)
            → {Tf : Partial φ (Sigma (Type ℓ') λ B → B ≃ᶠ A)}
            → (p : PartialP φ (λ { (φ = i1) → Tf 1=1 .fst }))
            → A [ φ ↦ (λ { (φ = i1) → Tf 1=1 .snd .fst (p 1=1) }) ]
            → Glue A Tf
glue-inc φ p x = glue {φ = φ} p (outS x)
