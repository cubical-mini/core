{-# OPTIONS --safe #-}
module Foundations.Prim.Glue where

open import Foundations.Prim.Equiv
open import Foundations.Prim.Interval
open import Foundations.Prim.Kan
open import Foundations.Prim.Type

open import Agda.Builtin.Cubical.Glue
  using ( primGlue     -- ∀ {ℓ ℓ′} (A : Type ℓ) {φ : I} (T : Partial φ (Type ℓ′))
                       -- → (e : PartialP φ (λ o → T o ≃′ A)) → Type ℓ′
        ; prim^unglue  -- ∀ {ℓ ℓ′} {A : Type ℓ} {φ : I} {T : Partial φ (Type ℓ′)}
                       -- → {e : PartialP φ (λ o → T o ≃′ A)} → primGlue A T e → A
        )
open import Agda.Builtin.Cubical.Glue public
  using ()
  renaming ( prim^glue to glue -- ∀ {ℓ ℓ′} {A : Type ℓ} {φ : I} {T : Partial φ (Type ℓ′)}
                               -- → {e : PartialP φ (λ o → T o ≃′ A)}
                               -- → PartialP φ T → A → primGlue A T e
           )

open import Agda.Builtin.Sigma

-- TODO comment this out? it's not used anywhere
module _ where
  open import Agda.Builtin.Cubical.HCompU
    using ( prim^glueU
          ; prim^unglueU
          ; primFaceForall )
  open import Agda.Builtin.Cubical.HCompU public
    renaming ( transpProof to transp-proof-builtin )

-- Uncurry Glue to make it more pleasant to use
@0 Glue : {ℓ ℓ′ : Level} (A : Type ℓ)
          {φ : I}
        → (Te : Partial φ (Σ (Type ℓ′) λ T → T ≃ᵇ A))
        → Type ℓ′
Glue A Te = primGlue A (λ x → Te x .fst) (λ x → Te x .snd)

-- Make the φ argument of prim^unglue explicit
@0 unglue : {ℓ ℓ′ : Level} {A : Type ℓ} (φ : I) {T : Partial φ (Type ℓ′)}
            {e : PartialP φ (λ o → T o ≃ᵇ A)}
          → primGlue A T e → A
unglue φ = prim^unglue {φ = φ}

@0 glue-inc : {ℓ ℓ′ : Level} {A : Type ℓ} (φ : I)
            → {Tf : Partial φ (Σ (Type ℓ′) λ B → B ≃ᵇ A)}
            → (p : PartialP φ (λ { (φ = i1) → Tf 1=1 .fst }))
            → A [ φ ↦ (λ { (φ = i1) → Tf 1=1 .snd .fst (p 1=1) }) ]
            → Glue A Tf
glue-inc φ p x = glue {φ = φ} p (outS x)
