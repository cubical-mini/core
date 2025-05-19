{-# OPTIONS --safe #-}
module Prim.Glue where

open import Prim.Equiv
open import Prim.Interval
open import Prim.Kan
open import Prim.Type

open import Agda.Builtin.Cubical.Glue
  using ( primGlue     -- ∀ {ℓ ℓ′} (A : Type ℓ) {φ : I} (T : Partial φ (Type ℓ′))
                       -- → (e : PartialP φ (λ o → T o ≃′ A)) → Type ℓ′
        ; prim^unglue  -- ∀ {ℓ ℓ′} {A : Type ℓ} {φ : I} {T : Partial φ (Type ℓ′)}
                       -- → {e : PartialP φ (λ o → T o ≃′ A)} → primGlue A T e → A
        ; prim^glue    -- ∀ {ℓ ℓ′} {A : Type ℓ} {φ : I} {T : Partial φ (Type ℓ′)}
                       -- → {e : PartialP φ (λ o → T o ≃′ A)}
                       -- → PartialP φ T → A → primGlue A T e
        )

open import Agda.Builtin.Sigma

module _ where
  open import Agda.Builtin.Cubical.HCompU
    using ( prim^glueU
          ; prim^unglueU
          ; primFaceForall )
  open import Agda.Builtin.Cubical.HCompU public
    renaming ( transpProof to transp-proofᵇ )

@0 Glue : {ℓ ℓ′ : Level} (A : Type ℓ)
          {φ : I}
        → (Te : Partial φ (Σ (Type ℓ′) λ T → T ≃ₜ A))
        → Type ℓ′
Glue A {φ} Te = primGlue A tys eqvs
  module glue-sys where
  tys : Partial φ (Type _)
  tys (φ = i1) = Te 1=1 .fst

  eqvs : PartialP φ (λ .o → tys _ ≃ₜ A)
  eqvs (φ = i1) = Te 1=1 .snd
{-# DISPLAY primGlue A (glue-sys.tys _ Te) (glue-sys.eqvs _ Te) = Glue A Te #-}

@0 unattach
  : {ℓ ℓ′ : Level }{A : Type ℓ} (φ : I) {T : Partial φ (Type ℓ′)}
    {e : PartialP φ (λ o → T o ≃ₜ A)}
  → primGlue A T e → A
unattach φ = prim^unglue {φ = φ}
{-# DISPLAY prim^unglue {l} {l′} {A} {φ} {t} {e} x = unattach {l} {l′} {A} φ {t} {e} x #-}

@0 attach
  : {ℓ ℓ′ : Level} {A : Type ℓ} (φ : I) {T : Partial φ (Type ℓ′)} {e : PartialP φ (λ o → T o ≃ₜ A)}
  → (p : PartialP φ T)
  → A [ φ ↦ (λ o → e o .fst (p o)) ]
  → primGlue A T e
attach φ p x = prim^glue {φ = φ} p (outS x)
{-# DISPLAY prim^glue {_} {_} {_} {φ} {_} {_} x y = attach φ x y #-}
