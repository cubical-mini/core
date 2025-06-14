{-# OPTIONS --safe --erased-cubical #-}
module Prim.Kan where

open import Prim.Interval
open import Prim.Type

open import Agda.Builtin.Sigma
open import Agda.Builtin.Cubical.Sub public
  using ( inS )
  renaming ( Sub to _[_↦_]
           ; primSubOut to outS )

open import Agda.Primitive.Cubical
  using ( primHComp
        ; primComp )

open import Agda.Primitive.Cubical public
  using ()
  renaming ( primTransp to transp )

hcomp : {ℓ : Level} {A : Type ℓ} (φ : I)
      → (u : (i : I) → Partial (φ ∨ ~ i) A)
      → A
hcomp {A = A} φ u = primHComp sys (u i0 1=1)
  module hcomp-sys where
  sys : ∀ j → Partial φ A
  sys j (φ = i1) = u j 1=1
{-# DISPLAY primHComp {ℓ} {A} {φ} (hcomp-sys.sys _ u) _ = hcomp {ℓ} {A} φ u #-}

∂ : I → I
∂ i = i ∨ ~ i

comp : {ℓ^ : I → Level} (A : (i : I) → Type (ℓ^ i)) (φ : I)
     → (u : (i : I) → Partial (φ ∨ ~ i) (A i))
     → A i1
comp A φ u = primHComp sys (transp A i0 (u i0 1=1))
  module comp-sys where
  sys : ∀ j → Partial φ (A i1)
  sys j (φ = i1) = transp (λ i → A (i ∨ j)) j (u j 1=1)
{-# DISPLAY primHComp {_} {_} {φ} (comp-sys.sys A _ u) _ = comp A φ u #-}
-- TODO check why 1Lab stopped using `primComp`
-- primComp A (λ j .o → u j (is1-left φ (~ j) o)) (u i0 1=1)

fill : {ℓ^ : I → Level} (A : ∀ i → Type (ℓ^ i)) (φ : I) (i : I)
     → (u : ∀ i → Partial (φ ∨ ~ i) (A i))
     → A i
fill A φ i u = comp (λ j → A (i ∧ j)) (φ ∨ ~ i) sys
  module fill-sys where
  sys : (j : I) → Partial ((φ ∨ ~ i) ∨ ~ j) _
  sys j (φ = i1) = u (i ∧ j) 1=1
  sys j (i = i0) = u i0      1=1
  sys j (j = i0) = u i0      1=1

hfill : {ℓ : Level} {A : Type ℓ} (φ : I) → I
      → ((i : I) → Partial (φ ∨ ~ i) A)
      → A
hfill {A} φ i u =  hcomp (φ ∨ ~ i) (fill-sys.sys (λ _ → A) φ i u)

open import Agda.Builtin.Cubical.Path public
  renaming ( _≡_   to _＝_
           ; PathP to Pathᴾ )

Path : {ℓ : Level} (A : Type ℓ) → A → A → Type ℓ
Path A A₀ A₁ = Pathᴾ (λ _ → A) A₀ A₁
