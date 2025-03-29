```agda

{-# OPTIONS --safe #-}

module Prim.Base.Kan where

open import Prim.Base.Type
open import Prim.Base.Interval
open import Prim.Base.Builtin

open import Agda.Builtin.Cubical.Sub
  using ( inS )
  renaming ( Sub to _[_↦_]
           ; primSubOut to outS )
  public

partial-pushout
  : ∀ {ℓ} (i j : I) {A : Partial (i ∨ j) (Type ℓ)}
    {ai : PartialP {a = ℓ} (i ∧ j) (λ { (j ∧ i = i1) → A 1=1 }) }
  → (.(z : IsOne i) → A (is1-left  i j z) [ (i ∧ j) ↦ (λ { (i ∧ j = i1) → ai 1=1 }) ])
  → (.(z : IsOne j) → A (is1-right i j z) [ (i ∧ j) ↦ (λ { (i ∧ j = i1) → ai 1=1 }) ])
  → PartialP (i ∨ j) A
partial-pushout i j u v = primPOr i j (λ z → outS (u z)) (λ z → outS (v z))

hcomp : ∀ {ℓ} {A : Type ℓ} (φ : I)
      → (u : (i : I) → Partial (φ ∨ ~ i) A)
      → A
hcomp φ u = Prim.primHComp (λ j .o → u j (is1-left φ (~ j) o)) (u i0 1=1)

comp : {ℓ^ : I → Level} (A : (i : I) → Type (ℓ^ i)) (φ : I)
     → (u : (i : I) → Partial (φ ∨ ~ i) (A i))
     → A i1
comp A φ u = Prim.primComp A (λ j .o → u j (is1-left φ (~ j) o)) (u i0 1=1)

hfill : ∀ {ℓ} {A : Type ℓ} (φ : I) → I
      → ((i : I) → Partial (φ ∨ ~ i) A)
      → A
hfill φ i u = 
  hcomp (φ ∨ ~ i) λ where
    j (φ = i1) → u (i ∧ j) 1=1
    j (i = i0) → u i0       1=1
    j (j = i0) → u i0       1=1

fill : {ℓ^ : I → Level} (A : ∀ i → Type (ℓ^ i)) (φ : I) (i : I)
     → (u : ∀ i → Partial (φ ∨ ~ i) (A i))
     → A i
fill A φ i u = comp (λ j → A (i ∧ j)) (φ ∨ ~ i) λ where
  j (φ = i1) → u (i ∧ j) 1=1
  j (i = i0) → u i0 1=1
  j (j = i0) → u i0 1=1
