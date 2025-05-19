{-# OPTIONS --safe #-}
module Prim.Kan where

open import Prim.Type
open import Prim.Interval

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
hcomp φ u = primHComp (λ j .o → u j (is1-left φ (~ j) o)) (u i0 1=1)

∂ : I → I
∂ i = i ∨ ~ i

comp : {ℓ^ : I → Level} (A : (i : I) → Type (ℓ^ i)) (φ : I)
     → (u : (i : I) → Partial (φ ∨ ~ i) (A i))
     → A i1
comp A φ u = primComp A (λ j .o → u j (is1-left φ (~ j) o)) (u i0 1=1)

hfill : {ℓ : Level} {A : Type ℓ} (φ : I) → I
      → ((i : I) → Partial (φ ∨ ~ i) A)
      → A
hfill φ i u =
  hcomp (φ ∨ ~ i) λ where
    j (φ = i1) → u (i ∧ j) 1=1
    j (i = i0) → u i0      1=1
    j (j = i0) → u i0      1=1

fill : {ℓ^ : I → Level} (A : ∀ i → Type (ℓ^ i)) (φ : I) (i : I)
     → (u : ∀ i → Partial (φ ∨ ~ i) (A i))
     → A i
fill A φ i u = comp (λ j → A (i ∧ j)) (φ ∨ ~ i) λ where
  j (φ = i1) → u (i ∧ j) 1=1
  j (i = i0) → u i0 1=1
  j (j = i0) → u i0 1=1

open import Agda.Builtin.Cubical.Path public
  renaming ( _≡_   to _＝_
           ; PathP to Pathᴾ )

Path : {ℓ : Level} (A : Type ℓ) → A → A → Type ℓ
Path A A₀ A₁ = Pathᴾ (λ _ → A) A₀ A₁

private
  hcomp-unique : {ℓ : Level} {A : Type ℓ} (φ : I)
                 (u : ∀ i → Partial (φ ∨ ~ i) A)
               → (h₂ : ∀ i → A [ _ ↦ (λ { (i = i0) → u i0 1=1
                                        ; (φ = i1) → u i  1=1 }) ])
               → hcomp φ u ＝ outS (h₂ i1)
  hcomp-unique φ u h₂ i =
    hcomp (φ ∨ i) λ where
      k (k = i0) → u i0 1=1
      k (i = i1) → outS (h₂ k)
      k (φ = i1) → u k 1=1


record Recall {ℓ ℓ′} {A : Type ℓ} {B : A → Type ℓ′}
  (f : (x : A) → B x) (x : A) (y : B x) : Type (ℓ l⊔ ℓ′) where
  constructor ⟪_⟫
  field eq : f x ＝ y

recall : {ℓ ℓ′ : Level} {A : Type ℓ} {B : A → Type ℓ′}
         (f : (x : A) → B x) (x : A)
       → Recall f x (f x)
recall f x = ⟪ (λ _ → f x) ⟫
