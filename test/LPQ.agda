{-# OPTIONS --safe #-}
module LPQ where

open import Prim.Data.Nat
open import Prim.Data.Sigma
open import Prim.Data.Unit
open import Prim.Kan
open import Prim.Type

open import Notation.Base

-- large quivers can depend on arbitrary number of levels
Funs : Quiverω 1 lsuc _⊔_
Funs .Quiverω.Obω ℓ .lowerω = Type ℓ
Funs .Quiverω.Homω .lowerω A B = A → B

-- small quivers depend on 0 levels
Paths : ∀{ℓ} (A : Type ℓ) → Quiverω 0 ℓ ℓ
Paths A .Quiverω.Obω .lowerω = A
Paths A .Quiverω.Homω .lowerω = _＝_

module _ {ℓa ℓb} {A : Type ℓa} {B : Type ℓb} {f : A → B} where private
  open Quiverω Funs

  test₁ : Ob _
  test₁ = A

  test₂ : Ob _
  test₂ = B

  test₃ : Hom A B
  test₃ = f

module _ {ℓ} {A : Type ℓ} {x y : A} {p : x ＝ y} where private
  open Quiverω (Paths A)

  test₁ : Ob _
  test₁ = x

  test₂ : Hom x y
  test₂ = p


-- observe posets where relation level is independent of carrier level
record Poset-on {ℓo} (A : Type ℓo) ℓh : Type (ℓo ⊔ lsuc ℓh) where
  no-eta-equality
  field _≤_ : A → A → Type ℓh

Monotone : ∀{ℓa ℓb ℓah ℓbh} {A : Type ℓa} {B : Type ℓb} (f : A → B) → Poset-on A ℓah → Poset-on B ℓbh → Type (ℓa ⊔ ℓah ⊔ ℓbh)
Monotone {A} f P Q = (x y : A) → x P.≤ y → f x Q.≤ f y where
  module P = Poset-on P
  module Q = Poset-on Q

Posetᵈ : Quiverωᵈ Funs 1 (λ ℓ ℓᵈ → ℓ ⊔ lsuc ℓᵈ) (λ ℓ _ ℓpᵈ ℓqᵈ → ℓ ⊔ ℓpᵈ ⊔ ℓqᵈ)
Posetᵈ .Quiverωᵈ.Obω[_] T (lh , _) = Poset-on T lh
Posetᵈ .Quiverωᵈ.Homω[_] f = Monotone f

module DispTest {ℓa ℓb ℓp ℓq} {A : Type ℓa} {B : Type ℓb} (f : A → B)
  (P : Poset-on A ℓp) (Q : Poset-on B ℓq) (m : Monotone f P Q) where private
  open Quiverωᵈ Posetᵈ

  test₁ : Ob[ A ] _
  test₁ = P

  test₂ : Ob[ B ] _
  test₂ = Q

  test₃ : Hom[ f ] P Q
  test₃ = m
