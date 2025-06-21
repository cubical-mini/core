{-# OPTIONS --safe #-}
module LPQ where

open import Prim.Kan

open import Notation.Base
open import Notation.Refl.Base
open import Notation.Total

-- large quivers can depend on arbitrary number of levels
Funs : Quiverω 1 lsuc _⊔_
Funs .Quiverω.Obω ℓ .lowerω = Type ℓ
Funs .Quiverω.Homω .lowerω A B = A → B

instance
  Fun-Refl : ∀{ℓ} → Refl Funs (ℓ , _)
  Fun-Refl .refl _ x = x

-- small quivers depend on 0 levels
Paths : ∀{ℓ} (A : Type ℓ) → Quiverω 0 ℓ ℓ
Paths A .Quiverω.Obω .lowerω = A
Paths A .Quiverω.Homω .lowerω = _＝_

instance
  Path-Refl : ∀{ℓ} {A : Type ℓ} → Refl (Paths A) _
  Path-Refl .refl x _ = x

module _ {ℓa ℓb} {A : Type ℓa} {B : Type ℓb} {f : A → B} where private
  open Quiverω Funs

  test₁ : Ob _
  test₁ = A

  test₂ : Ob _
  test₂ = B

  test₃ : Hom A B
  test₃ = f

  test₄ : Hom A A
  test₄ = refl _

module _ {ℓ} {A : Type ℓ} {x y : A} {p : x ＝ y} where private
  open Quiverω (Paths A)

  test₁ : Ob _
  test₁ = x

  test₂ : Hom x y
  test₂ = p

  test₃ : Hom x x
  test₃ = refl _


-- observe posets where relation level is independent of carrier level
record Poset-on {ℓo} (A : Type ℓo) ℓh : Type (ℓo ⊔ lsuc ℓh) where
  no-eta-equality
  field _≤_ : A → A → Type ℓh

Monotone : ∀{ℓa ℓb ℓah ℓbh} {A : Type ℓa} {B : Type ℓb} (f : A → B) → Poset-on A ℓah → Poset-on B ℓbh → Type (ℓa ⊔ ℓah ⊔ ℓbh)
Monotone {A} f P Q = (x y : A) → x P.≤ y → f x Q.≤ f y where
  module P = Poset-on P
  module Q = Poset-on Q

Posetᵈ : Quiverωᵈ Funs 1 _ _
Posetᵈ .Quiverωᵈ.Obω[_] T (lh , _) = Poset-on T lh
Posetᵈ .Quiverωᵈ.Homω[_] f = Monotone f

instance
  Poset-Reflᵈ : ∀{ℓo ℓh} → Reflᵈ Funs Posetᵈ (ℓo , _) (ℓh , _)
  Poset-Reflᵈ .reflᵈ _ _ _ = refl _

module DispTest {ℓa ℓb ℓp ℓq} {A : Type ℓa} {B : Type ℓb} (f : A → B)
  (PA : Poset-on A ℓp) (QB : Poset-on B ℓq) (m : Monotone f PA QB) where private
  open Quiverωᵈ Posetᵈ

  test₁ : Ob[ A ] _
  test₁ = PA

  test₂ : Ob[ B ] _
  test₂ = QB

  test₃ : Hom[ f ] PA QB
  test₃ = m

  test₄ : Hom[ refl _ ] PA PA
  test₄ = reflᵈ PA


module CompTest {ℓa ℓp} {A : Type ℓa} (P Q : Poset-on A ℓp) where private
  C = Component Posetᵈ A (ℓp , _)
  open Quiverω C

  test₁ : Ob _
  test₁ = P

  module _ where
    private module P = Poset-on P
    private module Q = Poset-on Q

    test₂ : (h : ∀{x y} → x P.≤ y  → x Q.≤ y) → Hom P Q
    test₂ h _ _ p = h p


module TotalTest where
  Posets : Quiverω 2 _ _
  Posets = ∫ Funs Posetᵈ
  open Quiverω Posets

  Poset : (ℓo ℓh : Level) → Type (lsuc (ℓo ⊔ ℓh))
  Poset ℓo ℓh = Ob (ℓo , ℓh , _)

  module _ {ℓa ℓb ℓp ℓq} {P : Poset ℓa ℓp} {Q : Poset ℓb ℓq} {f : Hom P Q} where
    test₁ : P .fst → Q .fst
    test₁ = f .hom

    test₂ : Monotone (f .hom) (P .snd) (Q .snd)
    test₂ = f .preserves
