{-# OPTIONS --safe #-}
module LPQ where

open import Prim.Interval
open import Prim.Kan

open import Notation.Base
open import Notation.Lens.Bivariant
open import Notation.Lens.Contravariant
open import Notation.Lens.Covariant
open import Notation.Refl.Base
open import Notation.Total

-- large quivers can depend on arbitrary number of levels
Funs : Quiverω 1 _ _
Funs .Quiverω.Ob (ℓ , _) = Type ℓ
Funs .Quiverω.Hom A B = A → B

instance
  Fun-Refl : Reflω Funs
  Fun-Refl .refl x = x

-- small quivers depend on 0 levels
Paths : ∀{ℓ} (A : Type ℓ) → Quiverω 0 _ _
Paths A .Quiverω.Ob _ = A
Paths A .Quiverω.Hom = _＝_

instance
  Path-Refl : ∀{ℓ} {A : Type ℓ} → Reflω (Paths A)
  Path-Refl .refl {x} _ = x

  Path-Push-Path : ∀{ℓa ℓb} {A : Type ℓa} {B : A → Type ℓb}
                 → Pushω (Paths A) (λ x → Paths (B x))
  Path-Push-Path {B} .push p = transp (λ i → B (p i)) i0

  Path-Push-Path-Lawful : ∀{ℓa ℓb} {A : Type ℓa} {B : A → Type ℓb}
                        → Lawful-Pushω (Paths A) (λ x → Paths (B x))
  Path-Push-Path-Lawful {B} .Lawful-Push.push-refl {x} {u} i = transp (λ _ → B x) i u

  Path-Pull-Path : ∀{ℓa ℓb} {A : Type ℓa} {B : A → Type ℓb}
                 → Pullω (Paths A) (λ x → Paths (B x))
  Path-Pull-Path {B} .pull p = transp (λ i → B (p (~ i))) i0

  Path-Lawful-Pull-Lawful : ∀{ℓa ℓb} {A : Type ℓa} {B : A → Type ℓb}
                          → Lawful-Pullω (Paths A) (λ x → Paths (B x))
  Path-Lawful-Pull-Lawful {B} .pull-refl {y} {v} i = transp (λ i → B y) (~ i) v

  Path-Extend : ∀{ℓa ℓb} {A : Type ℓa} {B : {x y : A} → x ＝ y → Type ℓb}
              → Extendω (Paths A) (λ p → Paths (B p))
  Path-Extend {B} .extend-l p = transp (λ i → B λ j → p (  i ∧ j)) i0
  Path-Extend {B} .extend-r p = transp (λ i → B λ j → p (~ i ∨ j)) i0

  Path-Extend-Lafwul : ∀{ℓa ℓb} {A : Type ℓa} {B : {x y : A} → x ＝ y → Type ℓb}
                     → Lawful-Extendω (Paths A) (λ p → Paths (B p))
  Path-Extend-Lafwul .extend-refl = refl
  Path-Extend-Lafwul {B} .extend-coh {x} {u} i = hcomp (∂ i) λ where
    j (i = i0) → transp (λ _ → B λ _ → x)    j  u
    j (i = i1) → transp (λ _ → B λ _ → x) (~ j) u
    j (j = i0) → transp (λ _ → B λ _ → x)    i  u

module _ {ℓa ℓb} {A : Type ℓa} {B : Type ℓb} {f : A → B} where private
  open Quiverω Funs

  test₁ : Ob _
  test₁ = A

  test₂ : Ob _
  test₂ = B

  test₃ : Hom A B
  test₃ = f

  test₄ : Hom A A
  test₄ = refl

module PathTest {ℓ} {A : Type ℓ} {x y : A} {p : x ＝ y} where private
  open Quiverω (Paths A)

  test₁ : Ob _
  test₁ = x

  test₂ : Hom x y
  test₂ = p

  test₃ : Hom x x
  test₃ = refl

module PushTest {ℓa ℓb} {A : Type ℓa} {B : A → Type ℓb} {x y : A} {p : x ＝ y} where private

  test₁ : B x → B y
  test₁ = push p


-- observe posets where relation level is independent of carrier level
record Poset-on {ℓo} (A : Type ℓo) ℓh : Type (ℓo ⊔ lsuc ℓh) where
  no-eta-equality
  field _≤_ : A → A → Type ℓh

Monotone : ∀{ℓa ℓb ℓah ℓbh} {A : Type ℓa} {B : Type ℓb} (f : A → B) → Poset-on A ℓah → Poset-on B ℓbh → Type (ℓa ⊔ ℓah ⊔ ℓbh)
Monotone {A} f P Q = (x y : A) → x P.≤ y → f x Q.≤ f y where
  module P = Poset-on P
  module Q = Poset-on Q

Posetᵈ : Quiverωᵈ Funs 1 _ _
Posetᵈ .Quiverωᵈ.Ob[_] T (lh , _) = Poset-on T lh
Posetᵈ .Quiverωᵈ.Hom[_] f = Monotone f

instance
  Poset-Reflᵈ : ∀{ℓo ℓh} → Reflᵈ Funs Posetᵈ (ℓo , _) (ℓh , _)
  Poset-Reflᵈ .reflᵈ _ _ _ = refl

module DispTest {ℓa ℓb ℓp ℓq} {A : Type ℓa} {B : Type ℓb} (f : A → B)
  (PA : Poset-on A ℓp) (QB : Poset-on B ℓq) (m : Monotone f PA QB) where private
  open Quiverωᵈ Posetᵈ

  test₁ : Ob[ A ] _
  test₁ = PA

  test₂ : Ob[ B ] _
  test₂ = QB

  test₃ : Hom[ f ] PA QB
  test₃ = m

  test₄ : Hom[ refl ] PA PA
  test₄ = reflᵈ PA


module CompTest {ℓa ℓp} {A : Type ℓa}
  (open Quiverω (Component Posetᵈ A (ℓp , _)))
  (P Q : Ob _) where private

  test₁ : Poset-on A ℓp
  test₁ = P

  private module P = Poset-on P
  private module Q = Poset-on Q

  test₂ : (h : ∀ x y → x P.≤ y → x Q.≤ y) → Hom P Q
  test₂ = refl


module TotalTest where
  Posets : Quiverω 2 _ _
  Posets = ∫ Posetᵈ
  open Quiverω Posets

  Poset : (ℓo ℓh : Level) → Type (lsuc (ℓo ⊔ ℓh))
  Poset ℓo ℓh = Ob (ℓo , ℓh , _)

  module _ {ℓa ℓb ℓp ℓq} {P : Poset ℓa ℓp} {Q : Poset ℓb ℓq} {f : Hom P Q} where
    test₁ : P .fst → Q .fst
    test₁ = f .hom

    test₂ : Monotone (f .hom) (P .snd) (Q .snd)
    test₂ = f .preserves
