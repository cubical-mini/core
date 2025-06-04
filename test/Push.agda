{-# OPTIONS --safe #-}
module Push where

open import Prim.Interval
open import Prim.Type

open import Notation.Base
open import Notation.Composition
open import Notation.Displayed.Base
open import Notation.Displayed.Push
open import Notation.Displayed.Reflexivity
open import Notation.Reflexivity
open import Notation.Symmetry
open import Notation.Unitality.Outer

open import Foundations.Path.Groupoid
open import Foundations.Path.Transport
open import Foundations.Pi.Category

Pointed : ∀{ℓ} → Type ℓ → Type ℓ
Pointed A = A

open Fun-cat
open Path-gpd0
instance
  Pointed-Push : Pushω Funs Pointed
  Pointed-Push .push f x = f x

  Pointed-Push-Id : Push-Idω Funs Pointed {ℓ-homᵈ = λ ℓ _ → ℓ} Pathsω
  Pointed-Push-Id .push-id = refl

manual automatic : Quiver-onᵈ Funs Pointed λ _ z → z
manual .Quiver-onᵈ.Hom[_] f x y = f x ＝ y
automatic = Disp⁺ Funs Pointed {ℓ-homᵈ = λ ℓ _ → ℓ} Pathsω

what1 : ∀{ℓa}{A : Type ℓa} {A∙ : Pointed A} → A∙ ＝ A∙
what1 {A} {A∙} = reflᵈ

module _ {ℓa ℓb} {A : Type ℓa} {B : Type ℓb} (f : A → B) (a : A) (b : B) where
  _ : automatic .Quiver-onᵈ.Hom[_] f a b ＝ Quiver-onᵈ.Hom[_] manual f a b
  _ = refl


module Pa {ℓ} {A : Type ℓ} {c : A} where
  open Path-gpd
  instance
    Path-Push : Pushω (Pathsω A) (c ＝_)
    Path-Push .push {x} {y} p q = q ∙ p

    Path-Push-Id : Push-Idω (Pathsω A) (c ＝_) {ℓ-homᵈ = λ ℓ _ → _} (λ t → Pathsω (c ＝ t))
    Path-Push-Id .push-id = id-o _
