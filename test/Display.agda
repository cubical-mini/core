{-# OPTIONS --safe #-}
module Display where

open import Prim.Data.Equality
open import Prim.Type

open import Quiver.Base
open import Quiver.Lens.Bivariant
open import Quiver.Lens.Contravariant
open import Quiver.Lens.Covariant
open import Quiver.Total

Funs : Quiverω lsuc _⊔_
Funs .Quiverω.Ob ℓ = Type ℓ
Funs .Quiverω.Hom X Y = X → Y
Funs .Quiverω.refl x = x

Paths : ∀{ℓ} (A : Type ℓ) → Quiverω _ _
Paths A .Quiverω.Ob _ = A
Paths A .Quiverω.Hom = _＝ⁱ_
Paths A .Quiverω.refl = reflⁱ

Pathsᶠ : ∀ {ℓ-adj : ℓ-sig¹} {ℓa} {A : Type ℓa} (S : ∀ {ℓ}(a : A) → Type (ℓ-adj ℓ))
       → (a : A) → Quiverω (λ _ → ℓ-adj ℓa) (λ _ _ → ℓ-adj ℓa)
Pathsᶠ {ℓa} S A = Paths (S {ℓa} A)

ap : ∀{ℓa ℓb} {A : Type ℓa} {B : Type ℓb} (f : A → B) {x y : A} (p : x ＝ⁱ  y) → f x ＝ⁱ f y
ap f reflⁱ = reflⁱ

-- Paths have a lot of interesting properties

instance
  Path-Push : ∀{ℓa ℓb} {A : Type ℓa} {B : A → Type ℓb}
            → Push (Paths A) (Pathsᶠ B)
  Path-Push .push reflⁱ w = w
  Path-Push .push-refl = reflⁱ

  Path-Pull : ∀{ℓa ℓb} {A : Type ℓa} {B : A → Type ℓb}
            → Pull (Paths A) (Pathsᶠ B)
  Path-Pull .pull reflⁱ w = w
  Path-Pull .pull-refl = reflⁱ

  Path-Extend : ∀{ℓa ℓb} {A : Type ℓa} {B : {x y : A} → x ＝ⁱ y → Type ℓb}
              → Extend (Paths A) (Pathsᶠ B)
  Path-Extend .extend-l reflⁱ u = u
  Path-Extend .extend-r reflⁱ v = v
  Path-Extend .Extend.extend-refl = reflⁱ
  Path-Extend .Extend.extend-coh = reflⁱ


-- Pointed structure

record Pointed {ℓ} (A : Type ℓ) : Type ℓ where
  constructor ∙
  field pt : A

instance
  Pointed-Push : Push Funs (Pathsᶠ Pointed)
  Pointed-Push .push f (∙ x) = ∙ (f x)
  Pointed-Push .push-refl = reflⁱ


Pointedᵈ : Quiverωᵈ Funs _ _
Pointedᵈ = Disp⁺ (Pathsᶠ Pointed)

Pointeds : Quiverω _ _
Pointeds = ∫ Pointedᵈ

Type∙ : (ℓ : Level) → Type (lsuc ℓ)
Type∙ = ΣOb Pointed
{-# NOINLINE Type∙ #-}


-- Magma structure

record Magma-on′ {ℓa} {ℓb} (A : Type ℓa) (B : Type ℓb) : Type (ℓa ⊔ ℓb) where
  constructor mk-magma-on
  field _⋆_ : A → A → B

Magma-on : ∀{ℓ} (A : Type ℓ) → Type ℓ
Magma-on A = Magma-on′ A A

instance
  Magma-Extend : Extend Funs (λ {x = A} {y = B} _ → Paths (Magma-on′ A B))
  Magma-Extend .extend-l p u .Magma-on′._⋆_ x y = p (x ⋆ y) where open Magma-on′ u
  Magma-Extend .extend-r p v .Magma-on′._⋆_ x y = p x ⋆ p y where open Magma-on′ v
  Magma-Extend .extend-refl = reflⁱ
  Magma-Extend .extend-coh = reflⁱ

Magmaᵈ : Quiverωᵈ Funs _ _
Magmaᵈ = Disp± (λ {x = A} {y = B} _ → Paths (Magma-on′ A B))

Magmas : Quiverω  _ _
Magmas = ∫ Magmaᵈ

Magma : (ℓ : Level) → Type (lsuc ℓ)
Magma = ΣOb Magma-on


module Display-Structure {ℓa ℓb} {A : Type ℓa} {B : Type ℓb} {f : A → B} where
  module _ {a : A} {b : B} {p : f a ＝ⁱ b} where private
    open Quiverω Pointeds

    test : Hom (A , ∙ a) (B , ∙ b)
    test .hom = f
    test .preserves = ap ∙ p

  module _ {_⊕_ : A → A → A} {_⊗_ : B → B → B} {p : (x y : A) → f (x ⊕ y) ＝ⁱ (f x ⊗ f y)} where private
    open Quiverω Magmas

    test : Hom (A , mk-magma-on _⊕_) (B , mk-magma-on _⊗_)
    test .hom = f
    test .preserves = {!!} -- i .Magma-on′._⋆_ x y = p x y i -- need funext


module Hom-Induction {ℓa} where
  module _ {A : Type ℓa} where
    _∙₁_ : ∀{x y z : A} → x ＝ⁱ y → y ＝ⁱ z → x ＝ⁱ z
    _∙₁_ p q = extend-l {ℓx = lzero} {ℓy = lzero} q p

    _∙₂_ : {x y z : A} → x ＝ⁱ y → y ＝ⁱ z → x ＝ⁱ z
    _∙₂_ = extend-r {ℓx = lzero} {ℓy = lzero}

  open Quiverω Magmas
  module Algebraic-Kek {M : Magma ℓa} where
     very-funny : (X : Magma ℓa) (h : X .fst → M .fst) (x y : X .fst) → M .fst
     very-funny X h = extend-l h (X .snd) .Magma-on′._⋆_

     -- if `to` and `from` are actual inverses you get something coherent
     transfer-structure : (X : Type ℓa) (to : X → M .fst) (from : M .fst → X)
                        → Magma-on X
     transfer-structure X to from .Magma-on′._⋆_ w z = from (extend-r to (M .snd) .Magma-on′._⋆_ w z) 
