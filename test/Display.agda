{-# OPTIONS --safe #-}
module Display where

open import Prim.Interval
open import Prim.Kan

open import Notation.Base
open import Notation.Lens.Bivariant
open import Notation.Lens.Contravariant
open import Notation.Lens.Covariant
open import Notation.Refl
open import Notation.Total

open import LPQ

-- Pointed structure

record Pointed {ℓ} (A : Type ℓ) : Type ℓ where
  constructor ∙
  field pt : A

instance
  Pointed-Push : Pushω Funs (λ T → Paths (Pointed T))
  Pointed-Push .push f (∙ x) = ∙ (f x)

  Pointed-Lawful-Push : Lawful-Pushω Funs (λ T → Paths (Pointed T))
  Pointed-Lawful-Push .push-refl = refl

Pointedᵈ : Quiverωᵈ Funs 0 _ _
Pointedᵈ = Disp⁺ (λ T → Paths (Pointed T))

Pointeds : Quiverω 1 _ _
Pointeds = ∫ Pointedᵈ

Type∙ : (ℓ : Level) → Type (lsuc ℓ)
Type∙ ℓ = Pointeds .Quiverω.Ob (ℓ , _)
{-# NOINLINE Type∙ #-}

Fun∙ : {ℓx ℓy : Level} → Type∙ ℓx → Type∙ ℓy → Type (ℓx ⊔ ℓy)
Fun∙ = Pointeds .Quiverω.Hom


-- Magma structure

record Magma-on′ {ℓa} {ℓb} (A : Type ℓa) (B : Type ℓb) : Type (ℓa ⊔ ℓb) where
  constructor mk-magma-on
  field _⋆_ : A → A → B

Magma-on : ∀{ℓ} (A : Type ℓ) → Type ℓ
Magma-on A = Magma-on′ A A

instance
  Magma-Extend : Extendω Funs (λ {x = A} {y = B} _ → Paths (Magma-on′ A B))
  Magma-Extend .extend-l p u .Magma-on′._⋆_ x y = p (x ⋆ y) where open Magma-on′ u
  Magma-Extend .extend-r p v .Magma-on′._⋆_ x y = p x ⋆ p y where open Magma-on′ v

  Magma-Lawful-Extend : Lawful-Extendω Funs (λ {x = A} {y = B} _ → Paths (Magma-on′ A B))
  Magma-Lawful-Extend .extend-refl = refl
  Magma-Lawful-Extend .extend-coh = refl


module _ where
  private
    Q : Quiverωᵈ Funs 0 _ _
    Q = Disp± (λ {x = A} {y = B} _ → Paths (Magma-on′ A B))

  Magmaᵈ : Quiverωᵈ Funs 0 _ _
  Magmaᵈ .Quiverωᵈ.Ob[_] = Q .Quiverωᵈ.Ob[_]
  Magmaᵈ .Quiverωᵈ.Hom[_] = Q .Quiverωᵈ.Hom[_] -- TODO repack

  instance
    Magma-Reflᵈ : Reflωᵈ Funs Magmaᵈ
    Magma-Reflᵈ .reflᵈ _ = refl

Magmas : Quiverω 1 _ _
Magmas = ∫ Magmaᵈ

Magma : (ℓ : Level) → Type (lsuc ℓ)
Magma ℓ = Magmas .Quiverω.Ob (ℓ , tt)

Magma-Hom : {ℓx ℓy : Level} → Magma ℓx → Magma ℓy → Type (ℓx ⊔ ℓy)
Magma-Hom = Magmas .Quiverω.Hom
{-# DISPLAY ΣHom Funs Magmaᵈ M N = Magma-Hom M N #-}


module Display-Structure {ℓa ℓb} {A : Type ℓa} {B : Type ℓb} {f : A → B} where
  module _ {a : A} {b : B} {p : f a ＝ b} where private
    test : Fun∙ (A , ∙ a) (B , ∙ b)
    test .hom = f
    test .preserves i = ∙ (p i)

  module _ {_⊕_ : A → A → A} {_⊗_ : B → B → B} {p : (x y : A) → f (x ⊕ y) ＝ (f x ⊗ f y)} where private
    test : Magma-Hom (A , mk-magma-on _⊕_) (B , mk-magma-on _⊗_)
    test .hom = f
    test .preserves i .Magma-on′._⋆_ x y = p x y i

    ads : (t : Magma-Hom (A , mk-magma-on _⊕_) (B , mk-magma-on _⊗_)) → {!!}
    ads t = {!!}

module Hom-Induction {ℓa} where
  module _ {A : Type ℓa} where
    _∙₁_ : ∀{x y z : A} → x ＝ y → y ＝ z → x ＝ z
    _∙₁_ p q = extend-l q p

    _∙₂_ : {x y z : A} → x ＝ y → y ＝ z → x ＝ z
    _∙₂_ = extend-r

  open Quiverω Magmas
  module Algebraic-Kek {M : Magma ℓa} where
     very-funny : (X : Magma ℓa) (h : X .fst → M .fst) (x y : X .fst) → M .fst
     very-funny X h = extend-l h (X .snd) .Magma-on′._⋆_

     -- if `to` and `from` are actual inverses you get something coherent
     transfer-structure : (X : Type ℓa) (to : X → M .fst) (from : M .fst → X)
                        → Magma-on X
     transfer-structure X to from .Magma-on′._⋆_ w z = from (extend-r to (M .snd) .Magma-on′._⋆_ w z)
