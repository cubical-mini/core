{-# OPTIONS --safe #-}
module Display where

open import Prim.Data.Sigma
open import Prim.Interval
open import Prim.Kan
open import Prim.Type

open import Notation.Base
open import Notation.Lens.Bivariant
open import Notation.Lens.Contravariant
open import Notation.Lens.Covariant
open import Notation.Refl
open import Notation.Total

Funs : Quiverω lsuc _⊔_
Funs .Quiverω.Ob ℓ = Type ℓ
Funs .Quiverω.Hom X Y = X → Y

instance
  Fun-Refl : Reflω Funs
  Fun-Refl .refl x = x

Paths : ∀{ℓ} (A : Type ℓ) → Quiverω (λ _ → ℓ) (λ _ _ → ℓ)
Paths A .Quiverω.Ob _ = A
Paths A .Quiverω.Hom = _＝_

instance
  Path-Refl : ∀{ℓ} {A : Type ℓ} → Reflω (Paths A)
  Path-Refl .refl {x} _ = x
  {-# INCOHERENT Path-Refl #-}

  Path-Refl0 : ∀{ℓ} {A : Type ℓ} → Refl (Paths A) lzero
  Path-Refl0 = Path-Refl

Pathsᶠ : ∀ {ℓ-adj : ℓ-sig¹} {ℓa} {A : Type ℓa} (S : ∀ {ℓ}(a : A) → Type (ℓ-adj ℓ))
       → (a : A) → Quiverω (λ _ → ℓ-adj ℓa) (λ _ _ → ℓ-adj ℓa)
Pathsᶠ {ℓa} S a = Paths (S {ℓa} a)

-- 2-Pathsᶠ′ : {ℓ-ob : ℓ-sig¹} {ℓ-hom : ℓ-sig²} {C : Quiverω ℓ-ob ℓ-hom } (open Quiverω C)
--           → (S : ∀{ℓx ℓy} (a : Ob ℓx) (b : Ob ℓy) (r : Hom a b) → Type (ℓ-hom ℓx ℓy))
--           → ∀{ℓa ℓb} {a : Ob ℓa} {b : Ob ℓb} (r : Hom a b) → Quiverω (λ _ → ℓ-hom ℓa ℓb) (λ _ _ → ℓ-hom ℓa ℓb)
-- 2-Pathsᶠ′ S {a} {b} r = Paths (S a b r)

-- Paths have a lot of interesting properties

instance
  Path-Push : ∀{ℓa ℓb} {A : Type ℓa} {B : A → Type ℓb}
            → Pushω (Paths A) (Pathsᶠ B)
  Path-Push {B} .push p = transp (λ i → B (p i)) i0

  Path-Lawful-Push : ∀{ℓa ℓb} {A : Type ℓa} {B : A → Type ℓb}
                   → Lawful-Pushω (Paths A) (Pathsᶠ B)
  Path-Lawful-Push {B} .push-refl {x} {u} i = transp (λ i → B x) i u

  Path-Pull : ∀{ℓa ℓb} {A : Type ℓa} {B : A → Type ℓb}
            → Pullω (Paths A) (Pathsᶠ B)
  Path-Pull {B} .pull p = transp (λ i → B (p (~ i))) i0

  Path-Lawful-Pull : ∀{ℓa ℓb} {A : Type ℓa} {B : A → Type ℓb}
                   → Lawful-Pullω (Paths A) (Pathsᶠ B)
  Path-Lawful-Pull {B} .pull-refl {x} {v} i = transp (λ i → B x) (~ i) v

  Path-Extend : ∀{ℓa ℓb} {A : Type ℓa} {B : {x y : A} → x ＝ y → Type ℓb}
              → Extendω (Paths A) (Pathsᶠ B)
  Path-Extend {B} .extend-l p = transp (λ i → B λ j → p (  i ∧ j)) i0
  Path-Extend {B} .extend-r p = transp (λ i → B λ j → p (~ i ∨ j)) i0

  Path-Lawful-Extend : ∀{ℓa ℓb} {A : Type ℓa} {B : {x y : A} → x ＝ y → Type ℓb}
                     → Lawful-Extendω (Paths A) (Pathsᶠ B)
  Path-Lawful-Extend .extend-refl = refl
  Path-Lawful-Extend {B} .extend-coh {x} {u} i = hcomp (∂ i) λ where
    j (i = i0) → transp (λ _ → B λ _ → x)    j  u
    j (i = i1) → transp (λ _ → B λ _ → x) (~ j) u
    j (j = i0) → transp (λ _ → B λ _ → x)    i  u


-- Pointed structure

record Pointed {ℓ} (A : Type ℓ) : Type ℓ where
  constructor ∙
  field pt : A

instance
  Pointed-Push : Pushω Funs (Pathsᶠ Pointed)
  Pointed-Push .push f (∙ x) = ∙ (f x)

  Pointed-Lawful-Push : Lawful-Pushω Funs (Pathsᶠ Pointed)
  Pointed-Lawful-Push .push-refl = refl

Pointedᵈ : Quiverωᵈ Funs _ _
Pointedᵈ = Disp⁺ (Pathsᶠ Pointed)

Pointeds : Quiverω _ _
Pointeds = ∫ Pointedᵈ

Type∙ : (ℓ : Level) → Type (lsuc ℓ)
Type∙ = Pointeds .Quiverω.Ob
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
  Magma-Extend : Extendω Funs (λ {x = x} {y} _ → Paths (Magma-on′ x y))
  Magma-Extend .extend-l p u .Magma-on′._⋆_ x y = p (x ⋆ y) where open Magma-on′ u
  Magma-Extend .extend-r p v .Magma-on′._⋆_ x y = p x ⋆ p y where open Magma-on′ v

  Magma-Lawful-Extend : Lawful-Extendω Funs (λ {x = x} {y} _ → Paths (Magma-on′ x y))
  Magma-Lawful-Extend .extend-refl = refl
  Magma-Lawful-Extend .extend-coh = refl


module _ where
  private
    Q : Quiverωᵈ Funs _ _
    Q = Disp± _
    -- (λ {x = A} {y = B} _ → Paths (Magma-on′ A B))

  Magmaᵈ : Quiverωᵈ Funs _ _
  Magmaᵈ .Quiverωᵈ.Ob[_] = Q .Quiverωᵈ.Ob[_]
  Magmaᵈ .Quiverωᵈ.Hom[_] = Q .Quiverωᵈ.Hom[_] -- TODO repack

  instance
    Magma-Reflᵈ : Reflωᵈ Magmaᵈ
    Magma-Reflᵈ .reflᵈ = Disp±-Reflᵈ .Reflᵈ.reflᵈ

Magmas : Quiverω  _ _
Magmas = ∫ Magmaᵈ

Magma : (ℓ : Level) → Type (lsuc ℓ)
Magma = Magmas .Quiverω.Ob

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
    _∙₁_ p q = extend-l {ℓx = lzero} {ℓy = lzero} q p

    _∙₂_ : {x y z : A} → x ＝ y → y ＝ z → x ＝ z
    _∙₂_ = extend-r {ℓx = lzero} {ℓy = lzero}

  open Quiverω Magmas
  module Algebraic-Kek {M : Magma ℓa} where
     very-funny : (X : Magma ℓa) (h : X .fst → M .fst) (x y : X .fst) → M .fst
     very-funny X h = extend-l h (X .snd) .Magma-on′._⋆_

     -- if `to` and `from` are actual inverses you get something coherent
     transfer-structure : (X : Type ℓa) (to : X → M .fst) (from : M .fst → X)
                        → Magma-on X
     transfer-structure X to from .Magma-on′._⋆_ w z = from (extend-r to (M .snd) .Magma-on′._⋆_ w z)
