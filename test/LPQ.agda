{-# OPTIONS --safe #-}
module LPQ where

open import Prim.Interval
open import Prim.Kan

open import Foundations.Quiver.Base
open import Foundations.Quiver.Component.Base
open import Foundations.Quiver.Lens.Bivariant
open import Foundations.Quiver.Lens.Contravariant
open import Foundations.Quiver.Lens.Covariant
open import Foundations.Quiver.Total.Base

open import Notation.Assoc
open import Notation.Comp
open import Notation.Lens.Bivariant
open import Notation.Lens.Contravariant
open import Notation.Lens.Covariant
open import Notation.Refl
open import Notation.Sym

-- large quivers can depend on arbitrary number of levels
Funs : Quiverω 1 _ _
Funs .Quiverω.Ob (ℓ , _) = Type ℓ
Funs .has-quiver-onω .Quiver-onω.Hom A B = A → B

instance
  Fun-Refl : Reflω Funs
  Fun-Refl .refl x = x

  Fun-Comp : Compω Funs
  Fun-Comp ._∙_ f g x = g (f x)

Paths-on : ∀{ℓ} (A : Type ℓ) → Quiver-onω 0 (λ _ → A) _
Paths-on _ = corr²→quiver-onω _＝_

-- small quivers depend on 0 levels
Paths : ∀{ℓ} (A : Type ℓ) → Quiverω 0 _ _
Paths A .Quiverω.Ob _ = A
Paths A .has-quiver-onω = Paths-on A

instance
  Path-Refl : ∀{ℓ} {A : Type ℓ} → Reflω (Paths A)
  Path-Refl .refl {x} _ = x

  Path-Sym : ∀{ℓ} {A : Type ℓ} → Symω (Paths A)
  Path-Sym .sym p i = p (~ i)

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

  Path-Extend-Path : ∀{ℓa ℓb} {A : Type ℓa} {B : {x y : A} → x ＝ y → Type ℓb}
                   → Extendω (Paths A) (λ p → Paths (B p))
  Path-Extend-Path {B} .extend-l p = transp (λ i → B λ j → p (  i ∧ j)) i0
  Path-Extend-Path {B} .extend-r p = transp (λ i → B λ j → p (~ i ∨ j)) i0

  Path-Extend-Path-Lafwul : ∀{ℓa ℓb} {A : Type ℓa} {B : {x y : A} → x ＝ y → Type ℓb}
                          → Lawful-Extendω (Paths A) (λ p → Paths (B p))
  Path-Extend-Path-Lafwul .extend-refl = refl
  Path-Extend-Path-Lafwul {B} .extend-coh {x} {u} i = hcomp (∂ i) λ where
    j (i = i0) → transp (λ _ → B λ _ → x)    j  u
    j (i = i1) → transp (λ _ → B λ _ → x) (~ j) u
    j (j = i0) → transp (λ _ → B λ _ → x)    i  u

{-# OVERLAPPING
  Path-Refl Path-Sym
#-}

{-# INCOHERENT
  Path-Push-Path Path-Push-Path-Lawful
  Path-Pull-Path Path-Lawful-Pull-Lawful
  Path-Extend-Path Path-Extend-Path-Lafwul
#-}


-- test assoc
instance
  Fun-Assoc : Assocω Funs (λ _ _ → Paths-on _)
  Fun-Assoc .assoc = refl


module _ {ℓa ℓb} {A : Type ℓa} {B : Type ℓb} {f : A → B} {g : B → A} where private
  open Quiverω Funs

  test₁ : Ob _
  test₁ = A

  test₂ : Ob _
  test₂ = B

  test₃ : Hom A B
  test₃ = f

  test₄ : Hom A A
  test₄ = refl

  test₅ : Hom A A
  test₅ = f ∙ g

  test₆ : f ∙ (g ∙ f) ＝ (f ∙ g) ∙ f
  test₆ = assoc {f = f} {g = g} {h = f} -- TODO CHECK bad inference for functions or in general?


module PathTest {ℓ} {A : Type ℓ} {x y : A} {p : x ＝ y} where private
  open Quiverω (Paths A)

  test₁ : Ob _
  test₁ = x

  test₂ : Hom y x
  test₂ = sym p

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
Posetᵈ .has-quiver-onωᵈ .Quiver-onωᵈ.Hom[_] f = Monotone f

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


-- polynomials and lenses

Lensᵈ : Quiverωᵈ Funs 1 _ _
Lensᵈ .Quiverωᵈ.Ob[_] A (ℓb , _) = A → Type ℓb
Lensᵈ .has-quiver-onωᵈ .Quiver-onωᵈ.Hom[_] {x = A} f P Q = (x : A) → Q (f x) → P x

Lenses : Quiverω 2 _ _
Lenses = ∫ Lensᵈ

Poly : (ℓa ℓb : Level) → Type (lsuc (ℓa ⊔ ℓb))
Poly ℓa ℓb = Quiverω.Ob Lenses (ℓa , ℓb , _)

Lens : ∀{ℓa ℓb ℓc ℓd} → Poly ℓa ℓb → Poly ℓc ℓd → Type (ℓa ⊔ ℓb ⊔ ℓc ⊔ ℓd)
Lens = Quiverω.Hom Lenses


-- xxtra large spans!
module _ {n : ℕ} {ℓ-ob : ℓ-sig n} {ℓ-hom : ℓ-sig² n}
  (C : Quiverω n ℓ-ob ℓ-hom) (open Quiverω C) ⦃ _ : Compω C ⦄ where

  Spanᵈ : Quiverωᵈ C (n + n) _ _
  Spanᵈ .Quiverωᵈ.Ob[_] T lsᵈ =
    let las , lbs = ℓ-split n lsᵈ
    in Σ (Ob las) λ A → Σ (Ob lbs) λ B → Hom T A × Hom T B
  Spanᵈ .has-quiver-onωᵈ .Quiver-onωᵈ.Hom[_] {x = S} {y = T} f (A₁ , B₁ , sa , sb) (A₂ , B₂ , ta , tb) =
    Σ (Hom A₁ A₂) λ fa → Σ (Hom B₁ B₂) λ fb → (f ∙ ta  ＝ sa ∙ fa) × (f ∙ tb ＝ sb ∙ fb)

  Spans : Quiverω (n + (n + n)) _ _
  Spans = ∫ Spanᵈ

-- spans of types
module FunSpan {ℓa ℓb ℓt} {A : Type ℓa} {B : Type ℓb} {T : Type ℓt} (p₁ : T → A) (p₂ : T → B) where private
  open Quiverω (Spans Funs)

  test : Ob _
  test = T , A , B , p₁ , p₂


-- deriving composition from pull
module _ {n : ℕ} {ℓ-ob : ℓ-sig n} {ℓ-hom : ℓ-sig² n}
  (C : Quiverω n ℓ-ob ℓ-hom) (open Quiverω C)
  ⦃ FP : ∀{lys} {y : Ob lys} → Pullω C λ t → Paths (Hom t y) ⦄
  ⦃ rc : Reflω C ⦄
  ⦃ FPL : ∀{lys} {y : Ob lys} → Lawful-Pullω C λ t → Paths (Hom t y) ⦄
  where private

  instance
    KEKW : Compω C
    KEKW ._∙_ = pull

  cmp-refl : ∀{lxs} {x : Ob lxs} → refl {x = x} ＝ refl ∙ refl
  cmp-refl = pull-refl

  -- -- here we need to commute pull
  -- ass : ∀{lws lxs lys lzs} {w : Ob lws} {x : Ob lxs} {y : Ob lys} {z : Ob lzs}
  --       {f : Hom w x} {g : Hom x y} {h : Hom y z}
  --     → f ∙ (g ∙ h) ＝ (f ∙ g) ∙ h
  -- ass {f} {g} {h} = {!!}
