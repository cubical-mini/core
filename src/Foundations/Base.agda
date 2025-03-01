{-# OPTIONS --safe #-}
module Foundations.Base where

import Foundations.Prim.Empty as ⊥
open ⊥ using (⊥ₜ) public
open import Foundations.Prim.Interval public
open import Foundations.Prim.Kan public
open import Foundations.Prim.Type public
import Foundations.Prim.Sum as ⊎
open ⊎ using (_⊎_; inl; inr) public

open import Foundations.Cat.Reflexivity public
open import Foundations.Cat.Composition public
open import Foundations.Cat.Diagram.Coproduct.Binary public
open import Foundations.Cat.Diagram.Coproduct.Indexed public
open import Foundations.Cat.Diagram.Exponential public
open import Foundations.Cat.Diagram.Initial public
open import Foundations.Cat.Diagram.Product.Binary public
open import Foundations.Cat.Diagram.Product.Indexed public
open import Foundations.Cat.Diagram.Terminal public
open import Foundations.Cat.Structures.Quiver public
open import Foundations.Cat.Symmetry public
open import Foundations.Cat.Underlying public

open import Agda.Builtin.Sigma public
  renaming (Σ to Σₜ)
open import Agda.Builtin.Unit public
  renaming (⊤ to ⊤ₜ)

-- We reside in the double ∞-category of types, functions and binary correspondences, let's get comfy

FunQ : Quiver
FunQ = mk-quiver (λ ℓ → Type ℓ) Fun

CorrQ : (ℓ : Level) → Quiver
CorrQ ℓ = mk-quiver (λ _ → Type ℓ) (Corr² ℓ)

instance
  Refl-Fun : Refl FunQ
  Refl-Fun .refl x = x

  Comp-Fun : Comp FunQ
  Comp-Fun ._∙_ f g x = g (f x)

  Underlying-Fun : Underlying FunQ
  Underlying-Fun .ℓ-und ℓ = ℓ
  Underlying-Fun .⌞_⌟ X = X

  Refl-Corr² : {ℓ : Level} → Refl (CorrQ ℓ)
  Refl-Corr² .refl = _＝_

  Comp-Corr² : {ℓ : Level} → Comp (CorrQ ℓ)
  Comp-Corr² ._∙_ {x = A} {y = B} {z = C} R S a c = Σₜ B λ b → Σₜ (R a b) (λ _ → S b c)

  Symmetry-Corr : {ℓ : Level} → Symmetry (CorrQ ℓ)
  Symmetry-Corr .sym R B A = R A B

{-# INCOHERENT Refl-Fun Comp-Fun Underlying-Fun
               Refl-Corr² Symmetry-Corr Comp-Corr²
#-}


module _ where
  open Initial
  open Terminal

  instance
    Initial-Fun : Initial FunQ
    Initial-Fun .⊥ = ⊥ₜ
    Initial-Fun .has-is-init _ .centre ()
    Initial-Fun .has-is-init _ .paths _ _ ()

    Terminal-Fun : Terminal FunQ
    Terminal-Fun .⊤ = ⊤ₜ
    Terminal-Fun .has-is-terminal _ .centre _ = tt
    Terminal-Fun .has-is-terminal _ .paths _ _ _ = tt
{-# INCOHERENT Initial-Fun Terminal-Fun #-}


module _ where
  open Binary-coproducts
  open Coproduct
  open Binary-products
  open Product

  instance
    Binary-coproducts-Fun : Binary-coproducts FunQ
    Binary-coproducts-Fun ._⨿_ = _⊎_
    Binary-coproducts-Fun .has-coproduct .ι₁ = inl
    Binary-coproducts-Fun .has-coproduct .ι₂ = inr
    Binary-coproducts-Fun .has-coproduct .has-is-coproduct .⁅_,_⁆ = ⊎.rec
    Binary-coproducts-Fun .has-coproduct .has-is-coproduct .⁅⁆∘ι₁ {f} _ = f
    Binary-coproducts-Fun .has-coproduct .has-is-coproduct .⁅⁆∘ι₂ {g} _ = g
    Binary-coproducts-Fun .has-coproduct .has-is-coproduct .⁅⁆-unique fs sn i (inl x) = fs i x
    Binary-coproducts-Fun .has-coproduct .has-is-coproduct .⁅⁆-unique fs sn i (inr x) = sn i x

    Binary-products-Fun : Binary-products FunQ
    Binary-products-Fun ._×_ A B = Σₜ A λ _ → B
    Binary-products-Fun .has-product .π₁ = fst
    Binary-products-Fun .has-product .π₂ = snd
    Binary-products-Fun .has-product .has-is-product .⟨_,_⟩ f g q = f q , g q
    Binary-products-Fun .has-product .has-is-product .π₁∘⟨⟩ {f} _ = f
    Binary-products-Fun .has-product .has-is-product .π₂∘⟨⟩ {g} _ = g
    Binary-products-Fun .has-product .has-is-product .⟨⟩-unique fs sn i q = fs i q , sn i q
{-# INCOHERENT Binary-coproducts-Fun Binary-products-Fun #-}

infixr 70 _⨿ₜ_
_⨿ₜ_ : {ℓa ℓb : Level} → Type ℓa → Type ℓb → Type (ℓa l⊔ ℓb)
_⨿ₜ_ = _⨿_ ⦃ _ ⦄ ⦃ Binary-coproducts-Fun ⦄
{-# INLINE _⨿ₜ_ #-}

infixr 80 _×ₜ_
_×ₜ_ : {ℓa ℓb : Level} → Type ℓa → Type ℓb → Type (ℓa l⊔ ℓb)
_×ₜ_ = _×_ ⦃ _ ⦄ ⦃ Binary-products-Fun ⦄
{-# INLINE _×ₜ_ #-}


module _ where
  open Cartesian-closed
  open Exponential

  instance
    Cartesian-closed-Fun : Cartesian-closed FunQ
    Cartesian-closed-Fun ._⇒_ = Fun
    Cartesian-closed-Fun .has-exp .ev (f , x) = f x
    Cartesian-closed-Fun .has-exp .has-is-exp .ƛ w g a = w (g , a)
    Cartesian-closed-Fun .has-exp .has-is-exp .ƛ-commutes m _ = m
    Cartesian-closed-Fun .has-exp .has-is-exp .ƛ-unique _ p i g a = p i (g , a)
    {-# INCOHERENT Cartesian-closed-Fun #-}

infixr 0 ¬ₜ_
¬ₜ_ : {ℓ : Level} → Type ℓ → Type ℓ
¬ₜ_ = ¬_ ⦃ Refl-Fun ⦄ ⦃ Comp-Fun ⦄ ⦃ Initial-Fun ⦄
{-# INLINE ¬ₜ_ #-}


-- Π
module _ where
  open Indexed-products
  open Indexed-product

  instance
    Indexed-products-Fun : {ℓi : Level} {Idx : Type ℓi} → Indexed-products FunQ Idx
    Indexed-products-Fun {Idx} .∏ B = (x : Idx) → B x
    Indexed-products-Fun .has-ip .π i f = f i
    Indexed-products-Fun .has-ip .has-is-ip .∏-tuple f y i = f i y
    Indexed-products-Fun .has-ip .has-is-ip .π-commute {f} _ = f _
    Indexed-products-Fun .has-ip .has-is-ip .∏-unique _ g j y i = g i j y
{-# INCOHERENT Indexed-products-Fun #-}

Πₜ : {ℓi ℓf : Level} (Idx : Type ℓi) → (Idx → Type ℓf) → 𝒰 (ℓi l⊔ ℓf)
Πₜ _ = ∏ ⦃ _ ⦄ ⦃ Indexed-products-Fun ⦄
{-# INLINE Πₜ #-}

flip : {ℓa ℓb ℓc : Level} {A : Type ℓa} {B : Type ℓb} {C : A → B → Type ℓc} → (∀ a b → C a b) → (∀ b a → C a b)
flip f b a = f a b
{-# INLINE flip #-}

const : {ℓa ℓb : Level} {A : Type ℓa} {B : Type ℓb} → A → @0 B → A
const x _ = x
{-# INLINE const #-}

infixr -1 _$_
_$_ : {ℓa ℓb : Level} {A : Type ℓa} {B : A → Type ℓb}
    → (f : (a : A) → B a) (x : A) → B x
f $ a = f a
{-# INLINE _$_ #-}

infixl -1 _&_
_&_ : {ℓa ℓb : Level} {A : Type ℓa} {B : A → Type ℓb}
    → (x : A) (f : (a : A) → B a) → B x
a & f = f a
{-# INLINE _&_ #-}

infixr 9 _∘ᵈ_
_∘ᵈ_ : {ℓa ℓb ℓc : Level} {A : Type ℓa} {B : A → Type ℓb} {C : (a : A) → B a → Type ℓc}
     → (g : {a : A} (b : B a) → C a b) (f : (a : A) → B a) (x : A) → C x (f x)
(g ∘ᵈ f) x = g (f x)
{-# INLINE _∘ᵈ_ #-}


-- Σ
module _ where
  open Indexed-coproducts
  open Indexed-coproduct

  instance
    Indexed-coproducts-Fun : {ℓi : Level} {Idx : Type ℓi} → Indexed-coproducts FunQ Idx
    Indexed-coproducts-Fun .∐ = Σₜ _
    Indexed-coproducts-Fun .has-ic .ι = _,_
    Indexed-coproducts-Fun .has-ic .has-is-ic .∐-match f (i , x) = f i x
    Indexed-coproducts-Fun .has-ic .has-is-ic .ι-commute {f} _ = f _
    Indexed-coproducts-Fun .has-ic .has-is-ic .∐-unique _ p j (i , x) = p i j x
{-# INCOHERENT Indexed-coproducts-Fun #-}

_ : {ℓi ℓf : Level} (Idx : Type ℓi) → (Idx → Type ℓf) → 𝒰 (ℓi l⊔ ℓf)
_ = Σₜ

bimap : {ℓa ℓb ℓ ℓ′ : Level} {A : Type ℓa} {B : A → Type ℓb} {P : A → Type ℓ} {Q : ∀ {a} → P a → B a → Type ℓ′}
      → (f : (a : A) →  B a) (g : ∀ {a} (b : P a) → Q b (f a)) (p : Σₜ A P) → Σₜ (B (p .fst)) (Q (p .snd))
bimap f g (x , y) = f x , g y
{-# INLINE bimap #-}

first : {ℓa ℓb ℓc : Level} {A : Type ℓa} {B : A → Type ℓb} {C : A → Type ℓc}
      → (f : (a : A) → B a) (p : Σₜ A C)
      → B (p .fst) ×ₜ C (p .fst)
first f = bimap f (λ x → x)
{-# INLINE first #-}

second : {ℓa ℓb ℓc : Level} {A : Type ℓa} {B : A → Type ℓb} {C : A → Type ℓc}
       → (∀ {x} → B x → C x) → Σₜ A B → Σₜ A C
second = bimap (λ x → x)
{-# INLINE second #-}

uncurry : {ℓa ℓb ℓc : Level} {A : Type ℓa} {B : A → Type ℓb} {C : (a : A) → B a → Type ℓc}
        → ((a : A) (b : B a) → C a b)
        → (p : Σₜ A B) → C (p .fst) (p .snd)
uncurry f (x , y) = f x y
{-# INLINE uncurry #-}

curry : {ℓa ℓb ℓc : Level} {A : Type ℓa} {B : A → Type ℓb} {C : (a : A) → B a → Type ℓc}
      → ((p : Σₜ A B) → C (p .fst) (p .snd))
      → (x : A) (y : B x) → C x y
curry f x y = f (x , y)
{-# INLINE curry #-}
