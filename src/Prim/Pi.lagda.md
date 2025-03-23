```agda

{-# OPTIONS --safe #-}

module Prim.Pi where

open import Prim.Base.Type
open import Prim.Base.Interval using ( PathP; _≡_; I; i0; i1 )

infixr 40 _∘_
infixr -1 _$_
infixl -1 _&_

Π : ∀ {u v} {A : Type u} (B : A → Type v) → Type (u ⊔ v)
Π {A = A} B = (x : A) → B x

pi-syntax : ∀ {u v} (A : Type u) (B : A → Type v) → Type (u ⊔ v)
pi-syntax A = Π {A = A}
syntax pi-syntax A (λ x → M) = Π x ꞉ A , M
{-# DISPLAY pi-syntax _ B = Π B #-}

Fun : ∀ {u v} → Type u → Type v → Type (u ⊔ v)
Fun A B = A → B

-- Wild natural transformations
Nt : ∀ {u v w} {X : Type u} → (X → Type v) → (X → Type w) → Type (u ⊔ v ⊔ w)
Nt A B = ∀ x → A x → B x

id : ∀ {u} {A : Type u} → A → A
id = λ x → x
{-# INLINE id #-}

idfun : ∀ {u} (A : Type u) → A → A
idfun A = λ x → x
{-# INLINE id #-}

const : ∀ {u v} {A : Type u} {B : Type v} → A → B → A
const a ._ = a
{-# INLINE const #-}

flip : ∀ {u v w} {A : Type u} {B : Type v} {C : Type w}
     → (A → B → C) → (B → A → C)
flip f = λ x y → f y x
{-# INLINE flip #-}

flipd : ∀ {u v w : Level} {A : Type u} {B : Type v} {C : A → B → Type w}
      → (∀ a b → C a b) → (∀ b a → C a b)
flipd f b a = f a b
{-# INLINE flipd #-}

-- S-combinator
_∘_ : ∀ {u v w} {A : Type u} {B : A → Type v} {C : (x : A) → B x → Type w}
    → ({x : A} (y : B x) → C x y) → (f : (x : A) → B x) (x : A) → C x (f x)
g ∘ f = λ x → g (f x)
{-# INLINE _∘_ #-}

_∘ₛ_ : ∀ {u v w} {A : Type u} {B : Type v} {C : B → Type w}
     → ((y : B) → C y) → (f : A → B) (x : A) → C (f x)
_∘ₛ_ g f = λ x → g (f x)
{-# INLINE _∘ₛ_ #-}

_$_ : ∀ {u v} {A : Type u} {B : A → Type v}
    → (f : (a : A) → B a) (x : A) → B x
f $ a = f a
{-# INLINE _$_ #-}

_$ᵢ_ : ∀ {ℓ} {A : I → Type ℓ} {a : A i0} {b : A i1} → PathP A a b → (i : I) → A i
p $ᵢ i = p i
{-# INLINE _$ᵢ_ #-}

_&_ : ∀ {u v} {A : Type u} {B : A → Type v}
    → (x : A) (f : (a : A) → B a) → B x
a & f = f a
{-# INLINE _&_ #-}

auto : ∀ {ℓ} {A : Type ℓ} → ⦃ A ⦄ → A
auto ⦃ (a) ⦄ = a

autoω : {A : Typeω} → ⦃ A ⦄ → A
autoω ⦃ (a) ⦄ = a

-- Explicit type hint
the : ∀ {ℓ} (A : Type ℓ) → A → A
the _ a = a

```

# To sort

import Lib.Empty as ⊥
open ⊥ using (⊥ₜ) public
open import Prim.Interval public
open import Prim.Kan public
open import Prim.Type public
import Lib.Sum as ⊎
open ⊎ using (_⊎_; inl; inr) public

open import Control.Reflexivity public
open import Control.Composition public
open import Control.Diagram.Coproduct.Binary public
open import Control.Diagram.Coproduct.Indexed public
open import Control.Diagram.Exponential public
open import Control.Diagram.Initial public
open import Control.Diagram.Product.Binary public
open import Control.Diagram.Product.Indexed public
open import Control.Diagram.Terminal public
open import Control.Structures.Quiver public
open import Control.Symmetry public
open import Control.Underlying public

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

  Refl-Corr² : ∀ {ℓ} → Refl (CorrQ ℓ)
  Refl-Corr² .refl = _≡_

  Comp-Corr² : ∀ {ℓ} → Comp (CorrQ ℓ)
  Comp-Corr² ._∙_ {x = A} {y = B} {z = C} R S a c = Σₜ B λ b → Σₜ (R a b) (λ _ → S b c)

  Symmetry-Corr : ∀ {ℓ} → Symmetry (CorrQ ℓ)
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
_⨿ₜ_ : ∀ {u v} → Type u → Type v → Type (u ⊔ v)
_⨿ₜ_ = _⨿_ ⦃ _ ⦄ ⦃ Binary-coproducts-Fun ⦄
{-# INLINE _⨿ₜ_ #-}

infixr 80 _×ₜ_
_×ₜ_ : ∀ {u v} → Type u → Type v → Type (u ⊔ v)
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
¬ₜ_ : ∀ {ℓ} → Type ℓ → Type ℓ
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



Corr² : ∀ {u v} ℓ → Type u → Type v → Type (u ⊔ v ⊔ ℓ ₊)
Corr² ℓ A B = A → B → Type ℓ

Πₜ : {ℓi ℓf : Level} (Idx : Type ℓi) → (Idx → Type ℓf) → Type (ℓi ⊔ ℓf)
Πₜ _ = ∏ ⦃ _ ⦄ ⦃ Indexed-products-Fun ⦄
{-# INLINE Πₜ #-}

infixr 9 _∘ᵈ_
_∘ᵈ_ : {u v ℓc : Level} {A : Type u} {B : A → Type v} {C : (a : A) → B a → Type ℓc}
     → (g : {a : A} (b : B a) → C a b) (f : (a : A) → B a) (x : A) → C x (f x)
(g ∘ᵈ f) x = g (f x)
{-# INLINE _∘ᵈ_ #-}

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

_ : {ℓi ℓf : Level} (Idx : Type ℓi) → (Idx → Type ℓf) → Type (ℓi ⊔ ℓf)
_ = Σₜ

bimap : {u v ℓ ℓ′ : Level} {A : Type u} {B : A → Type v} {P : A → Type ℓ} {Q : ∀ {a} → P a → B a → Type ℓ′}
      → (f : (a : A) →  B a) (g : ∀ {a} (b : P a) → Q b (f a)) (p : Σₜ A P) → Σₜ (B (p .fst)) (Q (p .snd))
bimap f g (x , y) = f x , g y
{-# INLINE bimap #-}

first : {u v ℓc : Level} {A : Type u} {B : A → Type v} {C : A → Type ℓc}
      → (f : (a : A) → B a) (p : Σₜ A C)
      → B (p .fst) ×ₜ C (p .fst)
first f = bimap f (λ x → x)
{-# INLINE first #-}

second : {u v ℓc : Level} {A : Type u} {B : A → Type v} {C : A → Type ℓc}
       → (∀ {x} → B x → C x) → Σₜ A B → Σₜ A C
second = bimap (λ x → x)
{-# INLINE second #-}

uncurry : {u v ℓc : Level} {A : Type u} {B : A → Type v} {C : (a : A) → B a → Type ℓc}
        → ((a : A) (b : B a) → C a b)
        → (p : Σₜ A B) → C (p .fst) (p .snd)
uncurry f (x , y) = f x y
{-# INLINE uncurry #-}

curry : {u v ℓc : Level} {A : Type u} {B : A → Type v} {C : (a : A) → B a → Type ℓc}
      → ((p : Σₜ A B) → C (p .fst) (p .snd))
      → (x : A) (y : B x) → C x y
curry f x y = f (x , y)
{-# INLINE curry #-}
