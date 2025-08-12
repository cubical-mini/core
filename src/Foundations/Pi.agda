{-# OPTIONS --safe #-}
module Foundations.Pi where

open import Foundations.Quiver.Base

id : ∀{ℓ} {A : Type ℓ} → A → A
id x = x

infixr 900 _∘_
_∘_ : ∀{ℓa ℓb ℓc} {A : Type ℓa} {B : A → Type ℓb} {C : (a : A) → B a → Type ℓc}
      (g : {a : A} (b : B a) → C a b) (f : (a : A) → B a) (x : A) → C x (f x)
(g ∘ f) x = g (f x)

flip : ∀{ℓa ℓb ℓc} {A : Type ℓa} {B : Type ℓb} {C : A → B → Type ℓc}
     → (∀ a b → C a b) → (∀ b a → C a b)
flip f y x = f x y

infixr -1 _$_
_$_ : ∀{ℓa ℓb} {A : Type ℓa} {B : A → Type ℓb}
    → (f : (a : A) → B a) (x : A) → B x
f $ a = f a

infixl -1 _&_
_&_ : ∀{ℓa ℓb} {A : Type ℓa} {B : A → Type ℓb}
    → (x : A) (f : (a : A) → B a) → B x
a & f = f a
