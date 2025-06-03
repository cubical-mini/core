{-# OPTIONS --safe #-}
module Foundations.Pi.Base where

open import Prim.Type

Fun : ∀{ℓa ℓb} → Type ℓa → Type ℓb → Type (ℓa l⊔ ℓb)
Fun A B = A → B

DFun : ∀{ℓa ℓb} (A : Type ℓa) → (A → Type ℓb) → Type (ℓa l⊔ ℓb)
DFun A B = (a : A) → B a

id : ∀{ℓa} {A : Type ℓa} → A → A
id x = x

infixr 90 _∘_
_∘_ : ∀{ℓa ℓb ℓc} {A : Type ℓa} {B : A → Type ℓb} {C : (a : A) → B a → Type ℓc}
      (g : {a : A} (b : B a) → C a b) (f : (a : A) → B a)
      (x : A) → C x (f x)
(g ∘ f) x = g (f x)

flip : ∀{ℓa ℓb ℓc} {A : Type ℓa} {B : Type ℓb} {C : A → B → Type ℓc}
     → (∀ a b → C a b) → (∀ b a → C a b)
flip f y x = f x y
{-# INLINE flip #-}

implicit : ∀{ℓa ℓb} {A : Type ℓa} {B : A → Type ℓb}
         → ((a : A) → B a) → ({x : A} → B x)
implicit f {x} = f x
{-# INLINE implicit #-}

explicit : ∀{ℓa ℓb} {A : Type ℓa} {B : A → Type ℓb}
         → ({a : A} → B a) → ((x : A) → B x)
explicit f x = f {x}
{-# INLINE explicit #-}

infixr -1 _$_
_$_ : ∀{ℓa ℓb} {A : Type ℓa} {B : A → Type ℓb}
    → (f : (a : A) → B a) (x : A) → B x
f $ a = f a
{-# INLINE _$_ #-}

infixl -1 _&_
_&_ : ∀{ℓa ℓb} {A : Type ℓa} {B : A → Type ℓb}
    → (x : A) (f : (a : A) → B a) → B x
a & f = f a
{-# INLINE _&_ #-}
