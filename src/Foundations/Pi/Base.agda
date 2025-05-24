{-# OPTIONS --safe #-}
module Foundations.Pi.Base where

open import Prim.Interval
open import Prim.Kan
open import Prim.Type

id : {ℓa : Level} {A : Type ℓa} → A → A
id x = x

infixr 90 _∘_
_∘_ : {ℓa ℓb ℓc : Level} {A : Type ℓa} {B : A → Type ℓb} {C : (a : A) → B a → Type ℓc}
      (g : {a : A} (b : B a) → C a b) (f : (a : A) → B a)
      (x : A) → C x (f x)
(g ∘ f) x = g (f x)


-- Path

ap : {ℓa ℓb : Level} {A : Type ℓa} {B : A → Type ℓb}
     (f : (a : A) → B a)
     {x y : A} (p : x ＝ y)
   → Pathᴾ (λ i → B (p i)) (f x) (f y)
ap f p i = f (p i)

ap² : {ℓa ℓb ℓc : Level} {A : Type ℓa} {B : A → Type ℓb} {C : (a : A) (b : B a) → Type ℓc}
      (f : (a : A) (b : B a) → C a b)
      {x y : A} (p : x ＝ y)
      {u : B x} {v : B y} (q : Pathᴾ (λ i → B (p i)) u v)
    → Pathᴾ (λ i → C (p i) (q i)) (f x u) (f y v)
ap² f p q i = f (p i) (q i)

apᴾ : {ℓa ℓb : Level} {A : I → Type ℓa} {B : (i : I) → A i → Type ℓb}
      (f : (i : I) (a : A i) → B i a)
      {x : A i0} {y : A i1} (p : Pathᴾ A x y)
    → Pathᴾ (λ i → B i (p i)) (f i0 x) (f i1 y)
apᴾ f p i = f i (p i)

fun-ext : {ℓa ℓb : Level} {A : Type ℓa} {B : A → I → Type ℓb}
          {f : (a : A) → B a i0} {g : (a : A) → B a i1}
        → ((a : A) → Pathᴾ (B a) (f a) (g a))
        → Pathᴾ (λ i → (x : A) → B x i) f g
fun-ext p i x = p x i

happly : {ℓa ℓb : Level} {A : Type ℓa} {B : A → I → Type ℓb}
         {f : (a : A) → B a i0} {g : (a : A) → B a i1}
       → Pathᴾ (λ i → (a : A) → B a i) f g
       → (x : A) → Pathᴾ (B x) (f x) (g x)
happly eq x i = eq i x
