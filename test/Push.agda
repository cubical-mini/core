{-# OPTIONS --safe --erased-cubical #-}
module Push where

open import Prim.Data.List
open import Prim.Data.Maybe
open import Prim.Interval
open import Prim.Kan

open import Foundations.Quiver.Base
open import Foundations.Quiver.Discrete

open import Notation.Refl
open import Notation.Lens.Covariant

funs-on : HQuiver-onω 1 (λ (ℓ , tt) → Type ℓ) _
funs-on .Quiver-onω.Het A B = A → B


instance
  funs-refl : Reflω funs-on
  funs-refl .refl x = x

lmap : ∀{ℓa ℓb} {A : Type ℓa} {B : Type ℓb}
     → (A → B) → List A → List B
lmap _ [] = []
lmap f (x ∷ xs) = f x ∷ lmap f xs


instance
  push-list-list : Pushω funs-on 0 (λ A _ → List A) (λ A _ → List A)
  push-list-list .push = lmap

  lawful-push-list-list : Lawful-Pushω funs-on (λ A → Disc (List A))
  lawful-push-list-list .push-refl {x = A} {u = xs} = {!!}

  push-maybe-maybe : Pushω funs-on 0 (λ A _ → Maybe A) (λ A _ → Maybe A)
  push-maybe-maybe .push p (just x) = just (p x)
  push-maybe-maybe .push _ nothing  = nothing

  lawful-push-maybe-maybe : Lawful-Pushω funs-on (λ A → Disc (Maybe A))
  lawful-push-maybe-maybe .push-refl {u = just x}  _ = just x
  lawful-push-maybe-maybe .push-refl {u = nothing} _ = nothing

  push-maybe-list : Pushω funs-on 0 (λ A _ → Maybe A) (λ A _ → List A)
  push-maybe-list .push f (just x) = f x ∷ []
  push-maybe-list .push _ nothing = []

  -- non-parametric, this is unlawful
  push-list-maybe : Pushω funs-on 0 (λ A _ → List A) (λ A _ → Maybe A)
  push-list-maybe .push f [] = nothing
  push-list-maybe .push f (x ∷ _) = just (f x)

  lawful-push-maybe-list : Lawful-Pushω funs-on (λ A → mk-quiver-onω (λ mx xs → push ⦃ push-maybe-list ⦄ refl mx ＝ xs)) ⦃ auto ⦄ ⦃ push-maybe-list ⦄
  lawful-push-maybe-list .push-refl {u} _ = push (λ x → x) u
