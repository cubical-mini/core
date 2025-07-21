{-# OPTIONS --safe #-}
module Push where

open import Prim.Data.List
open import Prim.Data.Maybe

open import Foundations.Quiver.Base
open import Foundations.Quiver.Discrete
open import Foundations.Quiver.Type

open import Notation.Pull
open import Notation.Push
open import Notation.Refl

lmap : ∀{ℓa ℓb} {A : Type ℓa} {B : Type ℓb}
     → (A → B) → List A → List B
lmap _ [] = []
lmap f (x ∷ xs) = f x ∷ lmap f xs


instance
  push-list-list : HPushω Funs 0 (λ A _ → List A)
  push-list-list .push = lmap

  lawful-push-list-list : Lawful-Pushω Funs (λ A → Disc (List A))
  lawful-push-list-list .push-refl {x = A} {u = xs} = {!!}

  push-maybe-maybe : HPushω Funs 0 (λ A _ → Maybe A)
  push-maybe-maybe .push p (just x) = just (p x)
  push-maybe-maybe .push _ nothing  = nothing

  lawful-push-maybe-maybe : Lawful-Pushω Funs (λ A → Disc (Maybe A))
  lawful-push-maybe-maybe .push-refl {u = just x}  _ = just x
  lawful-push-maybe-maybe .push-refl {u = nothing} _ = nothing

  push-maybe-list : Pushω Funs 0 (λ A _ → Maybe A) (λ A _ → List A)
  push-maybe-list .push f (just x) = f x ∷ []
  push-maybe-list .push _ nothing = []

  push-list-maybe : Pushω Funs 0 (λ A _ → List A) (λ A _ → Maybe A)
  push-list-maybe .push f [] = nothing
  push-list-maybe .push f (x ∷ _) = just (f x)

  -- lol it's not really bad
  bad-push : Pushω Funs 0 (λ A _ → List A) (λ A _ → Maybe A)
  bad-push .push f [] = nothing
  bad-push .push f (x ∷ []) = just (f x)
  bad-push .push f (x ∷ y ∷ xs) = just (f y)

  -- lawful-push-maybe-list : Lawful-Pushω funs-on (λ A → mk-quiver-onω (λ mx xs → push ⦃ push-maybe-list ⦄ refl mx ＝ xs)) ⦃ auto ⦄ ⦃ push-maybe-list ⦄
  -- lawful-push-maybe-list .push-refl {u} _ = push (λ x → x) u

  -- lawful-push-list-maybe : Lawful-Pushω funs-on (λ A → mk-quiver-onω (λ xs mx → push ⦃ push-list-maybe ⦄ refl xs ＝ mx)) ⦃ auto ⦄ ⦃ push-list-maybe ⦄
  -- lawful-push-list-maybe .push-refl {u} _ = push (λ x → x) u

module _ {ℓa ℓb} {A : Type ℓa} {B : Type ℓb} (f : A → B) where
  α : ∀{ℓw} {W : Type ℓw} → Maybe W → List W
  α = push ⦃ push-maybe-list ⦄ refl

  α-is-natural : (mx : Maybe A) → push f (α mx) ＝ α (push f mx)
  α-is-natural (just x) _ = f x ∷ []
  α-is-natural nothing _ = []

  β : ∀{ℓw} {W : Type ℓw} → List W → Maybe W
  β = push ⦃ push-list-maybe ⦄ refl

  β-is-natural : (xs : List A) → push f (β xs) ＝ β (push f xs)
  β-is-natural [] _ = nothing
  β-is-natural (x ∷ _) _ = just (f x)

  γ : ∀{ℓw} {W : Type ℓw} → List W → Maybe W
  γ = push ⦃ bad-push ⦄ refl

  γ-is-natural : (xs : List A) → γ xs ▷ f ＝ γ (xs ▷ f)
  γ-is-natural [] = refl
  γ-is-natural (x ∷ []) = refl
  γ-is-natural (x ∷ x₁ ∷ xs) = refl

data Vec {ℓ} (A : Type ℓ) : ℕ → Type ℓ where
  []  : Vec A 0
  _∷_ : ∀{n} → A → Vec A n → Vec A (suc n)

vec-cast : ∀{ℓ}{A : Type ℓ} {m n} (p : m ＝ n) → Vec A m → Vec A n
vec-cast {m = 0}     {n = 0}     _ xs = xs
vec-cast {m = 0}     {n = suc n} p xs = {!!}
vec-cast {m = suc m} {n = 0}     p xs = {!!}
vec-cast {m = suc m} {n = suc n} p (x ∷ xs) = x ∷ vec-cast {!!} xs

vec-map : ∀{ℓa ℓb} {A : Type ℓa} {B : Type ℓb} {n} (f : A → B) → Vec A n → Vec B n
vec-map {n = 0}     _ _        = []
vec-map {n = suc n} f (x ∷ xs) = f x ∷ vec-map f xs

vec-map-lawful : ∀{ℓa} {A : Type ℓa} {n} (xs : Vec A n) → xs ＝ vec-map (λ x → x) xs
vec-map-lawful [] = refl
vec-map-lawful (x ∷ xs) i = x ∷ vec-map-lawful xs i

vec-cast-lawful : ∀{ℓa} {A : Type ℓa} {n} (xs : Vec A n) → xs ＝ vec-cast refl xs
vec-cast-lawful [] = refl
vec-cast-lawful (x ∷ xs) i = x ∷ vec-cast-lawful xs i

instance
  push-vec-vec : ∀{n} → HPushω Funs 0 (λ A _ → Vec A n)
  push-vec-vec .push = vec-map

  lawful-push-vec-vec : ∀{n} → Lawful-Pushω Funs λ A → Disc (Vec A n)
  lawful-push-vec-vec .push-refl = vec-map-lawful _

  push-vec-vec′ : ∀{ℓ}{A : Type ℓ} → HPushω (Disc ℕ) 0 (λ n _ → Vec A n)
  push-vec-vec′ .push = vec-cast

  lawful-push-vec-vec′ : ∀{ℓ}{A : Type ℓ} → Lawful-Pushω (Disc ℕ) λ n → Disc (Vec A n)
  lawful-push-vec-vec′ .push-refl = vec-cast-lawful _

ex : ∀{ℓa ℓb} {A : Type ℓa} {B : Type ℓb}
     {m n}(p : m ＝ n) (f : A → B)
   → Vec A m → Vec B n
ex p f xs = xs ▷ f ▷ p
