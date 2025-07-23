{-# OPTIONS --safe #-}
module Push where

open import Prim.Data.List
open import Prim.Data.Maybe

open import Foundations.Quiver.Base
open import Foundations.Quiver.Discrete as Discrete
open import Foundations.Quiver.Type

open import Notation.Pull
open import Notation.Push
open import Notation.Refl

lmap : ∀{ℓa ℓb} {A : Type ℓa} {B : Type ℓb}
     → (A → B) → List A → List B
lmap _ [] = []
lmap f (x ∷ xs) = f x ∷ lmap f xs

open Discrete.Groupoid

lmap-id : ∀{ℓ} {A : Type ℓ} (xs : List A)
        → xs ＝ lmap id xs
lmap-id [] = refl
lmap-id (x ∷ xs) i = x ∷ lmap-id xs i

instance
  List-HPush : HPush Funs 0 (λ T → Disc (List T))
  List-HPush .push = lmap
  List-HPush .push-refl = lmap-id _

module _ {ℓa ℓb} {A : Type ℓa} {B : Type ℓb} where private
  test₁ test₂ : (f : A → B) → List A → List B
  test₁ f xs = xs ▷ f
  test₂ f xs = f <$> xs

data MLR {ℓ} {A : Type ℓ} : Maybe A → List A → Type ℓ where
  nothing~[]     : MLR nothing []
  just~singleton : ∀{x} → MLR (just x) (x ∷ [])

instance
  Maybe-HPush : HPush Funs 0 (λ T → Disc (Maybe T))
  Maybe-HPush .push p (just x) = just (p x)
  Maybe-HPush .push _ nothing = nothing
  Maybe-HPush .push-refl {u = just _} = refl
  Maybe-HPush .push-refl {u = nothing} = refl

  Maybe-List-Push : Push Funs 0 (λ _ → mk-quiver-onω MLR)
  Maybe-List-Push .push f (just x) = f x ∷ []
  Maybe-List-Push .push _ nothing = []
  Maybe-List-Push .push-refl {u = just x} = just~singleton
  Maybe-List-Push .push-refl {u = nothing} = nothing~[]

  -- -- now this one is bad for MLR
  -- List-Maybe-Push : Push Funs 0 λ _ → mk-quiver-onω (λ y x → MLR x y)
  -- List-Maybe-Push .push _ [] = nothing
  -- List-Maybe-Push .push f (x ∷ _) = just (f x)
  -- List-Maybe-Push .push-refl {u = []} = nothing~[]
  -- List-Maybe-Push .push-refl {u = x ∷ []} = just~singleton
  -- List-Maybe-Push .push-refl {u = x ∷ y ∷ u} = {!!} -- no no no

module _ {ℓa ℓb} {A : Type ℓa} {B : Type ℓb} (f : A → B) where
  α : ∀{ℓw} {W : Type ℓw} → Maybe W → List W
  α = push refl

  α-is-natural : (mx : Maybe A) → push f (α mx) ＝ α (push f mx)
  α-is-natural (just x) _ = f x ∷ []
  α-is-natural nothing _ = []

  -- β : ∀{ℓw} {W : Type ℓw} → List W → Maybe W
  -- β = push refl

  -- β-is-natural : (xs : List A) → push f (β xs) ＝ β (push f xs)
  -- β-is-natural [] _ = nothing
  -- β-is-natural (x ∷ _) _ = just (f x)



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
  Vec-HPush : ∀{n} → HPush Funs 0 (λ A → Disc (Vec A n))
  Vec-HPush .push = vec-map
  Vec-HPush .push-refl = vec-map-lawful _

  Vec-HPush′ : ∀{ℓ}{A : Type ℓ} → HPush (Disc ℕ) 0 (λ n → Disc (Vec A n))
  Vec-HPush′ .push = vec-cast
  Vec-HPush′ .push-refl = vec-cast-lawful _

ex : ∀{ℓa ℓb} {A : Type ℓa} {B : Type ℓb}
     {m n}(p : m ＝ n) (f : A → B)
   → Vec A m → Vec B n
ex p f xs = xs ▷ f ▷ p
