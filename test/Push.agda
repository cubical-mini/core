{-# OPTIONS --safe --erased-cubical #-}
module Push where

open import Prim.Data.List
open import Prim.Data.Maybe
open import Prim.Interval
open import Prim.Kan

open import Foundations.Quiver.Base
open import Foundations.Quiver.Discrete

open import Notation.Refl
open import Notation.Lens.Pull
open import Notation.Lens.Push
-- open import Notation.Lens.Divariant

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
  push-list-list : HPushω funs-on 0 (λ A _ → List A)
  push-list-list .push = lmap

  lawful-push-list-list : Lawful-Pushω funs-on (λ A → Disc (List A))
  lawful-push-list-list .push-refl {x = A} {u = xs} = {!!}

  push-maybe-maybe : HPushω funs-on 0 (λ A _ → Maybe A)
  push-maybe-maybe .push p (just x) = just (p x)
  push-maybe-maybe .push _ nothing  = nothing

  lawful-push-maybe-maybe : Lawful-Pushω funs-on (λ A → Disc (Maybe A))
  lawful-push-maybe-maybe .push-refl {u = just x}  _ = just x
  lawful-push-maybe-maybe .push-refl {u = nothing} _ = nothing

  push-maybe-list : Pushω funs-on 0 (λ A _ → Maybe A) (λ A _ → List A)
  push-maybe-list .push f (just x) = f x ∷ []
  push-maybe-list .push _ nothing = []

  push-list-maybe : Pushω funs-on 0 (λ A _ → List A) (λ A _ → Maybe A)
  push-list-maybe .push f [] = nothing
  push-list-maybe .push f (x ∷ _) = just (f x)

  -- lol it's not really bad
  bad-push : Pushω funs-on 0 (λ A _ → List A) (λ A _ → Maybe A)
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

  γ-is-natural : (xs : List A) → push f (γ xs) ＝ γ (push f xs)
  γ-is-natural [] = {!!}
  γ-is-natural (x ∷ []) = {!!}
  γ-is-natural (x ∷ x₁ ∷ xs) = {!!}

  -- dimap-fun : Profunctorω funs-on funs-on 0 (λ A B _ → A → B) (λ A B _ → A → B)
  -- dimap-fun .dimap = λ z₁ z₂ z₃ z₄ → z₂ (z₃ (z₁ z₄))

  -- dimap-lawful : Lawful-Profunctorω funs-on funs-on (λ A B → Disc (A → B))
  -- dimap-lawful .dimap-refl {u} _ = u

-- module _ {m ℓ-ob ℓ-hom} {Ob : ob-sig ℓ-ob}
--   (C : HQuiver-onω m Ob ℓ-hom) (open Quiver-onω C renaming (Het to Hom))
--   n
--   {ℓ-obᶠ⁻ ℓ-obᶠ⁺ : Levels m → ℓ-sig n}
--   {ℓ-hetᶠ : Levels m → ℓ-sig² n n}
--   {Ob[_]⁻ : ∀{ls} → Ob ls → ob-sig (ℓ-obᶠ⁻ ls)}
--   {Ob[_]⁺ : ∀{ls} → Ob ls → ob-sig (ℓ-obᶠ⁺ ls)}
--   (F : ∀{ls} (t : Ob ls) → Quiver-onω n n Ob[ t ]⁻ Ob[ t ]⁺ (ℓ-hetᶠ ls))
--   ⦃ _ : Reflω C ⦄
--   ⦃ _ : Pullω C n Ob[_]⁻ Ob[_]⁺ ⦄ ⦃ _ : Lawful-Pullω C F ⦄
--   ⦃ _ : Pushω C n Ob[_]⁻ Ob[_]⁺ ⦄ ⦃ _ : Lawful-Pushω C F ⦄
--   (φ⁻ : ∀{ls lsᶠ} {x : Ob ls} → Ob[ x ]⁻ lsᶠ → Ob[ x ]⁻ lsᶠ)
--   (φ⁺ : ∀{ls lsᶠ} {x : Ob ls} → Ob[ x ]⁺ lsᶠ → Ob[ x ]⁺ lsᶠ)
--   where
--   private module F {ls} t = Quiver-onω (F {ls} t)

--   -- lax paranaturality
--   Paranatural : ∀{ls lsᵈ} {x : Ob ls} (p : Hom x x) (d₀ : Ob[ x ]⁻ lsᵈ) (d₁ : Ob[ x ]⁺ lsᵈ) → Type (ℓ-hetᶠ ls lsᵈ lsᵈ)
--   Paranatural {x} p d₀ d₁ = F.Het x (pull p d₁) (push p d₀)
--                           → F.Het x (pull p (φ⁺ d₁)) (push p (φ⁻ d₀))
