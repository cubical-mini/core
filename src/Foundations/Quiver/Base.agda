{-# OPTIONS --safe #-}
module Foundations.Quiver.Base where

open import Prim.Data.Nat public
open import Prim.Data.Sigma public
open import Prim.Data.Unit public
open import Prim.Type public

-- vector of levels
Levels : ℕ → Type
Levels zero = ⊤
Levels (suc n) = Σ Level λ _ →  Levels n

-- object level adjustment
ℓ-sig : ℕ → Type
ℓ-sig n = Levels n → Level

-- arrow level adjustment
ℓ-sig² : ℕ → Type
ℓ-sig² n = Levels n → ℓ-sig n

ob-sig : ∀{n} (ℓ-ob : ℓ-sig n) → Typeω
ob-sig ℓ-ob = ∀ ls → Type (ℓ-ob ls)

fun-sig : ∀{n} {ℓ-ob₁ : ℓ-sig n} {ℓ-ob₂ : ℓ-sig n} (A : ob-sig ℓ-ob₁) (B : ob-sig ℓ-ob₂) → Typeω
fun-sig A B = ∀{ls} → A ls → B ls

hom-sig : ∀{n} {ℓ-ob : ℓ-sig n} (Ob : ob-sig ℓ-ob) (ℓ-hom : ℓ-sig² n) → Typeω
hom-sig Ob ℓ-hom = ∀{lxs lys} → Ob lxs → Ob lys → Type (ℓ-hom lxs lys)

record Quiver-onω n {ℓ-ob} (Ob : ob-sig ℓ-ob) (ℓ-hom : ℓ-sig² n) : Typeω where
  constructor mk-quiver-onω
  no-eta-equality
  field Hom : hom-sig Ob ℓ-hom
{-# INLINE mk-quiver-onω #-}

corr²→quiver-onω : ∀{ℓa ℓr} {A : Type ℓa} (R : A → A → Type ℓr) → Quiver-onω 0 (λ _ → A) (λ _ _ → ℓr)
corr²→quiver-onω R .Quiver-onω.Hom = R

record Quiverω n ℓ-ob ℓ-hom : Typeω where
  constructor mk-quiverω
  no-eta-equality
  field
    Ob             : ob-sig ℓ-ob
    has-quiver-onω : Quiver-onω n Ob ℓ-hom
  open Quiver-onω has-quiver-onω public
{-# INLINE mk-quiverω #-}
open Quiverω using (has-quiver-onω) public


module _ {n ℓ-ob ℓ-hom} (C : Quiverω n ℓ-ob ℓ-hom) (open Quiverω C) where
  2-Quiver-onω : (ℓ-hom₂ : ℓ-sig² n) → Typeω
  2-Quiver-onω ℓ-hom₂ = ∀{lxs lys} (x : Ob lxs) (y : Ob lys) → Quiver-onω 0 (λ _ → Hom x y) (λ _ _ → ℓ-hom₂ lxs lys)

  module _ {ℓ-hom₂} (C₂ : 2-Quiver-onω ℓ-hom₂) where
    private open module C₂ {lxs} {lys} {x} {y} = Quiver-onω (C₂ {lxs} {lys} x y)
              renaming (Hom to 2-Hom)

    3-Quiver-onω : (ℓh₃ : ℓ-sig² n) → Typeω
    3-Quiver-onω ℓh₃ = ∀{lxs lys} {x : Ob lxs} {y : Ob lys} (f g : Hom x y) → Quiver-onω 0 (λ _ → 2-Hom f g) (λ _ _ → ℓh₃ lxs lys)


module _ {n ℓ-ob} (Ob : ob-sig ℓ-ob) where
  ob-sigᵈ : ∀{m} (ℓ-obᵈ : Levels n → ℓ-sig m) → Typeω
  ob-sigᵈ ℓ-obᵈ = ∀{ls} (x : Ob ls) lsᵈ → Type (ℓ-obᵈ ls lsᵈ)

  module _ {ℓ-hom} (Hom : hom-sig Ob ℓ-hom) where
    hom-sigᵈ : ∀{m ℓ-obᵈ} (Ob[_] : ob-sigᵈ ℓ-obᵈ) (ℓ-homᵈ : Levels n → Levels n → ℓ-sig² m)
             → Typeω
    hom-sigᵈ Ob[_] ℓ-homᵈ = ∀{lxs lys} {x : Ob lxs} {y : Ob lys} (f : Hom x y)
                            {lxsᵈ lysᵈ} (x′ : Ob[ x ] lxsᵈ) (y′ : Ob[ y ] lysᵈ) → Type (ℓ-homᵈ lxs lys lxsᵈ lysᵈ)

    record Quiver-onωᵈ m {ℓ-obᵈ} (Ob[_] : ob-sigᵈ ℓ-obᵈ) (ℓ-homᵈ : Levels n → Levels n → ℓ-sig² m) : Typeω where
      constructor mk-quiver-onωᵈ
      no-eta-equality
      field Hom[_] : hom-sigᵈ Ob[_] ℓ-homᵈ
    {-# INLINE mk-quiver-onωᵈ #-}

module _ {n ℓ-ob ℓ-hom} (C : Quiverω n ℓ-ob ℓ-hom) (open Quiverω C) where
  record Quiverωᵈ m ℓ-obᵈ ℓ-homᵈ : Typeω where
    constructor mk-quiverωᵈ
    no-eta-equality
    field
      Ob[_]           : ob-sigᵈ Ob ℓ-obᵈ
      has-quiver-onωᵈ : Quiver-onωᵈ Ob Hom m Ob[_] ℓ-homᵈ
    open Quiver-onωᵈ has-quiver-onωᵈ public
  {-# INLINE mk-quiverωᵈ #-}
open Quiverωᵈ using (has-quiver-onωᵈ) public
