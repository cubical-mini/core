{-# OPTIONS --safe #-}
module Foundations.Quiver.Base where

open import Prim.Data.Nat public
open import Prim.Data.Sigma public
  renaming ( Σ   to Σₜ
           ; _×_ to _×ₜ_
           )
open import Prim.Data.Unit public
open import Prim.Type public

-- vector of levels
Levels : ℕ → Type
Levels zero = ⊤
Levels (suc n) = Level ×ₜ Levels n

ℓ-split : ∀ m {m′} → Levels (m + m′) → Levels m ×ₜ Levels m′
ℓ-split 0 ls = tt , ls
ℓ-split (suc m) (l , ls) = let left , right = ℓ-split m ls in (l , left) , right

-- object level adjustment
ℓ-sig : ℕ → Type
ℓ-sig n = Levels n → Level

-- arrow level adjustment
ℓ-sig² : ℕ → ℕ → Type
ℓ-sig² m n = Levels m → ℓ-sig n

ob-sig : ∀{n} (ℓ-ob : ℓ-sig n) → Typeω
ob-sig ℓ-ob = ∀ ls → Type (ℓ-ob ls)

het-sig : ∀{m n} {ℓ-ob⁻ : ℓ-sig m} {ℓ-ob⁺ : ℓ-sig n} (Ob⁻ : ob-sig ℓ-ob⁻) (Ob⁺ : ob-sig ℓ-ob⁺) (ℓ-het : Levels m → Levels n → Level) → Typeω
het-sig Ob⁻ Ob⁺ ℓ-het = ∀{lxs lys} → Ob⁻ lxs → Ob⁺ lys → Type (ℓ-het lxs lys)

hom-sig : ∀{n} {ℓ-ob : ℓ-sig n} (Ob : ob-sig ℓ-ob) (ℓ-hom : ℓ-sig² n n) → Typeω
hom-sig Ob = het-sig Ob Ob


record Quiver-onω m n {ℓ-ob⁻ ℓ-ob⁺} (Ob⁻ : ob-sig ℓ-ob⁻) (Ob⁺ : ob-sig ℓ-ob⁺) (ℓ-het : ℓ-sig² m n) : Typeω where
  constructor mk-quiver-onω
  no-eta-equality
  field Het : het-sig Ob⁻ Ob⁺ ℓ-het

  Ob-of⁻ = Ob⁻
  Ob-of⁺ = Ob⁺

{-# INLINE mk-quiver-onω #-}

HQuiver-onω : ∀ m {ℓ-ob} (Ob : ob-sig ℓ-ob) (ℓ-hom : ℓ-sig² m m) → Typeω
HQuiver-onω m Ob = Quiver-onω m m Ob Ob
{-# NOINLINE HQuiver-onω #-}


ob-sigᵈ : ∀ {m ℓ-ob} (Ob : ob-sig ℓ-ob) {n} (ℓ-obᵈ : Levels m → ℓ-sig n) → Typeω
ob-sigᵈ Ob ℓ-obᵈ = ∀{ls} (x : Ob ls) → ob-sig (ℓ-obᵈ ls)

ob-sigᵈ² : ∀ {m n ℓ-ob⁻ ℓ-ob⁺} (Ob⁻ : ob-sig ℓ-ob⁻) (Ob⁺ : ob-sig ℓ-ob⁺) {k} (ℓ-obᵈ² : Levels m → Levels n → ℓ-sig k) → Typeω
ob-sigᵈ² Ob⁻ Ob⁺ ℓ-obᵈ² = ∀{lxs lys} (x : Ob⁻ lxs) (y : Ob⁺ lys) → ob-sig (ℓ-obᵈ² lxs lys)

module _ {m n ℓ-ob⁻ ℓ-ob⁺} (Ob⁻ : ob-sig ℓ-ob⁻) (Ob⁺ : ob-sig ℓ-ob⁺) {ℓ-het} (Het : het-sig Ob⁻ Ob⁺ ℓ-het) where
    het-sigᵈ : ∀{m′ n′ ℓ-obᵈ⁻ ℓ-obᵈ⁺} (Ob[_]⁻ : ob-sigᵈ Ob⁻ ℓ-obᵈ⁻) (Ob[_]⁺ : ob-sigᵈ Ob⁺ ℓ-obᵈ⁺) (ℓ-hetᵈ : Levels m → Levels n → ℓ-sig² m′ n′)
             → Typeω
    het-sigᵈ Ob[_]⁻ Ob[_]⁺ ℓ-hetᵈ = ∀{lxs lys} {x : Ob⁻ lxs} {y : Ob⁺ lys} (f : Het x y)
                                    {lxsᵈ lysᵈ} (x′ : Ob[ x ]⁻ lxsᵈ) (y′ : Ob[ y ]⁺ lysᵈ) → Type (ℓ-hetᵈ lxs lys lxsᵈ lysᵈ)

module _ {m ℓ-ob} (Ob : ob-sig ℓ-ob) {ℓ-hom} (Hom : hom-sig Ob ℓ-hom) where
  hom-sigᵈ : ∀{m′ ℓ-obᵈ} (Ob[_] : ob-sigᵈ Ob ℓ-obᵈ) (ℓ-homᵈ : Levels m → Levels m → ℓ-sig² m′ m′) → Typeω
  hom-sigᵈ Ob[_] = het-sigᵈ Ob Ob Hom Ob[_] Ob[_]

module _ {m n ℓ-ob⁻ ℓ-ob⁺} (Ob⁻ : ob-sig ℓ-ob⁻) (Ob⁺ : ob-sig ℓ-ob⁺) {ℓ-het} (Het : het-sig Ob⁻ Ob⁺ ℓ-het) where
    record Quiver-onωᵈ m′ n′ {ℓ-obᵈ⁻ ℓ-obᵈ⁺} (Ob[_]⁻ : ob-sigᵈ Ob⁻ ℓ-obᵈ⁻) (Ob[_]⁺ : ob-sigᵈ Ob⁺ ℓ-obᵈ⁺) (ℓ-hetᵈ : Levels m → Levels n → ℓ-sig² m′ n′) : Typeω where
      constructor mk-quiver-onωᵈ
      no-eta-equality
      field Het[_] : het-sigᵈ Ob⁻ Ob⁺ Het Ob[_]⁻ Ob[_]⁺ ℓ-hetᵈ
    {-# INLINE mk-quiver-onωᵈ #-}

module _ {m ℓ-ob} (Ob : ob-sig ℓ-ob) {ℓ-hom} (Hom : hom-sig Ob ℓ-hom) where
  HQuiver-onωᵈ : ∀ m′ {ℓ-obᵈ} (Ob[_] : ob-sigᵈ Ob ℓ-obᵈ) (ℓ-homᵈ : Levels m → Levels m → ℓ-sig² m′ m′) → Typeω
  HQuiver-onωᵈ m′ Ob[_] = Quiver-onωᵈ Ob Ob Hom m′ m′ Ob[_] Ob[_]
  {-# NOINLINE HQuiver-onωᵈ #-}


-- bundled forms

record Quiverω m n ℓ-ob⁻ ℓ-ob⁺ ℓ-het : Typeω where
  constructor mk-quiverω
  no-eta-equality
  field
    Ob⁻            : ob-sig ℓ-ob⁻
    Ob⁺            : ob-sig ℓ-ob⁺
    has-quiver-onω : Quiver-onω m n Ob⁻ Ob⁺ ℓ-het
  open Quiver-onω has-quiver-onω public
{-# INLINE mk-quiverω #-}
open Quiverω using (has-quiver-onω) public

module _ {m n ℓ-ob⁻ ℓ-ob⁺ ℓ-het} (C : Quiverω m n ℓ-ob⁻ ℓ-ob⁺ ℓ-het) (open Quiverω C) where
  record Quiverωᵈ m′ n′ ℓ-obᵈ⁻ ℓ-obᵈ⁺ ℓ-hetᵈ : Typeω where
    constructor mk-quiverωᵈ
    no-eta-equality
    field
      Ob[_]⁻          : ob-sigᵈ Ob⁻ ℓ-obᵈ⁻
      Ob[_]⁺          : ob-sigᵈ Ob⁺ ℓ-obᵈ⁺
      has-quiver-onωᵈ : Quiver-onωᵈ Ob⁻ Ob⁺ Het m′ n′ Ob[_]⁻ Ob[_]⁺ ℓ-hetᵈ
    open Quiver-onωᵈ has-quiver-onωᵈ public
  {-# INLINE mk-quiverωᵈ #-}
  open Quiverωᵈ using (has-quiver-onωᵈ) public
