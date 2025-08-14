{-# OPTIONS --safe #-}
module Foundations.Base where

open import Prim.Data.Nat public
open import Prim.Data.Sigma public
  renaming ( Σ   to Σₜ
           ; _×_ to _×ₜ_ )
open import Prim.Data.Unit public
  renaming ( ⊤ to ⊤ₜ )
open import Prim.Type public

TVec : ∀{ℓ} (A : Type ℓ) → ℕ → Type ℓ
TVec _ 0       = Lift _ ⊤ₜ
TVec A (suc n) = A ×ₜ TVec A n

Levels : ℕ → Type
Levels = TVec Level

ℓ-split : ∀ m {m′} → Levels (m + m′) → Levels m ×ₜ Levels m′
ℓ-split 0 ls = _ , ls
ℓ-split (suc m) (l , ls) = let left , right = ℓ-split m ls in (l , left) , right

ℓ-sig : (m : ℕ) → TVec ℕ m → Type
ℓ-sig zero ns = Level
ℓ-sig (suc m) (n , ns) = Levels n → ℓ-sig _ ns


ob-sig : ∀{m} (ℓ-ob : ℓ-sig 1 (m , _)) → Typeω
ob-sig ℓ-ob = ∀ ls → Type (ℓ-ob ls)

het-sig : ∀{m ℓ-ob⁻} (Ob⁻ : ob-sig ℓ-ob⁻) {n ℓ-ob⁺} (Ob⁺ : ob-sig ℓ-ob⁺) (ℓ-het : ℓ-sig 2 (m , n , _)) → Typeω
het-sig Ob⁻ Ob⁺ ℓ-het = ∀{lxs lys} → Ob⁻ lxs → Ob⁺ lys → Type (ℓ-het lxs lys)

record Quiver-onω m {ℓ-ob⁻} (Ob⁻ : ob-sig ℓ-ob⁻) n {ℓ-ob⁺} (Ob⁺ : ob-sig ℓ-ob⁺) (ℓ-het : ℓ-sig 2 (m , n , _)) : Typeω where
  constructor mk-quiver-onω
  no-eta-equality
  field Het : het-sig Ob⁻ Ob⁺ ℓ-het

  In  = Ob⁻
  Out = Ob⁺

{-# INLINE mk-quiver-onω #-}

HQuiver-onω : ∀ m {ℓ-ob} (Ob : ob-sig ℓ-ob) (ℓ-hom : ℓ-sig 2 (m , m , _)) → Typeω
HQuiver-onω m Ob = Quiver-onω m Ob m Ob
{-# NOINLINE HQuiver-onω #-}


ob-sigᵈ : ∀{m ℓ-ob} (Ob : ob-sig ℓ-ob) {n} (ℓ-obᵈ : ℓ-sig 2 (m , n , _)) → Typeω
ob-sigᵈ Ob ℓ-obᵈ = ∀{ls} (x : Ob ls) → ob-sig (ℓ-obᵈ ls)

ob-sigᵈ² : ∀{m ℓ-ob⁻} (Ob⁻ : ob-sig ℓ-ob⁻) {n ℓ-ob⁺} (Ob⁺ : ob-sig ℓ-ob⁺) {k} (ℓ-obᵈ² : ℓ-sig 3 (m , n , k , _)) → Typeω
ob-sigᵈ² Ob⁻ Ob⁺ ℓ-obᵈ² = ∀{lxs lys} (x : Ob⁻ lxs) (y : Ob⁺ lys) → ob-sig (ℓ-obᵈ² lxs lys)

module _ {m ℓ-ob⁻} (Ob⁻ : ob-sig ℓ-ob⁻) {n ℓ-ob⁺} (Ob⁺ : ob-sig ℓ-ob⁺) {ℓ-het} (Het : het-sig Ob⁻ Ob⁺ ℓ-het) where
    het-sigᵈ : ∀{m′ ℓ-obᵈ⁻} (Ob[_]⁻ : ob-sigᵈ Ob⁻ ℓ-obᵈ⁻) {n′ ℓ-obᵈ⁺} (Ob[_]⁺ : ob-sigᵈ Ob⁺ ℓ-obᵈ⁺)
               (ℓ-hetᵈ : ℓ-sig 4 (m , n , m′ , n′ , _)) → Typeω
    het-sigᵈ Ob[_]⁻ Ob[_]⁺ ℓ-hetᵈ = ∀{lxs lys} {x : Ob⁻ lxs} {y : Ob⁺ lys} (f : Het x y)
                                    {lxsᵈ lysᵈ} (x′ : Ob[ x ]⁻ lxsᵈ) (y′ : Ob[ y ]⁺ lysᵈ) → Type (ℓ-hetᵈ lxs lys lxsᵈ lysᵈ)

module _ {m ℓ-ob⁻} {Ob⁻ : ob-sig ℓ-ob⁻} {n ℓ-ob⁺} {Ob⁺ : ob-sig ℓ-ob⁺} {ℓ-het}
  (C : Quiver-onω m Ob⁻ n Ob⁺ ℓ-het) (open Quiver-onω C) where
    record Quiver-onωᵈ m′ {ℓ-obᵈ⁻} (Ob[_]⁻ : ob-sigᵈ Ob⁻ ℓ-obᵈ⁻) n′ {ℓ-obᵈ⁺} (Ob[_]⁺ : ob-sigᵈ Ob⁺ ℓ-obᵈ⁺)
      (ℓ-hetᵈ : ℓ-sig 4 (m , n , m′ , n′ , _)) : Typeω where
      constructor mk-quiver-onωᵈ
      no-eta-equality
      field Het[_] : het-sigᵈ Ob⁻ Ob⁺ Het Ob[_]⁻ Ob[_]⁺ ℓ-hetᵈ
    {-# INLINE mk-quiver-onωᵈ #-}

module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom} (C : HQuiver-onω m Ob ℓ-hom) (open Quiver-onω C renaming (Het to Hom)) where
  -- base is homogeneous but display is heterogeneous
  SQuiver-onωᵈ : ∀ m′ {ℓ-obᵈ⁻} (Ob[_]⁻ : ob-sigᵈ Ob ℓ-obᵈ⁻) n′ {ℓ-obᵈ⁺} (Ob[_]⁺ : ob-sigᵈ Ob ℓ-obᵈ⁺)
                 (ℓ-homᵈ : ℓ-sig 4 (m , m , m′ , n′ , _)) → Typeω
  SQuiver-onωᵈ m′ Ob[_]⁻ n′ Ob[_]⁺ = Quiver-onωᵈ C m′ Ob[_]⁻ n′ Ob[_]⁺
  {-# NOINLINE SQuiver-onωᵈ #-}

  -- fully homogeneous
  HQuiver-onωᵈ : ∀ m′ {ℓ-obᵈ} (Ob[_] : ob-sigᵈ Ob ℓ-obᵈ) (ℓ-homᵈ : ℓ-sig 4 (m , m , m′ , m′ , _)) → Typeω
  HQuiver-onωᵈ m′ Ob[_] = SQuiver-onωᵈ m′ Ob[_] m′ Ob[_]
  {-# NOINLINE HQuiver-onωᵈ #-}


module _ {m ℓ-ob⁻} {Ob⁻ : ob-sig ℓ-ob⁻} {n ℓ-ob⁺} {Ob⁺ : ob-sig ℓ-ob⁺}
  {ℓ-het} (C : Quiver-onω m Ob⁻ n Ob⁺ ℓ-het) (open Quiver-onω C) where

  Fan⁻ : ∀{lbs} (b : Ob⁺ lbs) las → Type (ℓ-ob⁻ las ⊔ ℓ-het las lbs)
  Fan⁻ b las = Σₜ (Ob⁻ las) λ a → Het a b

  Fan⁺ : ∀{las} (a : Ob⁻ las) lbs → Type (ℓ-ob⁺ lbs ⊔ ℓ-het las lbs)
  Fan⁺ a lbs = Σₜ (Ob⁺ lbs) λ b → Het a b
