{-# OPTIONS --safe #-}
module Notation.Base where

open import Prim.Data.Nat
open import Prim.Data.Sigma
open import Prim.Data.Unit
open import Prim.Type

-- vector of levels
Levels : ℕ → Type
Levels zero = ⊤
Levels (suc n) = Σ Level λ _ →  Levels n

-- unary level adjustment
ℓ-sig : ℕ → Type
ℓ-sig 0       = Level
ℓ-sig (suc n) = Level → ℓ-sig n

-- binary level adjustment
ℓ-sig² : ℕ → Type
ℓ-sig² 0       = Level
ℓ-sig² (suc n) = Level → Level → ℓ-sig² n


-- large object signature
ob-sigω : {n : ℕ} (ℓ-obω : ℓ-sig n) → Typeω
ob-sigω {0}     ℓo    = Liftω (Type ℓo)
ob-sigω {suc n} ℓ-obω = (ℓ : Level) → ob-sigω (ℓ-obω ℓ)

-- large arrow signature
hom-sigω : {n : ℕ} (ℓ-obω⁻ ℓ-obω⁺ : ℓ-sig n) (ℓ-homω : ℓ-sig² n)
           (Ob⁻ : ob-sigω ℓ-obω⁻) (Ob⁺ : ob-sigω ℓ-obω⁺) → Typeω
hom-sigω {0} ℓo⁻ ℓo⁺ ℓh (liftω Ob⁻) (liftω Ob⁺) =
  Liftω (Ob⁻ → Ob⁺ → Type ℓh)
hom-sigω {suc n} ℓ-obω⁻ ℓ-obω⁺ ℓ-homω Ob⁻ Ob⁺ =
  {ℓx ℓy : Level} → hom-sigω (ℓ-obω⁻ ℓx) (ℓ-obω⁺ ℓy) (ℓ-homω ℓx ℓy) (Ob⁻ ℓx) (Ob⁺ ℓy)

-- saturated application of object level signature
ℓ-ob : ∀{n} (ℓ-obω : ℓ-sig n) → Levels n → Level
ℓ-ob {0}     ℓo    _        = ℓo
ℓ-ob {suc n} ℓ-obω (l , ls) = ℓ-ob {n} (ℓ-obω l) ls

-- saturated application of arrow level signature
ℓ-hom : ∀{n} (ℓ-obω⁻ ℓ-obω⁺ : ℓ-sig n) (ℓ-homω : ℓ-sig² n) (lxs lys : Levels n) → Level
ℓ-hom {0} ℓo⁻ ℓo⁺ ℓh _ _ = ℓh
ℓ-hom {suc n} ℓ-obω⁻ ℓ-obω⁺ ℓ-homω (lx , lxs) (ly , lys) = ℓ-hom (ℓ-obω⁻ lx) (ℓ-obω⁺ ly) (ℓ-homω lx ly) lxs lys

private
  -- saturated application of object signature
  Ob′ : (n : ℕ) (ℓ-obω : ℓ-sig n) (Obω : ob-sigω ℓ-obω)
        (ls : Levels n) → Type (ℓ-ob ℓ-obω ls)
  Ob′ 0 _ (liftω Ob) _ = Ob
  Ob′ (suc n) ℓ-obω Obω (l , ls) = Ob′ n (ℓ-obω l) (Obω l) ls
  {-# INLINE Ob′ #-}

  -- saturated application of arrow signature
  Hom′ : (n : ℕ) (ℓ-obω⁻ ℓ-obω⁺ : ℓ-sig n) (ℓ-homω : ℓ-sig² n) (Obω⁻ : ob-sigω ℓ-obω⁻) (Obω⁺ : ob-sigω ℓ-obω⁺)
         (Homω : hom-sigω ℓ-obω⁻ ℓ-obω⁺ ℓ-homω Obω⁻ Obω⁺)
         (lxs lys : Levels n) (x : Ob′ n ℓ-obω⁻ Obω⁻ lxs) (y : Ob′ n ℓ-obω⁺ Obω⁺ lys)
       → Type (ℓ-hom ℓ-obω⁻ ℓ-obω⁺ ℓ-homω lxs lys)
  Hom′ 0 _ _ ℓh (liftω Ob⁻) (liftω Ob⁺) (liftω Hom) _ _ x y = Hom x y
  Hom′ (suc n) ℓ-obω⁻ ℓ-obω⁺ ℓ-homω Obω⁻ Obω⁺ Homω (lx , lxs) (ly , lys) =
    Hom′ n (ℓ-obω⁻ lx) (ℓ-obω⁺ ly) (ℓ-homω lx ly) (Obω⁻ lx) (Obω⁺ ly) Homω lxs lys
  {-# INLINE Hom′ #-}

-- quiver of arbitrary size
record Quiverω (n : ℕ) (ℓ-obω : ℓ-sig n) (ℓ-homω : ℓ-sig² n) : Typeω where
  constructor mk-quiverω
  no-eta-equality
  field
    Obω  : ob-sigω ℓ-obω
    Homω : hom-sigω ℓ-obω ℓ-obω ℓ-homω Obω Obω

  Ob : (ls : Levels n) → Type (ℓ-ob ℓ-obω ls)
  Ob = Ob′ n ℓ-obω Obω

  Hom : {lxs lys : Levels n} → Ob lxs → Ob lys → Type (ℓ-hom ℓ-obω ℓ-obω ℓ-homω lxs lys)
  Hom {lxs} {lys} = Hom′ n ℓ-obω ℓ-obω ℓ-homω Obω Obω Homω lxs lys
{-# INLINE mk-quiverω #-}


-- large displayed object signature
ob-sigωᵈ : {n : ℕ} (ℓ-obω : ℓ-sig n) (Obω : ob-sigω ℓ-obω)
         → {m : ℕ} (ℓ-obωᵈ : ℓ-sig (n + m)) → Typeω
ob-sigωᵈ {0} ℓo (liftω Ob) {m} ℓ-obωᵈ = Ob → (ls : Levels m) → Type (ℓ-ob ℓ-obωᵈ ls)
ob-sigωᵈ {suc n} ℓ-obω Obω ℓ-obωᵈ = {ℓ : Level} → ob-sigωᵈ {n = n} (ℓ-obω ℓ) (Obω ℓ) (ℓ-obωᵈ ℓ)

-- large displayed arrow signature
hom-sigωᵈ : {n : ℕ} (ℓ-obω⁻ ℓ-obω⁺ : ℓ-sig n) (Obω⁻ : ob-sigω ℓ-obω⁻) (Obω⁺ : ob-sigω ℓ-obω⁺)
            (ℓ-homω : ℓ-sig² n) (Homω : hom-sigω ℓ-obω⁻ ℓ-obω⁺ ℓ-homω Obω⁻ Obω⁺)
          → {m : ℕ} (ℓ-obωᵈ⁻ ℓ-obωᵈ⁺ : ℓ-sig (n + m))
            (Obω[_]⁻ : ob-sigωᵈ ℓ-obω⁻ Obω⁻ ℓ-obωᵈ⁻) (Obω[_]⁺ : ob-sigωᵈ ℓ-obω⁺ Obω⁺ ℓ-obωᵈ⁺)
            (ℓ-homωᵈ : ℓ-sig² (n + m)) → Typeω
hom-sigωᵈ {0} ℓo⁻ ℓo⁺ (liftω Ob⁻) (liftω Ob⁺) ℓ-homω (liftω Hom) {m} ℓ-obωᵈ⁻ ℓ-obωᵈ⁺ Obω[_]⁻ Obω[_]⁺ ℓ-homωᵈ =
  {x : Ob⁻} {y : Ob⁺} → Hom x y → {lxs lys : Levels m} → Obω[ x ]⁻ lxs → Obω[ y ]⁺ lys → Type (ℓ-hom ℓ-obωᵈ⁻ ℓ-obωᵈ⁺ ℓ-homωᵈ lxs lys)
hom-sigωᵈ {suc n} ℓ-obω⁻ ℓ-obω⁺ Obω⁻ Obω⁺ ℓ-homω Homω ℓ-obωᵈ⁻ ℓ-obωᵈ⁺ Obω[_]⁻ Obω[_]⁺ ℓ-homωᵈ =
  {ℓx ℓy : Level} → hom-sigωᵈ {n} (ℓ-obω⁻ ℓx) (ℓ-obω⁺ ℓy) (Obω⁻ ℓx) (Obω⁺ ℓy) (ℓ-homω ℓx ℓy)  (Homω {ℓx} {ℓy}) (ℓ-obωᵈ⁻ ℓx) (ℓ-obωᵈ⁺ ℓy) Obω[_]⁻ Obω[_]⁺ (ℓ-homωᵈ ℓx ℓy)

-- saturated application of displayed object level signature
ℓ-obᵈ : ∀{n} (ℓ-obω : ℓ-sig n) {m} (ℓ-obωᵈ : ℓ-sig (n + m)) → Levels n → Levels m → Level
ℓ-obᵈ {0} ℓo ℓ-obωᵈ ls lsᵈ = ℓ-ob ℓ-obωᵈ lsᵈ
ℓ-obᵈ {suc n} ℓ-obω ℓ-obωᵈ (l , ls) lsᵈ = ℓ-obᵈ (ℓ-obω l) (ℓ-obωᵈ l) ls lsᵈ

-- saturated application of displayed arrow level signature
ℓ-homᵈ : ∀{n} (ℓ-obω⁻ ℓ-obω⁺ : ℓ-sig n) (ℓ-homω : ℓ-sig² n) {m} (ℓ-obωᵈ⁻ ℓ-obωᵈ⁺ : ℓ-sig (n + m)) (ℓ-homωᵈ : ℓ-sig² (n + m)) (lxs lys : Levels n) (lxsᵈ lysᵈ : Levels m) → Level
ℓ-homᵈ {0} ℓo⁻ ℓo⁺ ℓh ℓ-obωᵈ⁻ ℓ-obωᵈ⁺ ℓ-homωᵈ lxs lys lxsᵈ lysᵈ = ℓ-hom ℓ-obωᵈ⁻ ℓ-obωᵈ⁺ ℓ-homωᵈ lxsᵈ lysᵈ
ℓ-homᵈ {suc n} ℓ-obω⁻ ℓ-obω⁺ ℓ-homω ℓ-obωᵈ⁻ ℓ-obωᵈ⁺ ℓ-homωᵈ (lx , lxs) (ly , lys) lxsᵈ lysᵈ =
  ℓ-homᵈ (ℓ-obω⁻ lx) (ℓ-obω⁺ ly) (ℓ-homω lx ly) (ℓ-obωᵈ⁻ lx) (ℓ-obωᵈ⁺ lx) (ℓ-homωᵈ lx ly) lxs lys lxsᵈ lysᵈ

private
  -- saturated application of displayed object signature
  Ob[_]′ : (n : ℕ) (ℓ-obω : ℓ-sig n) (Obω : ob-sigω ℓ-obω)
           (m : ℕ) (ℓ-obωᵈ : ℓ-sig (n + m)) (Obω[_] : ob-sigωᵈ ℓ-obω Obω ℓ-obωᵈ)
           (ls : Levels n)
           (x : Ob′ n ℓ-obω Obω ls)
           (lsᵈ : Levels m) → Type (ℓ-obᵈ ℓ-obω ℓ-obωᵈ ls lsᵈ)
  Ob[_]′ 0 ℓo (liftω Ob) 0 ℓoᵈ Ob[_] _ x _ = Ob[ x ] tt
  Ob[_]′ 0 ℓo Obω (suc m) ℓ-obωᵈ Obω[_] _ x (lᵈ , lsᵈ) =
    Ob[_]′ 0 ℓo Obω m (ℓ-obωᵈ lᵈ) (λ y ls′ → Obω[ y ] (lᵈ , ls′)) _ x lsᵈ
  Ob[_]′ (suc n) ℓ-obω Obω m ℓ-obωᵈ Obω[_] (l , ls) x lsᵈ =
    Ob[_]′ n (ℓ-obω l) (Obω l) m (ℓ-obωᵈ l) Obω[_] ls x lsᵈ
  {-# INLINE Ob[_]′ #-}

  -- saturated application of displayed arrow signature
  Hom[_]′ : (n : ℕ) (ℓ-obω⁻ ℓ-obω⁺ : ℓ-sig n) (ℓ-homω : ℓ-sig² n) (Obω⁻ : ob-sigω ℓ-obω⁻) (Obω⁺ : ob-sigω ℓ-obω⁺)
            (Homω : hom-sigω ℓ-obω⁻ ℓ-obω⁺ ℓ-homω Obω⁻ Obω⁺)
            (lxs lys : Levels n)
            (m : ℕ) (ℓ-obωᵈ⁻ : ℓ-sig (n + m)) (ℓ-obωᵈ⁺ : ℓ-sig (n + m))
            (Obω[_]⁻ : ob-sigωᵈ ℓ-obω⁻ Obω⁻ ℓ-obωᵈ⁻) (Obω[_]⁺ : ob-sigωᵈ ℓ-obω⁺ Obω⁺ ℓ-obωᵈ⁺)
            (ℓ-homωᵈ : ℓ-sig² (n + m))
            (Homω[_] : hom-sigωᵈ ℓ-obω⁻ ℓ-obω⁺ Obω⁻ Obω⁺ ℓ-homω Homω ℓ-obωᵈ⁻ ℓ-obωᵈ⁺ Obω[_]⁻ Obω[_]⁺ ℓ-homωᵈ)
            (lxsᵈ lysᵈ : Levels m)
            (x : Ob′ n ℓ-obω⁻ Obω⁻ lxs) (y : Ob′ n ℓ-obω⁺ Obω⁺ lys) (f : Hom′ n ℓ-obω⁻ ℓ-obω⁺ ℓ-homω Obω⁻ Obω⁺ Homω lxs lys x y)
            (x′ : Ob[_]′ n ℓ-obω⁻ Obω⁻ m ℓ-obωᵈ⁻ Obω[_]⁻ lxs x lxsᵈ) (y′ : Ob[_]′ n ℓ-obω⁺ Obω⁺ m ℓ-obωᵈ⁺ Obω[_]⁺ lys y lysᵈ)
          → Type (ℓ-homᵈ ℓ-obω⁻ ℓ-obω⁺ ℓ-homω ℓ-obωᵈ⁻ ℓ-obωᵈ⁺ ℓ-homωᵈ lxs lys lxsᵈ lysᵈ)
  Hom[_]′ 0 ℓo⁻ ℓo⁺ ℓh (liftω Ob⁻) (liftω Ob⁺) (liftω Hom) _ _ 0 ℓoᵈ⁻ ℓoᵈ⁺ Ob[_]⁻ Ob[_]⁺ ℓhᵈ Hom[_] lxsᵈ lysᵈ x y f = Hom[ f ]
  Hom[_]′ 0 ℓo⁻ ℓo⁺ ℓh Obω⁻ Obω⁺ Homω _ _ (suc m) ℓ-obωᵈ⁻ ℓ-obωᵈ⁺ Obω[_]⁻ Obω[_]⁺ ℓ-homωᵈ Homω[_] (lxᵈ , lxsᵈ) (lyᵈ , lysᵈ) =
    Hom[_]′ 0 ℓo⁻ ℓo⁺ ℓh Obω⁻ Obω⁺ Homω _ _ m (ℓ-obωᵈ⁻ lxᵈ) (ℓ-obωᵈ⁺ lyᵈ) (λ t ls′ → Obω[ t ]⁻ (lxᵈ , ls′)) (λ t ls′ → Obω[ t ]⁺ (lyᵈ , ls′))
      (ℓ-homωᵈ lxᵈ lyᵈ) (λ g → Homω[ g ]) lxsᵈ lysᵈ
  Hom[_]′ (suc n) ℓ-obω⁻ ℓ-obω⁺ ℓ-homω Obω⁻ Obω⁺ Homω (lx , lxs) (ly , lys) m ℓ-obωᵈ⁻ ℓ-obωᵈ⁺ Obω[_]⁻ Obω[_]⁺ ℓ-homωᵈ Homω[_] =
    Hom[_]′ n (ℓ-obω⁻ lx) (ℓ-obω⁺ ly) (ℓ-homω lx ly) (Obω⁻ lx) (Obω⁺ ly) Homω lxs lys m (ℓ-obωᵈ⁻ lx) (ℓ-obωᵈ⁺ ly) Obω[_]⁻ Obω[_]⁺ (ℓ-homωᵈ lx ly) Homω[_]

-- displayed quiver of arbitrary size
module _ {n : ℕ} {ℓ-obω : ℓ-sig n} {ℓ-homω : ℓ-sig² n} (C : Quiverω n ℓ-obω ℓ-homω) (open Quiverω C) where
  record Quiverωᵈ (m : ℕ) (ℓ-obωᵈ : ℓ-sig (n + m)) (ℓ-homωᵈ : ℓ-sig² (n + m)) : Typeω where
    constructor mk-quiverωᵈ
    no-eta-equality
    field
      Obω[_]  : ob-sigωᵈ ℓ-obω Obω ℓ-obωᵈ
      Homω[_] : hom-sigωᵈ ℓ-obω ℓ-obω Obω Obω ℓ-homω Homω ℓ-obωᵈ ℓ-obωᵈ Obω[_] Obω[_] ℓ-homωᵈ

    Ob[_] : {ls : Levels n} (x : Ob ls) (lsᵈ : Levels m) → Type (ℓ-obᵈ ℓ-obω ℓ-obωᵈ ls lsᵈ)
    Ob[_] {ls} = Ob[_]′ n ℓ-obω Obω m ℓ-obωᵈ Obω[_] ls

    Hom[_] : {lxs lys : Levels n} {x : Ob lxs} {y : Ob lys} (f : Hom x y)
           → {lxsᵈ lysᵈ : Levels m} (x′ : Ob[ x ] lxsᵈ) (y′ : Ob[ y ] lysᵈ)
           → Type (ℓ-homᵈ ℓ-obω ℓ-obω ℓ-homω ℓ-obωᵈ ℓ-obωᵈ ℓ-homωᵈ lxs lys lxsᵈ lysᵈ)
    Hom[_] {lxs} {lys} {x} {y} f {lxsᵈ} {lysᵈ} =
      Hom[_]′ n ℓ-obω ℓ-obω ℓ-homω Obω Obω Homω lxs lys m ℓ-obωᵈ ℓ-obωᵈ Obω[_] Obω[_] ℓ-homωᵈ Homω[_] lxsᵈ lysᵈ x y f
  {-# INLINE mk-quiverωᵈ #-}
