{-# OPTIONS --safe --erased-cubical #-}
module Notation.Refl.Base where

open import Prim.Data.Nat
open import Prim.Type

open import Notation.Base

open import Prim.Data.Sigma
open import Prim.Data.Unit
Levels : ℕ → Type
Levels zero = ⊤
Levels (suc n) = Σ Level λ _ →  Levels n

-- lmap : ∀{n} → (Level → Level) → Levels n → Levels n
-- lmap {(zero)} _ _ = tt
-- lmap {suc n}  f (l , ls) = f l , lmap f ls

squash : ∀{n} {ℓ-ob : ℓ-sig n} {ℓ-hom : ℓ-sig² n} → Levels n → Level
squash {(zero)} {ℓ-ob = ℓo} {ℓ-hom = ℓh} ls = ℓo ⊔ ℓh
squash {suc n} {ℓ-ob} {ℓ-hom} (l , ls) = squash {n} {ℓ-ob = ℓ-ob l} {ℓ-hom = ℓ-hom l l} ls

-- 0 → ℓ-ob ⊔ ℓ-hom
-- 1 → ℓ-ob ℓ ⊔ ℓ-hom ℓ ℓ

-- refl-sig : {ℓ-num : ℕ} (ℓ-ob : ℓ-sig ℓ-num) (ℓ-hom : ℓ-sig² ℓ-num)
--          → (Ob : ob-sig ℓ-ob) (Hom : hom-sig ℓ-ob ℓ-ob ℓ-hom Ob Ob)
--          → Typeω
-- refl-sig {0}     ℓo   ℓh    (liftω Ob) (liftω Hom) = Liftω ({x : Ob} → Hom x x)
-- refl-sig {suc n} ℓ-ob ℓ-hom Ob         Hom         = ∀{ℓ} → refl-sig {n} (ℓ-ob ℓ) (ℓ-hom ℓ ℓ) (Ob ℓ) Hom

refl-sig : {ℓ-num : ℕ} {ℓ-ob : ℓ-sig ℓ-num} {ℓ-hom : ℓ-sig² ℓ-num}
    → {Ob : ob-sig ℓ-ob} {Hom : hom-sig ℓ-ob ℓ-ob ℓ-hom Ob Ob}
    → (ls : Levels ℓ-num)
    → Type (squash {ℓ-ob = ℓ-ob} {ℓ-hom = ℓ-hom} ls)
refl-sig {0}     {Ob = liftω Ob} {Hom = liftω Hom} _        = {x : Ob} → Hom x x
refl-sig {suc n} {ℓ-hom} {Ob}            {Hom}             (l , ls) = refl-sig {n} {ℓ-hom = ℓ-hom l l} {Ob = Ob l} {Hom = Hom} ls

module _ {ℓ-num : ℕ} {ℓ-ob : ℓ-sig ℓ-num} {ℓ-hom : ℓ-sig² ℓ-num}
  (C : Quiverω ℓ-num ℓ-ob ℓ-hom) (open Quiverω C) where

  record Refl (ls : Levels ℓ-num) : Typeω where
    no-eta-equality
    field reflω : refl-sig {ℓ-num} {ℓ-ob} {ℓ-hom} {Ob} {Hom} ls

  Reflω : Typeω
  Reflω = ∀ {ls} → Refl ls

open Refl ⦃ ... ⦄ public
{-# DISPLAY Refl.reflω _ = reflω #-}

open import Prim.Kan

Funs : Quiverω 1 lsuc _⊔_
Funs .Quiverω.Ob ℓ .lowerω = Type ℓ
Funs .Quiverω.Hom .lowerω A B = A → B

Paths : ∀{ℓ} (A : Type ℓ) → Quiverω 0 ℓ ℓ
Paths A .Quiverω.Ob .lowerω = A
Paths A .Quiverω.Hom .lowerω = _＝_

instance
  Fun-Refl : Reflω Funs
  Fun-Refl .reflω x = x

  Path-Refl : ∀ {ℓ} {A : Type ℓ} → Reflω (Paths A)
  Path-Refl .reflω {x} _ = x

test : ∀{ℓ} {A : Type ℓ} → A → A
test = reflω {1}

zooz : ∀ {n : ℕ} → n ＝ n
zooz = reflω {0}

test2 : (p : 3 ＝ 3) (q : p ＝ reflω {0}) → ℕ
test2 = {!!}

module Bek {ℓ-ob : ℓ-sig 1} {ℓ-hom : ℓ-sig² 1}
  (C : Quiverω 1 ℓ-ob ℓ-hom) (open Quiverω C) ⦃ _ : Reflω C ⦄ where

  aboba : ∀ {ℓx ℓy} → (x : Ob ℓx .lowerω) (y : Ob ℓy .lowerω) (f : Hom .lowerω x x) (p : f ＝ reflω {1}) → {!!}
  aboba = {!!}

-- module _ {ℓ-ob ℓ-obᵈ : ℓ-sig¹} {ℓ-hom ℓ-homᵈ : ℓ-sig³}
--   {C : Quiverω ℓ-ob ℓ-hom} (open Quiverω C) ⦃ _ : Reflω C ⦄
--   (D : Quiverωᵈ C ℓ-obᵈ ℓ-homᵈ) (open Quiverωᵈ D) where

--   record Reflᵈ ℓo ℓh : Typeω where
--     no-eta-equality
--     field reflᵈ : {x : Ob ℓo} {x′ : Ob[ x ]} → Hom[_] {ℓ = ℓh} refl x′ x′

--   Reflωᵈ = ∀ {ℓo ℓh} → Reflᵈ ℓo ℓh

-- open Reflᵈ ⦃ ... ⦄ public
-- {-# DISPLAY Reflᵈ.reflᵈ _ = reflᵈ #-}


-- -- displayed quiver over a reflexive quiver begets a family of _small_ quivers
-- module _ {ℓ-ob ℓ-obᵈ : ℓ-sig¹} {ℓ-hom ℓ-homᵈ : ℓ-sig³}
--   {C : Quiverω ℓ-ob ℓ-hom} (open Quiverω C) ⦃ _ : Reflω C ⦄
--   (D : Quiverωᵈ C ℓ-obᵈ ℓ-homᵈ) (open Quiverωᵈ D) where
--   module _ {ℓ} (t : Ob ℓ) where
--     _$ωᵈ_ : Quiverω (λ _ → ℓ-obᵈ ℓ) (λ _ _ _ → ℓ-homᵈ ℓ ℓ ℓ)
--     _$ωᵈ_ .Ob  _ = Ob[ t ]
--     _$ωᵈ_ .Hom _ = Hom[_] {ℓ = ℓ} refl
