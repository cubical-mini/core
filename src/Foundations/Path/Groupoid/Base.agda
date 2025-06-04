{-# OPTIONS --safe #-}
module Foundations.Path.Groupoid.Base where

open import Prim.Kan
open import Prim.Type

open import Notation.Base

Paths : ∀{ℓ} (A : Type ℓ) → Small-quiver-on A ℓ
Paths A .Small-quiver-on.Hom = Path A

Pathsω : ∀{ℓ} (A : Type ℓ) → Quiver-on (λ _ → A) (λ _ _ → ℓ)
Pathsω A = Enlarge (Paths A)

-- TODO refactor
Strict : ∀{ℓo ℓh} {Ob : Type ℓo} {C : Small-quiver-on Ob ℓh}
       → Small-2-quiver-on C
Strict {C} .Small-2-quiver-on.Quiver₂ x y = Paths (Hom x y) where open Small-quiver-on C

Strictω : {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig} {C : Quiver-on Ob ℓ-hom}
        → 2-Quiver-on C
Strictω {C} .2-Quiver-on.Quiver₂ x y = Pathsω (Hom x y) where open Quiver-on C

2-Strict : {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig} {C : Quiver-on Ob ℓ-hom} {C₂ : 2-Quiver-on C}
         → 3-Quiver-on C C₂
2-Strict {C₂} .3-Quiver-on.Quiver₃ f g = Pathsω (2-Hom f g) where open 2-Quiver-on C₂
