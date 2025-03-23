```agda

module Lib.Path.Tensor where

open import Prim.Base
open import Prim.Kan
open import Prim.Cartesian
open import Lib.Path.Base
open import Lib.Equiv.Base

canonical-path : ∀ {ℓ} (A : I → Type ℓ) → A i0 ≡ A i1
canonical-path A i = A i

canonical-pathp : ∀ {ℓ} (A : I → I → Type ℓ)
                → PathP (λ j → I → Type ℓ) (A i0) (A i1)
canonical-pathp A i j = A i j
