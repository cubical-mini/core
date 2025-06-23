{-# OPTIONS --safe #-}
module Foundations.Quiver.Wide.Base where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Total.Base public

module _ {n ℓ-ob ℓ-hom} (C : Quiverω n ℓ-ob ℓ-hom) (open Quiverω C)
  {ℓ-homᵈ} (D : Quiver-onωᵈ Ob Hom 0 (λ _ _ → ⊤) ℓ-homᵈ) where

  Wideᵈ : Quiverωᵈ C 0 _ ℓ-homᵈ
  Wideᵈ .Quiverωᵈ.Ob[_] _ _ = ⊤
  Wideᵈ .has-quiver-onωᵈ = D

  Wide : Quiverω n _ _
  Wide .Quiverω.Ob = Ob
  Wide .has-quiver-onω .Quiver-onω.Hom x y =
    ΣHom (C .has-quiver-onω) D {x = x} {y = y} _ _
