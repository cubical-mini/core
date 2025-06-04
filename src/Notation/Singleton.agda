{-# OPTIONS --safe #-}
module Notation.Singleton where

open import Prim.Type

open import Notation.Base
open import Notation.Displayed.Base
open import Notation.Displayed.Total
open import Notation.Reflexivity
open import Notation.Singleton.Base public

module _ {ℓo ℓh : Level} {Ob : Type ℓo}
  (C : Small-quiver-on Ob ℓh) (open Small-quiver-on C)
  ⦃ _ : Refl (Enlarge C) ℓo ⦄
  (c : Ob)
  (D : Small-quiver-onᵈ C (Hom c) ℓh) (open Small-quiver-onᵈ D)
  (push : (w : Singleton C c) → Hom[ w .structured ] refl (w .structured)) where
  -- TODO push looks like something from identity systems, can you factor it away?

  singleton-contractible : Contractible (Singletons C c D)
  singleton-contractible .carrier .carrier = c
  singleton-contractible .carrier .structured = refl
  singleton-contractible .structured w .hom = w .structured
  singleton-contractible .structured w .preserves = push w
