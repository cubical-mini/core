{-# OPTIONS --safe #-}
module Notation.Singleton.Base where

open import Prim.Type

open import Notation.Base
open import Notation.Displayed.Base
open import Notation.Displayed.Total

module _ {ℓo ℓh : Level} {Ob : Type ℓo}
  (C : Small-quiver-on Ob ℓh) (open Small-quiver-on C) where

  Central : Ob → Type (ℓo l⊔ ℓh)
  Central c = (x : Ob) → Hom c x

  Contractible : Type (ℓo l⊔ ℓh)
  Contractible = Total-ob (Enlarge C) Central ℓo

module _ {ℓo ℓh ℓa : Level} {Ob : Type ℓo}
  (B : Small-quiver-on Ob ℓh) (open Small-quiver-on B)
  {A : Type ℓa} (f : A → Ob) (y : Ob) where

  Fibre : Type (ℓh l⊔ ℓa)
  Fibre = Total-ob (Enlarge (Codisc A)) (λ a → Hom y (f a)) ℓo

module _ {ℓo ℓh : Level} {Ob : Type ℓo}
  (C : Small-quiver-on Ob ℓh) (open Small-quiver-on C)
  (c : Ob) where

  Singleton : Type (ℓo l⊔ ℓh)
  Singleton = Fibre C (λ x → x) c

  module _ (D : Small-quiver-onᵈ C (Hom c) ℓh) where
    Singleton-Hom : (u v : Singleton) → Type ℓh
    Singleton-Hom u v = Total-hom (Enlarge C) (Enlargeᵈ D) {ℓx = lzero} {ℓy = lzero} (u .structured) (v .structured)

    Singletons : Small-quiver-on Singleton ℓh
    Singletons .Small-quiver-on.Hom = Singleton-Hom
