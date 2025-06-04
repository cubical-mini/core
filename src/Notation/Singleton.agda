{-# OPTIONS --safe #-}
module Notation.Singleton where

open import Prim.Type

open import Notation.Base
open import Notation.Displayed.Base
open import Notation.Displayed.Total
open import Notation.Reflexivity

module _ {ℓo ℓh : Level} {Ob : Type ℓo}
  (C : Small-quiver-on Ob ℓh) (open Small-quiver-on C) where

  Central : Ob → Type (ℓo l⊔ ℓh)
  Central c = (x : Ob) → Hom c x

  Contractible : Type (ℓo l⊔ ℓh)
  Contractible = Total-ob (Enlarge C) Central lzero

module _ {ℓo ℓh ℓa : Level} {Ob : Type ℓo}
  (C : Small-quiver-on Ob ℓh) (open Small-quiver-on C)
  {A : Type ℓa} (f : A → Ob) (c : A) where

  Fibred : Type (ℓo l⊔ ℓh)
  Fibred = Total-ob (Enlarge C) (Hom (f c)) lzero

module _ {ℓo ℓh : Level} {Ob : Type ℓo}
  (C : Small-quiver-on Ob ℓh) (open Small-quiver-on C)
  (c : Ob) where

  Singleton : Type (ℓo l⊔ ℓh)
  Singleton = Fibred C (λ x → x) c

  module _ (D : Small-quiver-onᵈ C (Hom c) lzero) where
    Singleton-Hom : (u v : Singleton) → Type ℓh
    Singleton-Hom u v = Total-hom (Enlarge C) (Enlargeᵈ D) {ℓx = lzero} {ℓy = lzero} (u .structured) (v .structured)

    Singletons : Small-quiver-on Singleton ℓh
    Singletons .Small-quiver-on.Hom = Singleton-Hom

-- TODO move
module _ {ℓo ℓh : Level} {Ob : Type ℓo}
  (C : Small-quiver-on Ob ℓh) (open Small-quiver-on C)
  ⦃ _ : Refl (Enlarge C) lzero ⦄
  (c : Ob)
  (D : Small-quiver-onᵈ C (Hom c) lzero) (open Small-quiver-onᵈ D)
  (push : (w : Singleton C c) → Hom[ w .structured ] refl (w .structured)) where

  inhabited : Singleton C c
  inhabited .carrier = c
  inhabited .structured = refl

  kek : Contractible (Singletons C c D)
  kek .carrier = inhabited
  kek .structured w .hom = w .structured
  kek .structured w .preserves = push w
