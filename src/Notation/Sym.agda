{-# OPTIONS --safe #-}
module Notation.Sym where

open import Foundations.Base

module _ {m ℓ-ob ℓ-hom} {Ob : ob-sig ℓ-ob}
  (C : HQuiver-onω m Ob ℓ-hom) (open Quiver-onω C renaming (Het to Hom))
  {ℓf : ℓ-sig 4 (m , m , 0 , 0 , _)}
  (F : ∀{lxs lys} (x : Ob lxs) (y : Ob lys) → HQuiver-onω 0 (λ _ → Hom x y) (ℓf lxs lys))
  where
  private module F {lxs} {lys} {x} {y} = Quiver-onω (F {lxs} {lys} x y) renaming (Het to Hom)

  record Sym : Typeω where
    no-eta-equality
    field
      sym : ∀{lxs lys} {x : Ob lxs} {y : Ob lys} → Hom x y → Hom y x
      sym-invol : ∀{lxs lys} {x : Ob lxs} {y : Ob lys}
                  {p : Hom x y} → F.Hom p (sym (sym p))

open Sym ⦃ ... ⦄ public
{-# DISPLAY Sym.sym _ p = sym p #-}
{-# DISPLAY Sym.sym-invol _ = sym-invol #-}
