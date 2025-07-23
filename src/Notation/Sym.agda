{-# OPTIONS --safe #-}
module Notation.Sym where

open import Foundations.Quiver.Base

module _ {m ℓ-ob ℓ-hom} {Ob : ob-sig ℓ-ob}
  (C : HQuiver-onω m Ob ℓ-hom) (open Quiver-onω C renaming (Het to Hom)) where

  record Sym : Typeω where
    no-eta-equality
    field sym : ∀{lxs lys} {x : Ob lxs} {y : Ob lys} → Hom x y → Hom y x

open Sym ⦃ ... ⦄ public
{-# DISPLAY Sym.sym _ p = sym p #-}


module _ {m ℓ-ob ℓ-hom} {Ob : ob-sig ℓ-ob}
  {C : HQuiver-onω m Ob ℓ-hom} (open Quiver-onω C renaming (Het to Hom))
  {m′ ℓ-obᵈ ℓ-homᵈ} {Ob[_] : ob-sigᵈ Ob ℓ-obᵈ}
  (D : HQuiver-onωᵈ C m′ Ob[_] ℓ-homᵈ) (open Quiver-onωᵈ D renaming (Het[_] to Hom[_]))
  ⦃ _ : Sym C ⦄ where

  record Symᵈ : Typeω where
    no-eta-equality
    field symᵈ : ∀{lxs lys lxsᵈ lysᵈ}
                 {x : Ob lxs} {y : Ob lys} {f : Hom x y}
                 {x′ : Ob[ x ] lxsᵈ} {y′ : Ob[ y ] lysᵈ}
               → Hom[ f ] x′ y′ → Hom[ sym f ] y′ x′

open Symᵈ ⦃ ... ⦄ public
{-# DISPLAY Symᵈ.symᵈ _ p = symᵈ p #-}
