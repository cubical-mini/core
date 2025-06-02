{-# OPTIONS --safe #-}
module Foundations.Equiv.Base where

open import Prim.Data.Sigma
open import Prim.Data.Unit
open import Prim.Equiv
open import Prim.Type

open import Notation.Base
open import Notation.Displayed.Base
open import Notation.Displayed.Reflexivity
open import Notation.Displayed.Wide
open import Notation.Reflexivity

open import Foundations.Pi.Category

-- strict-contr-fibres : ∀{ℓa ℓb} {A : Type a} {B : Type b}
--                       {f : A → B} (g : B → A) (b : B)
--                     → Σ (fibre f (f (g b))) λ t →
--                     -- Σ[ t        ꞉ fibre f (f (g b)) ]
--                       Π[ (y′ , q) ꞉ fibre f       b   ]
--                       Path (fibre f (f (g b))) t (g (f y′) , ap (f ∘ g) q)
-- strict-contr-fibres     g b .fst           = g b , refl
-- strict-contr-fibres {f} g b .snd (a , p) i = g (p (~ i)) , λ j → f (g (p (~ i ∨ j)))

Equivsᵈ : Quiver-onᵈ Funs (λ {_} X → ⊤) _l⊔_
Equivsᵈ .Quiver-onᵈ.Hom[_] f _ _ = is-equiv f

-- open Fun-cat
-- instance
--   Equiv-Reflᵈ : Reflᵈ Funs Equivsᵈ {!!}
--   Equiv-Reflᵈ .reflᵈ = {!!}
