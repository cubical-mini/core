{-# OPTIONS --safe #-}
module Foundations.Equiv.Base where

open import Prim.Data.Sigma
open import Prim.Data.Unit
open import Prim.Interval
open import Prim.Type

open import Notation.Base
open import Notation.Displayed.Base
open import Notation.Displayed.Reflexivity
open import Notation.Displayed.Wide
open import Notation.Displayed.Total
open import Notation.Reflexivity
open import Notation.Symmetry

open import Foundations.Path.Groupoid
open import Foundations.Pi.Category
open import Foundations.Singleton

open Path-gpd0

strict-contr-fibres : ∀{ℓa ℓb}{A : Type ℓa} {B : Type ℓb}
                      {f : A → B}
                      (g : B → A) (b : B)
                    → Total-ob (Pathsω (fibre f (f (g b))))
                        (λ t → (fb : fibre f b) → Path (fibre f (f (g b))) t (total-ob (g (f (fb .carrier))) (ap (f ∘ₜ g) (fb .structured)))) ℓa
strict-contr-fibres g b .carrier .carrier = g b
strict-contr-fibres g b .carrier .structured = refl
strict-contr-fibres g b .structured (total-ob a p) i .carrier = g (p i)
strict-contr-fibres {f} g b .structured (total-ob a p) i .structured j = f (g (p (i ∧ j)))

record is-equiv {ℓa ℓb} {A : Type ℓa} {B : Type ℓb} (f : A → B) : Type (ℓa l⊔ ℓb) where
  no-eta-equality
  field equiv-proof : (y : B) → is-contr (fibre f y)

open is-equiv public

Equivsᵈ : Quiver-onᵈ Funs (λ {_} X → ⊤) _l⊔_
Equivsᵈ .Quiver-onᵈ.Hom[_] f _ _ = is-equiv f

infix 10 _≃_
_≃_ : ∀{ℓa ℓb} (A : Type ℓa) (B : Type ℓb) → Type (ℓa l⊔ ℓb)
A ≃ B = Total-hom Funs Equivsᵈ {x = A} {y = B} tt tt
{-# DISPLAY Total-hom {_} {_} {_} Funs {_} {_} {_} Equivsᵈ {_} {_} {x} {y} _ _ = x ≃ y #-}

equiv-forward : ∀{ℓa ℓb} {A : Type ℓa} {B : Type ℓb} → A ≃ B → A → B
equiv-forward e = e .hom

equiv-proof-fast : ∀{ℓa ℓt} (T : Type ℓt) (A : Type ℓa) (w : T ≃ A) (a : A)
                 → ∀ ψ (f : Partial ψ (Σ T (λ z → equiv-forward w z ＝ a))) →  Σ T (λ z → equiv-forward w z ＝ a) [ ψ ↦ f ]
equiv-proof-fast T A w a ψ f = is-contr→extend cont ψ f where
  cont : is-contr (Σ T (λ z → equiv-forward w z ＝ a))
  cont .carrier .fst = w .preserves .equiv-proof a .carrier .carrier
  cont .carrier .snd = sym (w .preserves .equiv-proof a .carrier .structured)
  cont .structured (t , p) i .fst = w .preserves .equiv-proof a .structured (total-ob t (sym p)) i .carrier
  cont .structured (t , p) i .snd j = w .preserves .equiv-proof a .structured (total-ob t (sym p)) i .structured (~ j)

{-# BUILTIN EQUIV      _≃_           #-}
{-# BUILTIN EQUIVFUN   equiv-forward #-}
{-# BUILTIN EQUIVPROOF equiv-proof-fast #-}

open Fun-cat

Equivs : Quiver-on (λ ℓ → Type ℓ) _
Equivs = Wide Equivsᵈ

instance
  Equiv-Reflᵈ : Reflᵈω Funs Equivsᵈ
  Equiv-Reflᵈ .reflᵈ .equiv-proof = strict-contr-fibres refl

  -- Equiv-Sym : Symmetryω Equivs
  -- Equiv-Sym .sym e .hom t = e .preserves .equiv-proof t .carrier .carrier
  -- Equiv-Sym .sym e .preserves = {!!} -- TODO need quasi-inverse→is-equiv
