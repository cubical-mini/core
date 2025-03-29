Path fillers and up-to-homotopy computation rules

```agda

module Lib.Path.Coherence where

open import Prim.Base
open import Prim.Pi
open import Prim.Data.Sigma
open import Prim.Cartesian

open import Lib.Path.Base
open import Lib.HLevel.Base

hcomp-unique : ∀ {ℓ} {A : Type ℓ} (φ : I)
               (u : ∀ i → Partial (φ ∨ ~ i) A)
             → (h₂ : ∀ i → A [ _ ↦ (λ { (i = i0) → u i0 1=1
                                      ; (φ = i1) → u i  1=1 }) ])
             → hcomp φ u ＝ outS (h₂ i1)
hcomp-unique φ u h₂ i =
  hcomp (φ ∨ i) λ where
    k (k = i0) → u i0 1=1
    k (i = i1) → outS (h₂ k)
    k (φ = i1) → u k 1=1

canonical-path : ∀ {ℓ} (A : I → Type ℓ) → A i0 ＝ A i1
canonical-path A i = A i

canonical-filler : ∀ {ℓ} (A : I → I → Type ℓ) → PathP (λ j → I → Type ℓ) (A i0) (A i1)
canonical-filler A i j = A i j

transport-refl : ∀ {ℓ} {A : Type ℓ} (x : A) → transport refl x ＝ x
transport-refl {A = A} x i = transp (λ i → A) i x

transport-filler : ∀ {ℓ} {A B : Type ℓ} (p : A ＝ B) (x : A)
                 → PathP (λ i → p i) x (transport p x)
transport-filler {A = A} p x i = transp (λ j → p (i ∧ j)) (~ i) x

J-path : ∀ {ℓ ℓ'} {A : Type ℓ} {x : A}
       → (P : (y : A) → x ＝ y → Type ℓ')
       → (r : P x refl) → J P r refl ＝ r
J-path {x = x} P r i = transport-filler (λ i → P x (erefl x)) r (~ i)

module coh {u v w} {A : Type u} {B : A → Type v} (C : {x : A} → B x → Type w) (a : A)
  where
  mor : (b : A) → Type u
  mor b = a ＝ b
  dop : {u : A} {b : B a} (f : Π B) → Type {!!}
  dop {u} {b} f = (u : {x : A} → B a) → Σ a ∶ {!a ＝ !} , {!!}
module _ {ℓ} {A : Type ℓ} {w x y z : A} (p : w ＝ x) (q : x ＝ y) (r : y ＝ z) where
  Filler : Type ℓ
  Filler = Σ s ∶ (w ＝ z) , Square (sym p) q r s

  Filler-unique : (α β : Filler) → α ＝ β
  Filler-unique (α , αf) (β , βf) =
    λ i → (sq i , λ j k → cu i j k)
    where
      -- the same way that the filler has a line included as
      -- part of its own square, we need to make a square
      -- included as part its own cube
      cu : (i j : I) → p (~ j) ＝ r j
      cu i j k = hfill (∂ i ∨ ∂ k) j λ where
        l (i = i0) → αf l k
        l (i = i1) → βf l k
        l (k = i0) → p (~ l)
        l (k = i1) → r l
        l (l = i0) → q k

      sq : (i : I) → w ＝ z
      sq i j = cu i i1 j

  dbl-comp-filler : Filler
  dbl-comp-filler = φ
    module dbl-comp-filler where
    private
      φ = (p ∙∙ q ∙∙ r) , λ i j → hfill (∂ j) i λ where
        l (j = i0) → p (~ l)
        l (j = i1) → r l
        l (l = i0) → q j
    
    sys : Square (sym p) q r (φ .fst)
    sys = φ .snd

  Filler-is-contr : is-contr (Filler)
  Filler-is-contr .ctr = dbl-comp-filler
  Filler-is-contr .paths z = Filler-unique (dbl-comp-filler) z

comp-filler : ∀ {ℓ} {A : Type ℓ} {x y z : A}
            → (p : x ＝ y) (q : y ＝ z) → Filler refl p q
comp-filler p q = p ∙ q , sys
  module comp-filler where
    sys : Square refl p q (p ∙ q)
    sys = dbl-comp-filler refl p q .snd

module _ {ℓ} {A : Type ℓ} where
  refl-coh₁ : {x y : A} (p : x ＝ y) → Square refl refl p p
  refl-coh₁ p i j = p (i ∧ j)

  refl-coh₂ : {x y : A} (p : x ＝ y) → Square p p refl refl
  refl-coh₂ p i j = p (i ∨ j)

  invr-path : {x y : A} (p : x ＝ y) → p ∙ sym p ＝ refl
  invr-path {x = x} p i j = hcomp (∂ j ∨ i) λ where
    k (j = i0) → x
    k (j = i1) → p (~ k ∧ ~ i)
    k (i = i1) → x
    k (k = i0) → p (~ i ∧ j)

  invl-path : {x y : A} (p : x ＝ y) → sym p ∙ p ＝ refl
  invl-path p = invr-path (sym p)

  idnl-path : {x y : A} (p : x ＝ y) → refl ∙ p ＝ p
  idnl-path {x} {y} p i j = hcomp (∂ j ∨ i) λ where
    k (j = i0) → x
    k (j = i1) → p (i ∨ k)
    k (i = i1) → p j
    k (k = i0) → p (i ∧ j)

  idnr-path : {x y : A} (p : x ＝ y) → p ∙ refl ＝ p
  idnr-path {x} {y} p i j = hcomp (∂ j ∨ i) (λ _ _ → p j)

  assoc-path : {w x y z : A} (p : w ＝ x) (q : x ＝ y) (r : y ＝ z)
             → p ∙ (q ∙ r) ＝ (p ∙ q) ∙ r
  assoc-path {w} {x} {y} {z} p q r k =
    comp-filler.sys p q k ∙ {!!}
    where
    φ : PathP (λ j → q (~ j) ＝ z) {!q!} {!!}
    φ j i = {!!}
