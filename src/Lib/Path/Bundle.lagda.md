```agda

{-# OPTIONS --safe #-}

module Lib.Path.Bundle where

open import Prim.Base
open import Prim.Pi
open import Prim.Data.Sigma

open import Lib.Path.Base

Bundle : ∀ {u v} {E : Type u} (B : E → Type v) (f : Π B) (e : E) → B e → Type (u ⊔ v)
Bundle {E} B f e b = Σ x ∶ E , Σ p ∶ e ＝ x , PathP (λ i → B (p i)) (f (p i0)) (f (p i1))

brefl : ∀ {u v} {E : Type u} {B : E → Type v}
      → (f : Π B) {e : E} →  Bundle B f e (f e)
brefl f {e} = e , refl , refl

bget : ∀ {u v} {E : Type u} {B : E → Type v} {f : Π B} {e : E} {b : B e}
     → Bundle B f e b → Σ x ∶ E , (e ＝ x)
bget (x , p , _) = x , p

bput : ∀ {u v} {E : Type u} {B : E → Type v} {f : Π B} {e : E} {b : B e}
     → {x : E} → (p : e ＝ x) → Bundle B f e b
bput {f = f} p = p i1 , p , ap f p


ind-Bundle : ∀ {u v w} {E : Type u} {B : E → Type v} {f : Π B} {e : E}
           → (P : (y : B e) → Bundle B f e y → Type w)
           → P (f e) (brefl f)
           → (b : B e) (q : Bundle B f e b)
           → P b q
ind-Bundle {B = B} {f} {e} P r b (d , p , q) = {!!}
  where
  F : B d → B e
  F = tr B (sym p) 
  φ = {!!}

CoYoneda : ∀ {u v} {E : Type u} {B : Type v} → (E → B) → B → E → Type v
CoYoneda {E = E} {B} f a e = Bundle (const B) id a (f e)

apco : ∀ {u v w} {E : Type u} {B : Type v} {D : Type w}
         → (f : E → B) (g : B → D)
         → {e : E} {b : B} → CoYoneda f b e
         → CoYoneda g (g b) (f e)
apco f g {b = b} (x , p , q) = g b , ap g (p ∙ sym q) , refl
