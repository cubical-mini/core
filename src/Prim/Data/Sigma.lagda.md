```agda

{-# OPTIONS --safe #-}

module Prim.Data.Sigma where

open import Prim.Base.Type using ( Type; _⊔_ )
open import Prim.Base.Interval using ( _＝_ )

infixr 5 _×_
infixr -1 Σ-syntax 

```

Import the Sigma type from Agda.Builtin. We'll use TypeTopology's
notation because its far more convenient. We can use textbook style
notation if we want to annotate the type name with a syntax
declaration.

```

open import Agda.Builtin.Sigma public
  renaming ( Σ to Sigma )
  using ( _,_; fst; snd; module Σ ) -- keep the module the same name, it works

Σ : ∀ {ℓ ℓ'} {A : Type ℓ} → (A → Type ℓ') → Type (ℓ ⊔ ℓ')
Σ {A = A} B = Sigma A B
{-# INLINE Σ #-}
{-# INLINE _,_ #-}

Σ-syntax = Sigma
syntax Σ-syntax A (λ x → M) = Σ x ∶ A , M
{-# DISPLAY Σ-syntax _ B = Σ B #-}
{-# DISPLAY Sigma _ B = Σ B #-}

```

Next we define our induction principle for the Sigma type, which is
uncurrying, while the evaluation map of the Sigma type is currying.

```

module _ {u v w} {A : Type u} {B : A → Type v} (P : Σ B → Type w) where
  ind-Σ : ((x : A) (y : B x) → P (x , y)) → (z : Σ B) → P z
  ind-Σ g z = g (fst z) (snd z)

  indβ-Σ : (g : (x : A) (y : B x) → P (x , y)) ((x , y) : Σ B)
       → ind-Σ g (x , y) ＝ g x y  
  indβ-Σ g z i = g (fst z) (snd z)

  ev-Σ : ((z : Σ B) → P z) → (x : A) (y : B x) → P (x , y)
  ev-Σ g x y = g (x , y)

```

We also present our native notion of Cartesian product, with its
corresponding induction rule.

```

_×_ : ∀ {ℓ ℓ'} → Type ℓ → Type ℓ' → Type (ℓ ⊔ ℓ')
A × B = Sigma A (λ _ → B)

module _ {u v w} {A : Type u} {B : Type v} (P : A × B → Type w) where
  ind-× : ((x : A) (y : B) → P (x , y)) → (z : A × B) → P z
  ind-× g z = g (fst z) (snd z)

  indβ-× : (g : (x : A) (y : B) → P (x , y)) ((x , y) : A × B)
         → ind-× g (x , y) ＝ g x y
  indβ-× g z i = g (fst z) (snd z)
