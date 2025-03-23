```agda

{-# OPTIONS --safe #-}

module Control.Applicative.Base where

open import Prim.Prelude

record Applicative {ℓ ℓ'} (F : Type ℓ → Type ℓ') : Type (ℓ ₊ ⊔ ℓ') where
  infixl 4 _<*>_ _<*_ _*>_
  field
    pure : ∀ {A} → A → F A
    _<*>_ : ∀ {A B} → F (A → B) → F A → F B
    idnl : ∀ {A} (fa : F A) → pure (idfun A) <*> fa ≡ fa
    assoc : {A B C : Type ℓ} (u : F (B → A → C)) (v : F (A → B)) (w : F A)
          → pure _∘ₛ_ <*> u <*> v <*> w ≡ u <*> (v <*> w)
    hom : ∀ {A B} (f : A → B) {x : A} → pure f <*> pure x ≡ pure (f x)
    inter : ∀ {A B} (u : F (A → B)) (x : A) → u <*> pure x ≡ pure (λ f → f x) <*> u

  _<$>_ : ∀ {A B} → (A → B) → F A → F B
  f <$> u = pure f <*> u

  _<*_ : ∀ {A B} → F A → F B → F A
  a <* b = const <$> a <*> b

  _*>_ : ∀ {A B} → F A → F B → F B
  a *> b = flip const <$> a <*> b

  zipWith : ∀ {A B C} → (A → B → C) → F A → F B → F C
  zipWith f x y = f <$> x <*> y

  zip : ∀ {A B} → F A → F B → F (A × B)
  zip = zipWith _,_

  -- Haskell-style alternative name for pure
  return : ∀ {A} → A → F A
  return = pure

