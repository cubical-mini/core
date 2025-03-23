```

{-# OPTIONS --safe #-}

module Lib.HLevel.Base where

open import Prim.Base
open import Prim.Data.Nat using ( ℕ; zero; suc )

record is-contr {ℓ} (A : Type ℓ) : Type ℓ where
  no-eta-equality
  field
    ctr : A
    paths : (y : A) → ctr ≡ y

open is-contr {{...}} public

is-prop : ∀ {ℓ} → Type ℓ → Type ℓ
is-prop A = (x y : A) → x ≡ y

is-propd : ∀ {u v} {A : Type u} → (A → Type v) → Type (u ⊔ v)
is-propd B = ∀ x → is-prop (B x)

is-set : ∀ {ℓ} → Type ℓ → Type ℓ
is-set A = {x y : A} (p q : x ≡ y) → p ≡ q

is-hom-set : ∀ {o h} {ob : Type o} → (ob → ob → Type h) → Type (o ⊔ h)
is-hom-set H = ∀ x y → is-set (H x y)

is-grpd : ∀ {ℓ} → Type ℓ → Type ℓ
is-grpd A = {x y : A} {p q : x ≡ y} (r s : p ≡ q) → r ≡ s

is-hlevel : ∀ {ℓ} → ℕ → Type ℓ → Type ℓ
is-hlevel zero A = is-contr A
is-hlevel (suc zero) A = is-prop A
is-hlevel (suc (suc n)) A = {x y : A} → is-hlevel (suc n) (Path A x y)
{-# DISPLAY is-hlevel 0 A = is-contr A #-}
{-# DISPLAY is-hlevel 1 A = is-prop A #-}
{-# DISPLAY is-hlevel 2 A = is-set A #-}
{-# DISPLAY is-hlevel 3 A = is-grpd A #-}

-- use for situations where we'd calculate too many implicits
is-hlevelₑ : ∀ {ℓ} → ℕ → Type ℓ → Type ℓ
is-hlevelₑ zero A = is-contr A
is-hlevelₑ (suc zero) A = is-prop A
is-hlevelₑ (suc (suc n)) A = (x y : A) → is-hlevel n (Path A x y)

private module _ {ℓ} (A : Type ℓ) where
  _ : is-contr A ≡ is-hlevel 0 A
  _ = refl

  _ : is-prop A ≡ is-hlevel 1 A
  _ = refl

  _ : is-set A ≡ is-hlevel 2 A
  _ = refl

  _ : is-grpd A ≡ is-hlevel 3 A
  _ = refl

```

Now we define the Data types presenting these

```
-- 1lab's definitions are to the point
record n-Type ℓ n : Type₊ ℓ where
  no-eta-equality
  constructor el
  field
    ∣_∣ : Type ℓ
    is-tr : is-hlevel n ∣_∣

Prop : ∀ ℓ → Type₊ ℓ
Prop ℓ = n-Type ℓ 1

Set : ∀ ℓ → Type₊ ℓ
Set ℓ = n-Type ℓ 2
