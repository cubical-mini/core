```agda

{-# OPTIONS --safe #-}

module Lib.Equiv.Base where

open import Prim.Base
open import Prim.Kan
open import Prim.Pi
open import Prim.Data.Sigma

open import Lib.Path.Base
open import Lib.Path.Homotopy
open import Lib.HLevel.Base

record is-equiv {u v} {A : Type u} {B : Type v} (f : A → B) : Type (u ⊔ v) where
  no-eta-equality
  constructor equiv
  field
    inv : B → A
    sec : (x : A) → inv (f x) ＝ x
    retr : (y : B) → f (inv y) ＝ y
    coh : (x : A) → ap f (sec x) ＝ retr (f x)

  fun = f

open is-equiv public
  renaming ( inv to eqinv
           ; sec to eqv-is-sec
           ; retr to eqv-is-retr
           ; coh to eqv-coh
           ; fun to eqfun )
{-# INLINE eqfun #-}

```

Basic properties of is-equiv

```

-- eqv-inv-coh : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {f : A → B}
--             → (eq : is-equiv f) → is-equiv (eqinv eq)
-- eqv-inv-coh {f = f} eq .eqinv = eqfun eq
-- eqv-inv-coh eq .eqv-is-sec x = eqv-is-retr eq x
-- eqv-inv-coh eq .eqv-is-retr x = eqv-is-sec eq x
-- eqv-inv-coh {A = A} {f = f} eq .eqv-coh y i j = path i j
--   where
--   open is-equiv eq

--   path : ap inv (retr y) ＝ sec (inv y)
--   path i = tr2 (λ x y → ap inv x ＝ y) {!!} {!!} {!!} i



-- eqv-is-contr : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {f : A → B}
--              → is-equiv f → (y : B) → is-contr (fiber f y)
-- eqv-is-contr eq y .ctr = eqinv eq y , eqv-is-retr eq y
-- eqv-is-contr {f = f} eq y .paths (x , p) i = α i , β i where
--   open is-equiv eq
--   α : inv y ＝ x
--   α = ap inv (sym p) ∙ sec x

--   fib : f x ＝ y
--   fib = p

--   r : (y : _) → f (inv y) ＝ y
--   r y = retr y

--   fcoh : (i : I) → f (inv (f x)) ＝ f x
--   fcoh i = coh x i

--   fsec : (x : _) → f (inv (f x)) ＝ f x
--   fsec = λ x → ap f (sec x)

--   coh-sec : (i : I) → ∀ x → coh x i ＝ ap f (sec x)
--   coh-sec i x j k = {!!}

--   β : PathP (λ i → f (α i) ＝ y) (retr y) p
--   β i j = comp (λ k → f (α i) ＝ y) (λ k → λ {
--     (j = i0) → f (α i)
--     (j = i1) → y }) (λ _ → retr y j)

-- id-is-equiv : ∀ {ℓ} {A : Type ℓ} → is-equiv (idfun A)
-- id-is-equiv {A = A} .eqinv = idfun A
-- id-is-equiv {A = A} .eqv-is-sec = refl-htpy (idfun A)
-- id-is-equiv {A = A} .eqv-is-retr = refl-htpy (idfun A)
-- id-is-equiv {A = A} .eqv-coh = refl-htpy (ap id ∘ refl-htpy id)

-- inv-is-equiv : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {f : A → B}
--              → (eq : is-equiv f) → is-equiv (eqinv eq)
-- inv-is-equiv eq = {!!}

-- ```

-- Equivalences are an equivalence relation

-- ```

-- _≃_ : ∀ {u v} → Type u → Type v → Type (u ⊔ v)
-- A ≃ B = Σ f ∶ (A → B) , is-equiv f

-- eqvtofun : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → A ≃ B → A → B
-- eqvtofun (f , _) = f

-- -- The type of automorphisms of a type
-- Aut : ∀ {u} → Type u → Type u
-- Aut X = X ≃ X

-- refl-eqv : ∀ {ℓ} (X : Type ℓ) → Aut X
-- refl-eqv X = idfun X , id-is-equiv

-- -- sym-eqv : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → A ≃ B → B ≃ A
-- -- sym-eqv {A = A} (f , is-eqv) = e.inv , inv-is-equiv module _ where
-- --   private
-- --     module e = is-equiv is-eqv
-- --       renaming ( eqv-inv to inv
-- --                ; is-sec to sec
-- --                ; is-retr to retr
-- --                ; is-coh to coh )

-- --   inv-is-equiv : is-equiv (e.inv)
-- --   inv-is-equiv .eqv-inv = f
-- --   inv-is-equiv .is-sec y = e.retr y
-- --   inv-is-equiv .is-retr x = e.sec x
-- --   inv-is-equiv .is-coh y i j = φ i j
-- --     where
-- --     α : e.inv (f (e.inv y)) ＝ e.inv y
-- --     α = ap e.inv (e.retr y)

-- --     β : e.inv (f (e.inv y)) ＝ e.inv y
-- --     β = e.sec (e.inv y)

-- --     sec-coh : e.inv (f (e.inv y)) ＝ e.inv y
-- --     sec-coh = e.sec (e.inv y)

-- --     retr-coh : f (e.inv y) ＝ y
-- --     retr-coh = e.retr y

-- --     ap-coh : ap f (e.sec (e.inv y)) ＝ e.retr (f (e.inv y))
-- --     ap-coh = e.coh (e.inv y)

-- --     ap-face₁ : (k : I) → e.inv (f (e.inv (f (e.inv y)))) ＝ e.sec (e.inv y) k
-- --     ap-face₁ k = {! !}

-- --     ap-face₂ : (k : I) → e.inv (f (e.inv y)) ＝ e.inv (e.retr y k)
-- --     ap-face₂ k = ap e.inv {!!}

-- --     inv-sec : f (e.inv (f (e.inv y))) ＝ f (e.inv y)
-- --     inv-sec = ap f (e.sec (e.inv y))

-- --     sec-path : e.inv (f (e.inv y)) ＝ e.inv y
-- --     sec-path = e.sec (e.inv y)

-- --     inv-retr : e.inv (f (e.inv y)) ＝ e.inv y
-- --     inv-retr = ap e.inv (e.retr y)

-- --     γ : e.inv (f (e.inv y)) ＝ e.inv y
-- --     γ = ap e.inv (e.retr y)

-- --     φ : ap e.inv (e.retr y) ＝ e.sec (e.inv y)
-- --     φ i = {!γ i!}


-- ```

-- Sections and Retractions

-- ```
-- sec : ∀ {u v} {A : Type u} {B : Type v} (f : A → B) → Type (u ⊔ v)
-- sec {B = B} f = Σ g ∶ (B → _) , f ∘ g ∼ idfun B

-- retr : ∀ {u v} {A : Type u} {B : Type v} (f : A → B) → Type (u ⊔ v)
-- retr {A = A} f = Σ h ∶ (_ → A) , h ∘ f ∼ idfun A

-- module _ {u v} {A : Type u} {B : Type v} {f : A → B} where
--   equiv→sec : (eq : is-equiv f) → sec f
--   equiv→sec eq = eqinv eq , eqv-is-retr eq

--   equiv→retr : (eq : is-equiv f) → retr f
--   equiv→retr eq = eqinv eq , eqv-is-sec eq



-- module _ {ℓ} {A B : Type ℓ} where
--   idtoeqv : {i : I} → A ＝ B → A ≃ B
--   idtoeqv p = tr (A ≃_) p (refl-eqv A)
