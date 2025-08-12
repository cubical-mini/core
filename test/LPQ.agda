{-# OPTIONS --safe #-}
module LPQ where

open import Foundations.Quiver.Base
open import Foundations.Quiver.Component
open import Foundations.Quiver.Discrete
open import Foundations.Quiver.Lens.Extend
open import Foundations.Quiver.Lens.Pull
open import Foundations.Quiver.Lens.Push
open import Foundations.Quiver.Path
open import Foundations.Quiver.Total.Base

open import Notation.Refl
open import Notation.Sym


-- instance
--   Path-Sym : ∀{ℓ} {A : Type ℓ} → Symω (Disc A)
--   Path-Sym .sym p i = p (~ i)

--   Path-Comp : ∀{ℓ} {A : Type ℓ} → HCompω (Disc A)
--   Path-Comp = {!!}

--   Path-Push-Path : ∀{ℓa ℓb} {A : Type ℓa} {B : A → Type ℓb}
--                  → Pushω (Disc A) (λ x → Paths (B x))
--   Path-Push-Path {B} .push p = transp (λ i → B (p i)) i0

--   Path-Push-Path-Lawful : ∀{ℓa ℓb} {A : Type ℓa} {B : A → Type ℓb}
--                         → Lawful-Pushω (Paths A) (λ x → Paths (B x))
--   Path-Push-Path-Lawful {B} .Lawful-Push.push-refl {x} {u} i = transp (λ _ → B x) i u

--   Path-Pull-Path : ∀{ℓa ℓb} {A : Type ℓa} {B : A → Type ℓb}
--                  → Pullω (Paths A) (λ x → Paths (B x))
--   Path-Pull-Path {B} .pull p = transp (λ i → B (p (~ i))) i0

--   Path-Lawful-Pull-Lawful : ∀{ℓa ℓb} {A : Type ℓa} {B : A → Type ℓb}
--                           → Lawful-Pullω (Paths A) (λ x → Paths (B x))
--   Path-Lawful-Pull-Lawful {B} .pull-refl {y} {v} i = transp (λ i → B y) (~ i) v

--   Path-Extend-Path : ∀{ℓa ℓb} {A : Type ℓa} {B : {x y : A} → x ＝ y → Type ℓb}
--                    → Extendω (Paths A) (λ p → Paths (B p))
--   Path-Extend-Path {B} .extend-l p = transp (λ i → B λ j → p (  i ∧ j)) i0
--   Path-Extend-Path {B} .extend-r p = transp (λ i → B λ j → p (~ i ∨ j)) i0

--   Path-Extend-Path-Lafwul : ∀{ℓa ℓb} {A : Type ℓa} {B : {x y : A} → x ＝ y → Type ℓb}
--                           → Lawful-Extendω (Paths A) (λ p → Paths (B p))
--   Path-Extend-Path-Lafwul .extend-refl = refl
--   Path-Extend-Path-Lafwul {B} .extend-coh {x} {u} i = hcomp (∂ i) λ where
--     j (i = i0) → transp (λ _ → B λ _ → x)    j  u
--     j (i = i1) → transp (λ _ → B λ _ → x) (~ j) u
--     j (j = i0) → transp (λ _ → B λ _ → x)    i  u

-- {-# OVERLAPPING
--   Path-Refl Path-Sym
-- #-}

-- {-# INCOHERENT
--   Path-Push-Path Path-Push-Path-Lawful
--   Path-Pull-Path Path-Lawful-Pull-Lawful
--   Path-Extend-Path Path-Extend-Path-Lafwul
-- #-}


-- module _ {ℓa ℓb} {A : Type ℓa} {B : Type ℓb} {f : A → B} {g : B → A} where private
--   open Quiverω Funs

--   test₁ : Ob _
--   test₁ = A

--   test₂ : Ob _
--   test₂ = B

--   test₃ : Hom A B
--   test₃ = f

--   test₄ : Hom A A
--   test₄ = refl

--   test₅ : Hom A A
--   test₅ = f ∙ g


-- module PathTest {ℓ} {A : Type ℓ} {x y : A} {p : x ＝ y} where private
--   open Quiverω (Paths A)

--   test₁ : Ob _
--   test₁ = x

--   test₂ : Hom y x
--   test₂ = sym p

--   test₃ : Hom x x
--   test₃ = refl

-- module PushTest {ℓa ℓb} {A : Type ℓa} {B : A → Type ℓb} {x y : A} {p : x ＝ y} where private

--   test₁ : B x → B y
--   test₁ = push p


-- -- observe posets where relation level is independent of carrier level
-- record Poset-on {ℓo} (A : Type ℓo) ℓh : Type (ℓo ⊔ lsuc ℓh) where
--   no-eta-equality
--   field _≤_ : A → A → Type ℓh

-- Monotone : ∀{ℓa ℓb ℓah ℓbh} {A : Type ℓa} {B : Type ℓb} (f : A → B) → Poset-on A ℓah → Poset-on B ℓbh → Type (ℓa ⊔ ℓah ⊔ ℓbh)
-- Monotone {A} f P Q = (x y : A) → x P.≤ y → f x Q.≤ f y where
--   module P = Poset-on P
--   module Q = Poset-on Q

-- Posetᵈ : Quiverωᵈ Funs 1 _ _
-- Posetᵈ .Quiverωᵈ.Ob[_] T (lh , _) = Poset-on T lh
-- Posetᵈ .has-quiver-onωᵈ .Quiver-onωᵈ.Hom[_] f = Monotone f

-- instance
--   Poset-Reflᵈ : ∀{ℓo ℓh} → Reflᵈ Funs Posetᵈ (ℓo , _) (ℓh , _)
--   Poset-Reflᵈ .reflᵈ _ _ _ = refl

-- module DispTest {ℓa ℓb ℓp ℓq} {A : Type ℓa} {B : Type ℓb} (f : A → B)
--   (PA : Poset-on A ℓp) (QB : Poset-on B ℓq) (m : Monotone f PA QB) where private
--   open Quiverωᵈ Posetᵈ

--   test₁ : Ob[ A ] _
--   test₁ = PA

--   test₂ : Ob[ B ] _
--   test₂ = QB

--   test₃ : Hom[ f ] PA QB
--   test₃ = m

--   test₄ : Hom[ refl ] PA PA
--   test₄ = reflᵈ PA


-- module CompTest {ℓa ℓp} {A : Type ℓa}
--   (open Quiverω (Component Posetᵈ A (ℓp , _)))
--   (P Q : Ob _) where private

--   test₁ : Poset-on A ℓp
--   test₁ = P

--   private module P = Poset-on P
--   private module Q = Poset-on Q

--   test₂ : (h : ∀ x y → x P.≤ y → x Q.≤ y) → Hom P Q
--   test₂ = refl


-- module TotalTest where
--   Posets : Quiverω 2 _ _
--   Posets = ∫ Posetᵈ
--   open Quiverω Posets

--   Poset : (ℓo ℓh : Level) → Type (lsuc (ℓo ⊔ ℓh))
--   Poset ℓo ℓh = Ob (ℓo , ℓh , _)

--   module _ {ℓa ℓb ℓp ℓq} {P : Poset ℓa ℓp} {Q : Poset ℓb ℓq} {f : Hom P Q} where
--     test₁ : P .fst → Q .fst
--     test₁ = f .hom

--     test₂ : Monotone (f .hom) (P .snd) (Q .snd)
--     test₂ = f .preserves


-- -- polynomials and lenses

-- Lensᵈ : Quiverωᵈ Funs 1 _ _
-- Lensᵈ .Quiverωᵈ.Ob[_] A (ℓb , _) = A → Type ℓb
-- Lensᵈ .has-quiver-onωᵈ .Quiver-onωᵈ.Hom[_] {x = A} f P Q = (x : A) → Q (f x) → P x

-- Lenses : Quiverω 2 _ _
-- Lenses = ∫ Lensᵈ

-- Poly : (ℓa ℓb : Level) → Type (lsuc (ℓa ⊔ ℓb))
-- Poly ℓa ℓb = Quiverω.Ob Lenses (ℓa , ℓb , _)

-- Lens : ∀{ℓa ℓb ℓc ℓd} → Poly ℓa ℓb → Poly ℓc ℓd → Type (ℓa ⊔ ℓb ⊔ ℓc ⊔ ℓd)
-- Lens = Quiverω.Hom Lenses


-- -- xxtra large spans!
-- module _ {n : ℕ} {ℓ-ob : ℓ-sig n} {ℓ-hom : ℓ-sig² n}
--   (C : Quiverω n ℓ-ob ℓ-hom) (open Quiverω C) ⦃ _ : Compω C ⦄ where

--   Spanᵈ : Quiverωᵈ C (n + n) _ _
--   Spanᵈ .Quiverωᵈ.Ob[_] T lsᵈ =
--     let las , lbs = ℓ-split n lsᵈ
--     in Σ (Ob las) λ A → Σ (Ob lbs) λ B → Hom T A × Hom T B
--   Spanᵈ .has-quiver-onωᵈ .Quiver-onωᵈ.Hom[_] {x = S} {y = T} f (A₁ , B₁ , sa , sb) (A₂ , B₂ , ta , tb) =
--     Σ (Hom A₁ A₂) λ fa → Σ (Hom B₁ B₂) λ fb → (f ∙ ta  ＝ sa ∙ fa) × (f ∙ tb ＝ sb ∙ fb)

--   Spans : Quiverω (n + (n + n)) _ _
--   Spans = ∫ Spanᵈ

-- -- spans of types
-- module FunSpan {ℓa ℓb ℓt} {A : Type ℓa} {B : Type ℓb} {T : Type ℓt} (p₁ : T → A) (p₂ : T → B) where private
--   open Quiverω (Spans Funs)

--   test : Ob _
--   test = T , A , B , p₁ , p₂

-- -- deriving composition from pull
-- module _ {n : ℕ} {ℓ-ob : ℓ-sig n} {ℓ-hom : ℓ-sig² n}
--   (C : Quiverω n ℓ-ob ℓ-hom) (open Quiverω C)
--   ⦃ FP : ∀{lys} {y : Ob lys} → Pullω C λ t → Paths (Hom t y) ⦄
--   ⦃ rc : Reflω C ⦄
--   ⦃ FPL : ∀{lys} {y : Ob lys} → Lawful-Pullω C λ t → Paths (Hom t y) ⦄
--   where private

--   instance
--     KEKW : Compω C
--     KEKW ._∙_ = pull

--   cmp-refl : ∀{lxs} {x : Ob lxs} → refl {x = x} ＝ refl ∙ refl
--   cmp-refl = pull-refl

-- -- deriving composition from push
-- module _ {n : ℕ} {ℓ-ob : ℓ-sig n} {ℓ-hom : ℓ-sig² n}
--   (C : Quiverω n ℓ-ob ℓ-hom) (open Quiverω C)
--   ⦃ FP : ∀{lys} {y : Ob lys} → Pushω C λ t → Paths (Hom y t) ⦄
--   ⦃ rc : Reflω C ⦄
--   ⦃ FPL : ∀{lys} {y : Ob lys} → Lawful-Pushω C λ t → Paths (Hom y t) ⦄
--   where private

--   instance
--     KEKW : Compω C
--     KEKW ._∙_ p q = push q p

--   hmm : ∀{lxs lys} {x : Ob lxs} {y : Ob lys} {u : Hom x y} → push u refl ＝ u
--   hmm = {!!}

--   -- here we need to commute pull
--   ass : ∀{lws lxs lys lzs} {w : Ob lws} {x : Ob lxs} {y : Ob lys} {z : Ob lzs}
--         {f : Hom w x} {g : Hom x y} {h : Hom y z}
--       → f ∙ (g ∙ h) ＝ (f ∙ g) ∙ h
--   ass {f} {g} {h} = {!!}

-- 𝐵 : ∀{ℓ} (A : Type ℓ) → Quiverω 0 _ _
-- 𝐵 A .Quiverω.Ob _ = ⊤
-- 𝐵 A .has-quiver-onω .Quiver-onω.Hom _ _ = A

-- data _≤_ : ℕ → ℕ → Type where
--   z≤ : ∀{n} → 0 ≤ n
--   s≤ : ∀{m n} → m ≤ n → suc m ≤ suc n

-- ℕ⃗ : Quiverω 0 _ _
-- ℕ⃗ .Quiverω.Ob _ = ℕ
-- ℕ⃗ .has-quiver-onω .Quiver-onω.Hom = _≤_

-- ≤-refl : ∀ n → n ≤ n
-- ≤-refl 0 = z≤
-- ≤-refl (suc n) = s≤ (≤-refl n)

-- ≤-trans : ∀ {m n k} → m ≤ n → n ≤ k → m ≤ k
-- ≤-trans z≤ q = z≤
-- ≤-trans (s≤ p) (s≤ q) = s≤ (≤-trans p q)

-- ≤-is-prop : ∀ {m n} (p q : m ≤ n) → p ＝ q
-- ≤-is-prop = {!!}

-- instance
--   -- 𝐵ℕ-Pull-Path : Pullω (𝐵 ℕ) λ _ → Paths ℕ -- pull in slices
--   -- 𝐵ℕ-Pull-Path .pull = _+_
--   -- {-# INCOHERENT 𝐵ℕ-Pull-Path #-}

--   𝐵ℕ-refl : Reflω (𝐵 ℕ)
--   𝐵ℕ-refl .refl = 0

--   -- 𝐵ℕ-Pull-Path-Lawful : Lawful-Pullω (𝐵 ℕ) λ _ → Paths ℕ
--   -- 𝐵ℕ-Pull-Path-Lawful .pull-refl = refl

--   -- 𝐵ℕ-Pull-ℕ⃗ : Pullω (𝐵 ℕ) λ _ → ℕ⃗
--   -- 𝐵ℕ-Pull-ℕ⃗ .pull = _+_

--   -- 𝐵ℕ-Pull-ℕ⃗-Lawful : Lawful-Pullω (𝐵 ℕ) λ _ → ℕ⃗
--   -- 𝐵ℕ-Pull-ℕ⃗-Lawful .pull-refl = refl

--   ℕ⃗-refl : Reflω ℕ⃗
--   ℕ⃗-refl .refl = ≤-refl _

--   ℕ⃗-comp : Compω ℕ⃗
--   ℕ⃗-comp ._∙_ p q = ≤-trans p q

-- ℕ⃗-parametric : {m n : ℕ} (α : ∀ t → t ≤ m → t ≤ n) {k : ℕ} (p : k ≤ m) → p ∙ α m refl ＝ α k p
-- ℕ⃗-parametric _ _ = ≤-is-prop _ _


-- open import Prim.Data.Bool

-- _or_ : Bool → Bool → Bool
-- false or y = y
-- true  or _ = true

-- instance
--   𝐵2-Pull-Path : Pullω (𝐵 Bool) λ _ → Paths Bool
--   𝐵2-Pull-Path .pull = _or_

--   𝐵2-Refl : Reflω (𝐵 Bool)
--   𝐵2-Refl .refl = false

--   𝐵2-Pull-Path-Lawful : Lawful-Pullω (𝐵 Bool) λ _ → Paths Bool
--   𝐵2-Pull-Path-Lawful .pull-refl = refl

--   𝐵2-Comp : Compω (𝐵 Bool)
--   𝐵2-Comp ._∙_ = pull

-- -- false
-- 𝐵2-parametric : (α : Bool → Bool) (p : Bool) → p ∙ α refl ＝ α p
-- 𝐵2-parametric α false = refl
-- 𝐵2-parametric α true = {!!}

-- -- true
-- -- Path-parametric : ∀{ℓ} {A : Type ℓ} {m n : A} (α : ∀ t → t ＝ m → t ＝ n) {k : A} (p : k ＝ m) → p ∙ α m refl ＝ α k p
-- -- Path-parametric = ?

-- -- Scope-parametric : ∀{ℓ} {A : Type ℓ} {m n : Scope A} (α : ∀ t → t ⊑ m → t ⊑ n) {k : Scope A} (p : k ⊑ m) → p ∙ α m refl ＝ α k p


-- Reprᵈ : {ℓ-ob : ℓ-sig 0} {ℓ-hom : ℓ-sig² 0} {C : Quiverω 0 ℓ-ob ℓ-hom} (open Quiverω C) ⦃ _ : Compω C ⦄
--       → Quiver-onωᵈ Ob Hom 0 (λ _ _ → ⊤) (λ _ _ _ _ → ℓ-ob tt ⊔ ℓ-hom tt tt)
-- Reprᵈ {C} .Quiver-onωᵈ.Hom[_] {x} {y} f _ _ = Σ (∀ t → Hom t x → Hom t y) λ α → α ＝ λ _ → _∙ f
--   where open Quiverω C

-- Yo : ∀{ℓ-ob ℓ-hom} (C : Quiverω 0 ℓ-ob ℓ-hom) (open Quiverω C)
--    → Quiverω 0 _ _
-- Yo C .Quiverω.Ob = C .Quiverω.Ob
-- Yo C .has-quiver-onω .Quiver-onω.Hom x y = ∀ t → Hom t x → Hom t y where open Quiverω C

-- module _ {ℓ ℓ′} {A : Type ℓ} {x : A} (P : (y : A) → x ＝ y → Type ℓ′) (d : P x refl) where
--   Jₚ : {y : A} (p : x ＝ y) → P y p
--   Jₚ {y} p = transp (λ i → P (path i .fst) (path i .snd)) i0 d where
--     path : Path (Σ A λ t → (x ＝ t)) (x , refl) (y , p)
--     path i = (p i) , (λ j → p (i ∧ j))

-- fun-ext : ∀{ℓ ℓ′}{A : Type ℓ} {B : A → I → Type ℓ′}
--           {f : (a : A) → B a i0} {g : (a : A) → B a i1}
--         → ((a : A) → Pathᴾ (B a ) (f a) (g a))
--         → Pathᴾ  (λ i → (x : A) →  B x i) f g
-- fun-ext p i x = p x i

-- ap : ∀{ℓ ℓ′}{A : Type ℓ}{B : A → Type ℓ′} (f : (a : A) → B a)
--      {x y : A} (p : x ＝ y) → Pathᴾ (λ i → B (p i)) (f x) (f y)
-- ap f p i = f (p i)

-- happly : ∀{ℓ ℓ′}{A : Type ℓ} {B : A → I → Type ℓ′}
--          {f : (a : A) → B a i0} {g : (a : A) → B a i1}
--        →           Pathᴾ (λ i → (a : A) → B a i) f g
--        → (x : A) → Pathᴾ (B x) (f x) (g x)
-- happly eq x i = eq i x

-- module _ {ℓ} {A : I → Type ℓ} {x : A i0} {y : A i1} where opaque
--   -- to-pathᴾ : (transport (λ i → A i) x ＝ y) → ＜ x ／ A ＼ y ＞
--   to-pathᴾ : (transp A i0 x ＝ y) → Pathᴾ A x y
--   to-pathᴾ p i = hcomp (∂ i) λ where
--     j (i = i0) → x
--     j (i = i1) → p j
--     j (j = i0) → transp (λ k → A {!~ k ∨ ~ i!}) i1 x -- coe0→i A i x

-- module _ {ℓ-ob ℓ-hom} {C : Quiverω 0 ℓ-ob ℓ-hom} (open Quiverω C) ⦃ _ : Reflω C ⦄ where private
--   Repᵈ : Quiverωᵈ (Yo C) 0 _ _
--   Repᵈ .Quiverωᵈ.Ob[_] _ _ = ⊤
--   Repᵈ .has-quiver-onωᵈ .Quiver-onωᵈ.Hom[_] {x} {y} α _ _ = Σ (Hom x y) λ u → u ＝ α _ refl

-- -- naive?
-- --     ∀ {t} (k : Hom t x) → α _ k ＝ k ∙ α _ refl

--     -- Rice's definition
--     --     ∀ {s t} (k : Hom s x) (g : Hom t x) (h : Hom s t) → k ＝ h ∙ g → α _ k ＝ h ∙ (α _ g)

--   instance
--     eehm : Reflω (Yo C)
--     eehm .refl _ f = f

--     sad : Compω (Yo C)
--     sad ._∙_ α β t f = β t (α t f)

--     kreks : Reflωᵈ (Yo C) Repᵈ
--     kreks .reflᵈ _ = refl , refl

--     asdwqe : Compωᵈ (Yo C) Repᵈ
--     asdwqe ._∙ᵈ_ {f} {g} (p , p′) (q , q′) = g _ (f _ refl) , refl

--   Reprs : Quiverω _ _ _
--   Reprs = ∫ Repᵈ

--   Repr = Quiverω.Ob Reprs
--   RHom = Quiverω.Hom Reprs

--   RHom-Pathᴾ : {x y : Repr _} (f g : RHom x y) (p : f .hom ＝ g .hom)
--                (p′ : Pathᴾ (λ i → Σ (Hom (x .fst) (y .fst)) λ u → u ＝ p i _ refl) (f .preserves) (g .preserves))
--              → f ＝ g
--   RHom-Pathᴾ f g p p′ i .hom = p i
--   RHom-Pathᴾ f g p p′ i .preserves = p′ i

--   -- hasd : {x y : Ob _} (u : ∀ t → Hom t x → Hom t y) (f g : ∀ {s t} (k : Hom s x) (g : Hom t x) (h : Hom s t) → k ＝ h ∙ g → u _ k ＝ h ∙ (u _ g))
--   --      → {s t : Ob _} → f {s = s} {t = t} ＝ g
--   -- hasd {x} {y} u f g = fun-ext λ a → fun-ext λ b → fun-ext λ c → fun-ext λ p →
--   --   {!!}
--     -- p : a ＝ c ∙ b

--   hasd : {x y : Repr _} (f g : RHom x y) → f .hom ＝ g .hom → f ＝ g
--   hasd f g prf = RHom-Pathᴾ f g prf (to-pathᴾ {!prop!!})
--   -- hasd {(x)} {(y)} _ _ prf i .hom = prf i
--   -- hasd {x = x , _} {y = y , _} (f ,⃗ f′ , p) (g ,⃗ g′ , q) prf i .preserves .fst = {!!}
--   -- hasd {x = x , _} {y = y , _} (f ,⃗ f′ , p) (g ,⃗ g′ , q) prf i .preserves .snd = {!!}

--   open import Foundations.Quiver.Total.Groupoid
--   -- instance
--   --   Repr-Comp : Compω Reprs
--   --   Repr-Comp = {!!}


--   ass-test : {w x y z : Repr _} (f : RHom w x) (g : RHom x y) (h : RHom y z)
--            → f ∙ (g ∙ h) ＝ f ∙ g ∙ h
--   ass-test f g h = hasd (f ∙ (g ∙ h)) (f ∙ g ∙ h) refl

--   module _
--     ⦃ FP : ∀{lys} {y : Ob lys} → Pushω C λ t → Paths (Hom y t) ⦄
--     ⦃ FPL : ∀{lys} {y : Ob lys} → Lawful-Pushω C λ t → Paths (Hom y t) ⦄ where

--     inject : ∀{x y} → Hom x y → RHom (x , tt) (y , tt)
--     inject f = (λ _ → push f) ,⃗ f , {!!}

--     extract : ∀{x y} → RHom (x , tt) (y , tt) → Hom x y
--     extract = λ z → z .preserves .fst

--     one-two : ∀{x y} (f : Hom x y) → extract (inject f) ＝ f
--     one-two f = refl

--     instance
--       C-Comp : Compω C
--       C-Comp ._∙_ f g = push g f

--     Repᵈ′ : Quiverωᵈ C 0 _ _
--     Repᵈ′ .Quiverωᵈ.Ob[_] _ _ = ⊤
--     Repᵈ′ .has-quiver-onωᵈ .Quiver-onωᵈ.Hom[_] {x} {y} f _ _ = Σ (∀ t → Hom t x → Hom t y) (λ α → α ＝ λ _ → push f)

--     module _ {x y} (f : Hom x y) (α : ∀ t → Hom t x → Hom t y) where
--       tooda : (α ＝ λ _ → push f) → f ＝ α _ refl
--       tooda p =
--         let uu = happly (happly p x) refl
--         in sym (uu ∙ {!!}) -- need left neutrality

--       obratno : (p : f ＝ α _ refl) → ((λ _ → push f) ＝ α)
--       obratno p = fun-ext λ a → fun-ext λ g → {!!}   -- naturality of α, i.e. α of anything is determined by pushing α 1

--     two-one : ∀{x y} (f : RHom x y) → inject (extract f) ＝ f
--     two-one {x = x , _} {y = y , _} (α ,⃗ f , p) = hasd _ _ (fun-ext (λ a → fun-ext (happly (happly (obratno f α p) a))))
