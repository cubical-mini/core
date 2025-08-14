{-# OPTIONS --safe #-}
module Graph where

open import Foundations.Base
open import Foundations.Discrete
open import Foundations.Functions
open import Foundations.Lens.Extend
open import Foundations.Lens.Pull
open import Foundations.Product
open import Foundations.Total as Total

open import Notation.Refl
open import Notation.Underlying

private variable ℓo ℓoa ℓob ℓh ℓha ℓhb : Level

Graph-on : (A : Type ℓo) → HQuiver-onω 1 _ _
Graph-on A = A ⋔̫ₜ A ⋔̫ₜ Funs

instance
  Graph-Pull : HPull Funs 1 Graph-on
  Graph-Pull ._◁_ {x = A} {y = B} f S a₁ a₂ = S (f a₁) (f a₂)
  Graph-Pull .pull-refl _ _ = id

Graphs : HQuiver-onω 2 _ _
Graphs = Σ̫[ Disp⁻ Graph-on ]

Graph : (ℓo ℓh : Level) → Type (lsuc (ℓo ⊔ ℓh))
Graph ℓo ℓh = Quiver-onω.Out Graphs (ℓo , ℓh , _) ; {-# NOINLINE Graph #-}

Graph-Hom : Graph ℓoa ℓha → Graph ℓob ℓhb → Type (ℓoa ⊔ ℓha ⊔ ℓob ⊔ ℓhb)
Graph-Hom = Graphs .Quiver-onω.Het ; {-# NOINLINE Graph-Hom #-}

Refl-on : (A : Graph ℓoa ℓha) (B : Graph ℓob ℓhb) (p : Graph-Hom A B) → HQuiver-onω 0 _ _
Refl-on (A , R) (B , S) (f₀ , _) = ∀̫ₜ[ a ꞉ A ] Disc (S (f₀ a) (f₀ a))

open Total.Instances
instance
  RxGraph-Extend : Extend Graphs 0 Refl-on
  RxGraph-Extend .extend-l {x = A , R} {y = B , S} (f , p) rfl {x = t} = p t t rfl
  RxGraph-Extend .extend-r {x = A , R} {y = B , S} (f , p) rfl = rfl
  RxGraph-Extend .extend-refl = refl
  RxGraph-Extend .extend-coh = refl

RxGraphs : HQuiver-onω 2 _ _
RxGraphs = Σ̫[ Disp± Refl-on ]

RxGraph : (ℓo ℓh : Level) → Type (lsuc (ℓo ⊔ ℓh))
RxGraph ℓo ℓh = Quiver-onω.Out RxGraphs (ℓo , ℓh , _) ; {-# NOINLINE RxGraph #-}

RxGraph-Hom : RxGraph ℓoa ℓha → RxGraph ℓob ℓhb → Type (ℓoa ⊔ ℓha ⊔ ℓob ⊔ ℓhb)
RxGraph-Hom = RxGraphs .Quiver-onω.Het ; {-# NOINLINE RxGraph-Hom #-}

Trans-on : (A : RxGraph ℓoa ℓha) (B : RxGraph ℓob ℓhb) (p : RxGraph-Hom A B) → HQuiver-onω 0 _ _
Trans-on ((A , R) , rflᵃ) ((B , S) , rflᵇ) ((f₀ , f₁) , pres-rfl)
  = ∀̫ₜ[ x ꞉ A ] ∀̫ₜ[ y ꞉ A ] ∀̫ₜ[ z ꞉ A ] Π̫ₜ[ p ꞉ R x y ] Π̫ₜ[ q ꞉ R y z ] Disc (S (f₀ x) (f₀ z))

instance
  RawCat-Extend : Extend RxGraphs 0 Trans-on
  RawCat-Extend .extend-l {x = (A , R) , rflᵃ} {y = (B , S) , rflᵇ} ((f₀ , f₁) , pres-rfl) comp p q =
    f₁ _ _ (comp p q)
  RawCat-Extend .extend-r {x = (A , R) , rflᵃ} {y = (B , S) , rflᵇ} ((f₀ , f₁) , pres-rfl) comp p q =
    comp (f₁ _ _ p) (f₁ _ _ q)
  RawCat-Extend .extend-refl _ _ = refl
  RawCat-Extend .extend-coh _ _ = refl

RawCats : HQuiver-onω 2 _ _
RawCats = Σ̫[ Disp± Trans-on ]

RawCat : (ℓo ℓh : Level) → Type (lsuc (ℓo ⊔ ℓh))
RawCat ℓo ℓh = Quiver-onω.Out RawCats (ℓo , ℓh , _) ; {-# NOINLINE RawCat #-}

RawFunctor : RawCat ℓoa ℓha → RawCat ℓob ℓhb → Type (ℓoa ⊔ ℓha ⊔ ℓob ⊔ ℓhb)
RawFunctor = RawCats .Quiver-onω.Het ; {-# NOINLINE RawFunctor #-}

module Test (C : RawCat ℓoa ℓha) (D : RawCat ℓob ℓhb) (F : RawFunctor C D) where

  C₀ : Type ℓoa
  C₀ = C .fst .fst .fst

  C₁ : C₀ → C₀ → Type ℓha
  C₁ = C .fst .fst .snd

  rflᶜ : ∀{x} → C₁ x x
  rflᶜ = C .fst .snd

  _∙ᶜ_ : ∀{x y z} → C₁ x y → C₁ y z → C₁ x z
  _∙ᶜ_ = C .snd

  D₀ : Type ℓob
  D₀ = D .fst .fst .fst

  D₁ : D₀ → D₀ → Type ℓhb
  D₁ = D .fst .fst .snd

  rflᵈ : ∀{x} → D₁ x x
  rflᵈ = D .fst .snd

  _∙ᵈ_ : ∀{x y z} → D₁ x y → D₁ y z → D₁ x z
  _∙ᵈ_ = D .snd

  F₀ : C₀ → D₀
  F₀ = F .fst .fst .fst

  F₁ : ∀{x y} → C₁ x y → D₁ (F₀ x) (F₀ y)
  F₁ = F .fst .fst .snd _ _

  F-pres-rfl : ∀{x} → F₁ (rflᶜ {x = x}) ＝ rflᵈ {x = F₀ x}
  F-pres-rfl = F .fst .snd

  F-pres-comp : ∀{x y z} {p : C₁ x y} {q : C₁ y z} → F₁ (p ∙ᶜ q) ＝ (F₁ p ∙ᵈ F₁ q)
  F-pres-comp = F .snd _ _
