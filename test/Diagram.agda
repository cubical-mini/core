{-# OPTIONS --safe #-}
module Diagram where

open import Foundations.Base
open import Foundations.Diagram.Colimit
open import Foundations.Diagram.Limit
open import Foundations.Dual.Base
open import Foundations.Lens.Pull
open import Foundations.Lens.Push
open import Foundations.Functions
open import Foundations.Discrete

open import Notation.Refl

open Variadic-Pull
open Variadic-Push
open Colimit
open Limit
open is-universal⁻
open is-universal⁺

module Pi {lix} {Ix : Type lix} where
  PI : Quiver-onω 1 Types 1 (λ ls → Ix → Type (ls .fst)) _
  PI .Quiver-onω.Het P F = ∀ i → P → F i

  hmm : ∀{ls} {F : Ix → Type ls} → Pull Funs 0 λ X → Disc ((i : Ix) → X → F i)
  hmm ._◁_ {x = X} {y = Y} f α i x = α i (f x)
  hmm .pull-refl = refl

  pi : ∀{ls} (F : Ix → Type ls) → Limit Funs PI ⦃ Fun-Refl ⦄ ⦃ hmm ⦄ F ((lix ⊔ ls) , _)
  pi F .apex = (i : Ix) → F i
  pi F .ψ i f = f i
  pi F .lim-univ .unpull = λ u z i → u i z
  pi F .lim-univ .θ⁻ _ = refl
  pi F .lim-univ .unpull-unique u (w , z) j
    = (λ x i → z (~ j) i x)
    , λ k i x → z (~ j ∨ k) i x

  Preds : HQuiver-onω 1 (λ ls → Ix → 𝒰 (ls .fst)) _
  Preds .Quiver-onω.Het F G = (i : Ix) → F i → G i

  instance
    Pred-Refl : Refl Preds
    Pred-Refl .refl _ = id

  mmh : ∀{lys} {Y : Type lys} → Push Preds 0 λ F → Disc ((i : Ix) → Y → F i)
  mmh ._▷_ α f i y = f i (α i y)
  mmh .push-refl = refl

  copi : ∀{lys} (Y : Type lys) → Colimit Preds PI ⦃ Pred-Refl ⦄ ⦃ mmh ⦄ Y (lys , _)
  copi Y .coapex _ = Y
  copi Y .ψ _ = id
  copi Y .colim-univ .unpush = id
  copi Y .colim-univ .θ⁺ _ = refl
  copi Y .colim-univ .unpush-unique u (w , z) j
    = (λ i y → z j i y)
    , λ k i y → z (j ∧ k) i y


module Terminal where
  TERMINAL : Quiver-onω 1 Types 0 (λ _ → ⊤ₜ) λ _ _ → lzero
  TERMINAL .Quiver-onω.Het _ _ = ⊤ₜ

  terminal : Limit Funs TERMINAL tt (lzero , _)
  terminal .apex = ⊤ₜ
  terminal .ψ = tt
  terminal .lim-univ .unpull _ = λ _ → tt
  terminal .lim-univ .θ⁻ _ = refl
  terminal .lim-univ .unpull-unique _ _ = refl

  ! : ∀{ℓa} {A : Type ℓa} → (A → ⊤ₜ)
  ! {A} = terminal .lim-univ .unpull _

  !-unique : ∀{ℓa} {A : Type ℓa} (f : A → ⊤ₜ) → ! ＝ f
  !-unique {A} f = ap fst (terminal .lim-univ .unpull-unique _ (f , refl))


module Product where
  PRODUCT : Quiver-onω 1 Types 2 (λ (lx , ly , _) → Type lx ×ₜ Type ly ) _
  PRODUCT .Quiver-onω.Het P (A , B) = (P → A) ×ₜ (P → B)

  product : ∀{las lbs} (A : Type las) (B : Type lbs) → Limit Funs PRODUCT (A , B) ((las ⊔ lbs) , _)
  product A B .apex = A ×ₜ B
  product A B .ψ = fst , snd
  product A B .lim-univ .unpull (f , g) z = f z , g z
  product A B .lim-univ .θ⁻ _ = refl
  product A B .lim-univ .unpull-unique (f , g) (u , v) i
    = (λ q → v (~ i) .fst q , v (~ i) .snd q)
    , λ j → (λ q → v (~ i ∨ j) .fst q) , λ q → v (~ i ∨ j) .snd q

  ⟨_,_⟩ : ∀{las lbs lqs} {A : Type las} {B : Type lbs} {Q : Type lqs}
          (p1 : Q → A) (p2 : Q → B) → Q → A ×ₜ B
  ⟨ p1 , p2 ⟩ = product _ _ .lim-univ .unpull (p1 , p2)

  ⟨⟩∙π₁ : ∀{las lbs lqs} {A : Type las} {B : Type lbs} {Q : Type lqs}
          (p1 : Q → A) (p2 : Q → B) → fst ∘ ⟨ p1 , p2 ⟩ ＝ p1
  ⟨⟩∙π₁ p1 p2 = ap fst (product _ _ .lim-univ .θ⁻ (p1 , p2))

  ⟨⟩∙π₂ : ∀{las lbs lqs} {A : Type las} {B : Type lbs} {Q : Type lqs}
          (p1 : Q → A) (p2 : Q → B) → snd ∘ ⟨ p1 , p2 ⟩ ＝ p2
  ⟨⟩∙π₂ p1 p2 = ap snd (product _ _ .lim-univ .θ⁻ (p1 , p2))

  ⟨⟩-unique : ∀{las lbs lqs} {A : Type las} {B : Type lbs} {Q : Type lqs}
              (p1 : Q → A) (p2 : Q → B)
              (m : Q → A ×ₜ B) (u : fst ∘ m ＝ p1) (v : snd ∘ m ＝ p2)
            → m ＝ ⟨ p1 , p2 ⟩
  ⟨⟩-unique p1 p2 m u v = ap fst (λ i → product _ _ .lim-univ .unpull-unique (p1 , p2) (m , (u ,ₚ v)) (~ i))


module Exponential where
  EXP : Quiver-onω 1 Types 2 (λ (lx , ly , _) → Type lx ×ₜ Type ly) _
  EXP .Quiver-onω.Het P (A , B) = P ×ₜ A → B

  exponential : ∀{las lbs} (A : Type las) (B : Type lbs) → Limit Funs EXP (A , B) ((las ⊔ lbs) , _)
  exponential A B .apex = A → B
  exponential A B .ψ (f , a) = f a
  exponential A B .lim-univ .unpull {x = P} w p a = w (p , a)
  exponential A B .lim-univ .θ⁻ _ = refl
  exponential A B .lim-univ .unpull-unique {x = P} w (u , v) i
    = (λ p a → v (~ i) (p , a) )
    , λ j z → v (~ i ∨ j) z

  ev : ∀{ℓa ℓb} {A : Type ℓa} {B : Type ℓb}
     → ((A → B) ×ₜ A) → B
  ev {ℓa} {ℓb} = exponential _ _ .ψ

  ƛ : ∀{ℓa ℓb ℓg} {A : Type ℓa} {B : Type ℓb} {Γ : Type ℓg}
      (m : Γ ×ₜ A → B) → (Γ → (A → B))
  ƛ = exponential _ _ .lim-univ .unpull

  ƛ-commutes : ∀{ℓa ℓb ℓg} {A : Type ℓa} {B : Type ℓb} {Γ : Type ℓg}
               (m : Γ ×ₜ A → B)
             → ev ∘ (λ ga → ƛ m (ga .fst) , ga .snd) ＝ m
  ƛ-commutes = exponential _ _ .lim-univ .θ⁻

  ƛ-unique : ∀{ℓa ℓb ℓg} {A : Type ℓa} {B : Type ℓb} {Γ : Type ℓg}
             (m : Γ ×ₜ A → B) (m′ : Γ → (A → B))
           → ev ∘ (λ ga → m′ (ga .fst) , ga .snd) ＝ m
           → m′ ＝ ƛ m
  ƛ-unique {A} {B} m m′ p = ap fst (exponential _ _ .lim-univ .unpull-unique (λ z → m′ (z .fst) (z .snd)) (ƛ m , λ i → p (~ i)))
