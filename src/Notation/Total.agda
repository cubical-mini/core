{-# OPTIONS --safe #-}
module Notation.Total where

open import Notation.Base

-- total object level adjustment
ℓ-sig∫ : {n : ℕ} (ℓ-obω : ℓ-sig n)
       → {m : ℕ} (ℓ-obωᵈ : ℓ-sig (n + m)) → ℓ-sig (n + m)
ℓ-sig∫ {0} ℓo {0} ℓoᵈ = ℓo ⊔ ℓoᵈ
ℓ-sig∫ {0} ℓo {suc m} ℓ-obωᵈ ℓ = ℓ-sig∫ ℓo (ℓ-obωᵈ ℓ)
ℓ-sig∫ {suc n} ℓ-obω ℓ-obωᵈ ℓ = ℓ-sig∫ (ℓ-obω ℓ) (ℓ-obωᵈ ℓ)

-- total object signature
ΣObω : {n : ℕ} {ℓ-obω : ℓ-sig n} {Obω : ob-sigω ℓ-obω}
       {m : ℕ} (ℓ-obωᵈ : ℓ-sig (n + m)) (Obω[_] : ob-sigωᵈ ℓ-obω Obω ℓ-obωᵈ)
     → ob-sigω (ℓ-sig∫ ℓ-obω ℓ-obωᵈ)
ΣObω {0} {Obω = liftω Ob} {m = 0} ℓ-obωᵈ Ob[_] .lowerω = Σ Ob λ x → Ob[ x ] tt
ΣObω {0} {m = suc m} ℓ-obωᵈ Obω[_] ℓ = ΣObω {0} (ℓ-obωᵈ ℓ) λ t ls → Obω[ t ] (ℓ , ls)
ΣObω {suc n} ℓ-obωᵈ Obω[_] ℓ = ΣObω (ℓ-obωᵈ ℓ) (Obω[_] {ℓ})


-- total arrow level adjustment
ℓ-sig∫² : {n : ℕ} (ℓ-obω⁻ ℓ-obω⁺ : ℓ-sig n) (ℓ-homω : ℓ-sig² n)
          {m : ℕ} (ℓ-obωᵈ⁻ ℓ-obωᵈ⁺ : ℓ-sig (n + m)) (ℓ-homωᵈ : ℓ-sig² (n + m))
        → ℓ-sig² (n + m)
ℓ-sig∫² {(zero)} _ _ ℓh {0} _ _ ℓhᵈ = ℓh ⊔ ℓhᵈ
ℓ-sig∫² {(zero)} ℓo⁻ ℓo⁺ ℓh {suc m} ℓ-obωᵈ⁻ ℓ-obωᵈ⁺ ℓ-homωᵈ ℓx ℓy =
  ℓ-sig∫² ℓo⁻ ℓo⁺ ℓh (ℓ-obωᵈ⁻ ℓx) (ℓ-obωᵈ⁺ ℓy) (ℓ-homωᵈ ℓx ℓy)
ℓ-sig∫² {suc n} ℓ-obω⁻ ℓ-obω⁺ ℓ-homω ℓ-obωᵈ⁻ ℓ-obωᵈ⁺ ℓ-homωᵈ ℓx ℓy =
  ℓ-sig∫² {n} (ℓ-obω⁻ ℓx) (ℓ-obω⁺ ℓy) (ℓ-homω ℓx ℓy) (ℓ-obωᵈ⁻ ℓx) (ℓ-obωᵈ⁺ ℓy) (ℓ-homωᵈ ℓx ℓy)

module _ {n : ℕ} {ℓ-obω⁻ ℓ-obω⁺ : ℓ-sig n} {ℓ-homω : ℓ-sig² n}
  (Obω⁻ : ob-sigω ℓ-obω⁻) (Obω⁺ : ob-sigω ℓ-obω⁺) (Homω : hom-sigω ℓ-obω⁻ ℓ-obω⁺ ℓ-homω Obω⁻ Obω⁺)
  {m : ℕ} {ℓ-obωᵈ⁻ ℓ-obωᵈ⁺ : ℓ-sig (n + m)} {ℓ-homωᵈ : ℓ-sig² (n + m)}
  (Obω[_]⁻ : ob-sigωᵈ ℓ-obω⁻ Obω⁻ ℓ-obωᵈ⁻) (Obω[_]⁺ : ob-sigωᵈ ℓ-obω⁺ Obω⁺ ℓ-obωᵈ⁺)
  (Homω[_] : hom-sigωᵈ ℓ-obω⁻ ℓ-obω⁺ Obω⁻ Obω⁺ ℓ-homω Homω ℓ-obωᵈ⁻ ℓ-obωᵈ⁺ Obω[_]⁻ Obω[_]⁺ ℓ-homωᵈ)
  {lxs lys : Levels n} {x : Ob′ n ℓ-obω⁻ Obω⁻ lxs} {y : Ob′ n ℓ-obω⁺ Obω⁺ lys}
  where

  -- saturated application of total arrow signature
  infixr 40 _,⃗_
  record ΣHom {lxsᵈ lysᵈ}
    (x′ : Ob[_]′ n ℓ-obω⁻ Obω⁻ m ℓ-obωᵈ⁻ Obω[_]⁻ lxs x lxsᵈ)
    (y′ : Ob[_]′ n ℓ-obω⁺ Obω⁺ m ℓ-obωᵈ⁺ Obω[_]⁺ lys y lysᵈ) : Type
      ( ℓ-hom ℓ-obω⁻ ℓ-obω⁺ ℓ-homω lxs lys
      ⊔ ℓ-homᵈ ℓ-obω⁻ ℓ-obω⁺ ℓ-homω ℓ-obωᵈ⁻ ℓ-obωᵈ⁺ ℓ-homωᵈ lxs lys lxsᵈ lysᵈ) where
    constructor _,⃗_
    field
      hom       : Hom′ n ℓ-obω⁻ ℓ-obω⁺ ℓ-homω Obω⁻ Obω⁺ Homω lxs lys x y
      preserves : Hom[_]′ n ℓ-obω⁻ ℓ-obω⁺ ℓ-homω Obω⁻ Obω⁺ Homω lxs lys m ℓ-obωᵈ⁻ ℓ-obωᵈ⁺ Obω[_]⁻ Obω[_]⁺ ℓ-homωᵈ Homω[_] lxsᵈ lysᵈ x y hom x′ y′
  open ΣHom public

-- total arrow signature
ΣHomω : {n : ℕ} {ℓ-obω⁻ ℓ-obω⁺ : ℓ-sig n} {ℓ-homω : ℓ-sig² n}
        (Obω⁻ : ob-sigω ℓ-obω⁻) (Obω⁺ : ob-sigω ℓ-obω⁺) (Homω : hom-sigω ℓ-obω⁻ ℓ-obω⁺ ℓ-homω Obω⁻ Obω⁺)
        {m : ℕ} {ℓ-obωᵈ⁻ ℓ-obωᵈ⁺ : ℓ-sig (n + m)} (ℓ-homωᵈ : ℓ-sig² (n + m))
        (Obω[_]⁻ : ob-sigωᵈ ℓ-obω⁻ Obω⁻ ℓ-obωᵈ⁻) (Obω[_]⁺ : ob-sigωᵈ ℓ-obω⁺ Obω⁺ ℓ-obωᵈ⁺)
        (Homω[_] : hom-sigωᵈ ℓ-obω⁻ ℓ-obω⁺ Obω⁻ Obω⁺ ℓ-homω Homω ℓ-obωᵈ⁻ ℓ-obωᵈ⁺ Obω[_]⁻ Obω[_]⁺ ℓ-homωᵈ)
      → hom-sigω (ℓ-sig∫ ℓ-obω⁻ ℓ-obωᵈ⁻) (ℓ-sig∫ ℓ-obω⁺ ℓ-obωᵈ⁺)
          (ℓ-sig∫² ℓ-obω⁻ ℓ-obω⁺ ℓ-homω ℓ-obωᵈ⁻ ℓ-obωᵈ⁺ ℓ-homωᵈ)
          (ΣObω ℓ-obωᵈ⁻ Obω[_]⁻) (ΣObω ℓ-obωᵈ⁺ Obω[_]⁺)
ΣHomω {0} Obω⁻ Obω⁺ Homω {0} _ Obω[_]⁻ Obω[_]⁺ Homω[_] .lowerω (x , x′) (y , y′) =
  ΣHom Obω⁻ Obω⁺ Homω {0} (λ t _ → Obω[ t ]⁻ _) (λ t _ → Obω[ t ]⁺ _) (λ g → Homω[ g ]) x′ y′
ΣHomω {0} Obω⁻ Obω⁺ Homω {suc m} ℓ-homωᵈ Obω[_]⁻ Obω[_]⁺ Homω[_] {ℓx} {ℓy} =
  ΣHomω {0} Obω⁻ Obω⁺ Homω {m} (ℓ-homωᵈ ℓx ℓy)
    (λ t ls → Obω[ t ]⁻ (ℓx , ls)) (λ t ls → Obω[ t ]⁺ (ℓy , ls))
    (λ g → Homω[ g ])
ΣHomω {suc n} Obω⁻ Obω⁺ Homω ℓ-homωᵈ Obω[_]⁻ Obω[_]⁺ Homω[_] {ℓx} {ℓy}=
  ΣHomω {n} (Obω⁻ ℓx) (Obω⁺ ℓy) Homω (ℓ-homωᵈ ℓx ℓy) Obω[_]⁻ Obω[_]⁺ Homω[_]

module _ {n : ℕ} {ℓ-obω : ℓ-sig n} {ℓ-homω : ℓ-sig² n}
  (C : Quiverω n ℓ-obω ℓ-homω) (open Quiverω C)
  {m : ℕ} {ℓ-obωᵈ : ℓ-sig (n + m)} {ℓ-homωᵈ : ℓ-sig² (n + m)}
  (D : Quiverωᵈ C m ℓ-obωᵈ ℓ-homωᵈ) (open Quiverωᵈ D) where

  -- total quiver of arbitrary size
  ∫ : Quiverω (n + m) (ℓ-sig∫ ℓ-obω ℓ-obωᵈ) (ℓ-sig∫² ℓ-obω ℓ-obω ℓ-homω ℓ-obωᵈ ℓ-obωᵈ ℓ-homωᵈ)
  ∫ .Quiverω.Obω  = ΣObω ℓ-obωᵈ Obω[_]
  ∫ .Quiverω.Homω = ΣHomω Obω Obω Homω ℓ-homωᵈ Obω[_] Obω[_] Homω[_]
