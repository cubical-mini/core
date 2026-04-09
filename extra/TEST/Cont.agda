{-# OPTIONS --safe #-}
module TEST.Cont where

open import Foundations.Base
open import Foundations.Discrete.Base
open import Foundations.Lens.Pull.Base
open import Foundations.Lens.Push.Base

open import Notation.Refl

module _ {m ℓ-ob} {Ob : ob-sig ℓ-ob} {ℓ-hom}
  (C : HQuiver-onω m Ob ℓ-hom) (open Quiver-onω C renaming (Het to Hom)) where

  record Container ls lp : Type (lsuc ls ⊔ ℓ-ob lp) where
    no-eta-equality
    constructor _▶_
    field
      Shape : Type ls
      Pos   : Shape → Out lp

  open Container

  record Lens {lsu lpu lsv lpv} (U : Container lsu lpu) (V : Container lsv lpv) : Type (lsu ⊔ lsv ⊔ ℓ-hom lpv lpu) where
    no-eta-equality
    field
      shape→ : U .Shape → V .Shape
      pos→   : (s : U .Shape) → Hom (V .Pos (shape→ s)) (U .Pos s)

  open Lens

  Poly : HQuiver-onω (1 + m) (λ ls → Container (ls .fst) (ls .snd)) _
  Poly .Quiver-onω.Het = Lens

  module _ ⦃ _ : Refl C ⦄ where instance
    Poly-Refl : Refl Poly
    Poly-Refl .refl .shape→ s = s
    Poly-Refl .refl .pos→ s = refl

    module _ ⦃ _ : ∀{ls} {y : Ob ls} → HPull C 0 (λ x → Disc (Hom x y)) ⦄ where
      Poly-Push : ∀{ls lss} {U : Container ls lss} → HPush Poly 0 λ V → Disc (Lens U V)
      Poly-Push ._▷_ p q .shape→ su = q .shape→ (p .shape→ su)
      Poly-Push ._▷_ p q .pos→ su = q .pos→ (p .shape→ su) ◁ p .pos→ su
      Poly-Push .push-refl {u} i .shape→ su = u .shape→ su
      Poly-Push .push-refl {u} i .pos→ su = pull-refl {v = u .pos→ su} (~ i)

    module _ ⦃ _ : ∀{ls} {x : Ob ls} → HPush C 0 (λ y → Disc (Hom x y)) ⦄ where
      Poly-Pull : ∀{ls lss} {V : Container ls lss} → HPull Poly 0 λ U → Disc (Lens U V)
      Poly-Pull ._◁_ p q .shape→ su = q .shape→ (p .shape→ su)
      Poly-Pull ._◁_ p q .pos→ su = q .pos→ (p .shape→ su) ▷ p .pos→ su
      Poly-Pull .pull-refl {v} i .shape→ su = v .shape→ su
      Poly-Pull .pull-refl {v} i .pos→ su = push-refl {u = v .pos→ su} (~ i)
