{-# OPTIONS --safe #-}
module Notation.Base where

open import Prim.Type

ℓ-ob-sig = Level → Level
ℓ-hom-sig = Level → Level → Level

ob-sig : (ℓ-ob : ℓ-ob-sig) → Typeω
ob-sig ℓ-ob = ∀ ℓ → Type (ℓ-ob ℓ)
{-# INLINE ob-sig #-}

hom-sig : {ℓ-ob : ℓ-ob-sig} (Ob : ob-sig ℓ-ob) (ℓ-hom : ℓ-hom-sig) → Typeω
hom-sig Ob ℓ-hom = ∀{ℓx ℓy} → Ob ℓx → Ob ℓy → Type (ℓ-hom ℓx ℓy)
{-# INLINE hom-sig #-}

record Quiver-on {ℓ-ob : ℓ-ob-sig} (Ob : ob-sig ℓ-ob) (ℓ-hom : ℓ-hom-sig) : Typeω where
  constructor mk-quiver
  no-eta-equality
  field Hom : hom-sig Ob ℓ-hom
{-# INLINE mk-quiver #-}

record Small-quiver-on {ℓo : Level} (Ob : Type ℓo) (ℓh : Level) : Type (ℓo l⊔ lsuc ℓh) where
  constructor mk-small-quiver
  no-eta-equality
  field Hom : (x y : Ob) → Type ℓh
{-# INLINE mk-small-quiver #-}

Enlarge : ∀{ℓo ℓh} {Ob : Type ℓo} → Small-quiver-on Ob ℓh → Quiver-on (λ _ → Ob) λ _ _ → ℓh
Enlarge c .Quiver-on.Hom = Small-quiver-on.Hom c


-- globular vibe
2-hom-sig : {ℓ-ob : ℓ-ob-sig} (Ob : ob-sig ℓ-ob) {ℓ-hom : ℓ-hom-sig} (Hom : hom-sig Ob ℓ-hom) → Typeω
2-hom-sig Ob {ℓ-hom} Hom = ∀{ℓx ℓy} {x : Ob ℓx} {y : Ob ℓy} (f g : Hom x y) → Type (ℓ-hom ℓx ℓy)
{-# INLINE 2-hom-sig #-}

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig} (C : Quiver-on Ob ℓ-hom) (open Quiver-on C) where
  record 2-Quiver-on : Typeω where
    constructor mk-2-quiver
    no-eta-equality
    field Quiver₂ : ∀{ℓx ℓy} (x : Ob ℓx) (y : Ob ℓy) → Quiver-on (λ _ → Hom x y) (λ _ _ → ℓ-hom ℓx ℓy)

    2-Hom : 2-hom-sig Ob Hom
    2-Hom {ℓx} {ℓy} {x} {y} = Quiver-on.Hom (Quiver₂ x y) {ℓx} {ℓx} -- TODO no idea what's going on
{-# INLINE mk-2-quiver #-}


3-hom-sig : {ℓ-ob : ℓ-ob-sig} (Ob : ob-sig ℓ-ob) {ℓ-hom : ℓ-hom-sig} (Hom : hom-sig Ob ℓ-hom) (2-Hom : 2-hom-sig Ob Hom) → Typeω
3-hom-sig Ob {ℓ-hom} Hom 2-Hom = {ℓx ℓy : Level} {x : Ob ℓx} {y : Ob ℓy} {f g : Hom x y} (α β : 2-Hom f g) → Type (ℓ-hom ℓx ℓy)
{-# INLINE 3-hom-sig #-}

module _ {ℓ-ob : ℓ-ob-sig} {Ob : ob-sig ℓ-ob} {ℓ-hom : ℓ-hom-sig}
  (C : Quiver-on Ob ℓ-hom) (open Quiver-on C) (C₂ : 2-Quiver-on C) (open 2-Quiver-on C₂) where
  record 3-Quiver-on : Typeω where
    constructor mk-3-quiver
    no-eta-equality
    field Quiver₃ : {ℓx ℓy : Level} {x : Ob ℓx} {y : Ob ℓy} (f g : Hom x y) → Quiver-on (λ _ → 2-Hom f g) (λ _ _ → ℓ-hom ℓx ℓy)

    3-Hom : 3-hom-sig Ob Hom 2-Hom
    3-Hom {ℓx} {ℓy} {f} {g} = Quiver-on.Hom (Quiver₃ f g) {ℓx} {ℓx}
{-# INLINE mk-3-quiver #-}
