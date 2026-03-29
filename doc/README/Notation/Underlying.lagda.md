```agda
module README.Notation.Underlying where

open import Foundations.Base
open import Foundations.Functions

open import Notation.Underlying
```

`Underlying` notation is for quivers where:
- both sorts of objects are morally displayed over types,
  but not neccessarily have the form `Σ Type λ T → Some-Structure-on T`
- heteromorphisms are structured functions

```agda
record Preset ℓo ℓh : Type (lsuc (ℓo ⊔ ℓh)) where
  field
    Ob  : Type ℓo
    _≤_ : Ob → Ob → Type ℓh
    ≤-refl  : {x : Ob} → x ≤ x
    ≤-trans : {x y z : Ob} → x ≤ y → y ≤ z → x ≤ z

record Monotone {ℓo ℓo′ ℓh ℓh′} (P : Preset ℓo ℓh) (Q : Preset ℓo′ ℓh′) : Type (ℓo ⊔ ℓo′ ⊔ ℓh ⊔ ℓh′) where
  module P = Preset P
  module Q = Preset Q
  field
    hom    : P.Ob → Q.Ob
    pres-≤ : ∀{x y} → x P.≤ y → hom x Q.≤ hom y

Presets : HQuiver-onω 2 (λ (lo , lh , _) → Preset lo lh) _
Presets .Quiver-onω.Het = Monotone

instance
  Presets-HUnderlying : HUnderlying Presets
  Presets-HUnderlying = mk-hunderlying Preset.Ob Monotone.hom
```

TODO: add a non-trivial `Underlying` instance for an inherently heterogeneous quiver
Forgetting/adding free structure sound boring, is there something cool to consider?
