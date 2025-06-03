{-# OPTIONS --safe #-}
module Prim.Type where

open import Agda.Primitive public
  using ()
  renaming ( Set  to 𝒰
           ; Setω to 𝒰ω )
open import Agda.Primitive public
  using ( SSet
        ; SSetω
        ; LevelUniv
        ; Level
        ; lzero
        ; lsuc )
  renaming ( Prop  to DIProp
           ; Set   to Type
           ; Setω  to Typeω
           ; _⊔_   to _l⊔_ )

level-of-type : {ℓ : Level} → Type ℓ → Level
level-of-type {ℓ} _ = ℓ

level-of-term : {ℓ : Level} {A : Type ℓ} → A → Level
level-of-term {ℓ} _ = ℓ

record Lift {ℓ} ℓ′ (A : Type ℓ) : Type (ℓ l⊔ ℓ′) where
  constructor lift
  field lower : A
open Lift public

record Liftω {ℓ} (A : Type ℓ) : Typeω where
  constructor liftω
  field lower : A
open Liftω public

record Erased {ℓ} (@0 A : Type ℓ) : Type ℓ where
  constructor erase
  field @0 erased : A
open Erased public

instance
  Lift-default : {ℓ ℓ′ : Level} {A : Type ℓ} → ⦃ A ⦄ → Lift ℓ′ A
  Lift-default ⦃ (a) ⦄ = lift a

  Liftω-default : {ℓ : Level} {A : Type ℓ} → ⦃ A ⦄ → Liftω A
  Liftω-default ⦃ (a) ⦄ = liftω a

  Erased-default : {ℓ : Level} {A : Type ℓ} → ⦃ A ⦄ → Erased A
  Erased-default ⦃ (a) ⦄ .erased = a

{-# INCOHERENT Lift-default Liftω-default Erased-default #-}


-- Useful gadgets

the : ∀{ℓ} (A : Type ℓ) → A → A
the _ a = a

auto : ∀{ℓ} {A : Type ℓ} → ⦃ A ⦄ → A
auto ⦃ (a) ⦄ = a

autoω : {A : Typeω} → ⦃ A ⦄ → A
autoω ⦃ (a) ⦄ = a
