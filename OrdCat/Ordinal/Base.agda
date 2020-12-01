{-# OPTIONS --cubical --no-import-sorts --safe #-}
module OrdCat.Ordinal.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

private
  variable
    e p : Level

record OrderStructure : Type (ℓ-suc (ℓ-max e p)) where
  no-eta-equality
  field
    oe-type : Type e
    ≺-type : oe-type → oe-type → Type p

open OrderStructure public

record OrderElement (os : OrderStructure {e} {p}) : Type e where
  constructor oe-inject
  field
    oe-extract : os .oe-type

open OrderElement public

record _≺_ {os} (x y : OrderElement {e} {p} os) : Type p where
  constructor ≺-inject
  field
    ≺-extract : os .≺-type (x .oe-extract) (y .oe-extract)

open _≺_ public

data acc {os : OrderStructure {e} {p}} : OrderElement os → Type (ℓ-max e p) where
  acc-≺ : ∀ a → (∀ {b} → b ≺ a → acc b) → acc a

module _ (os : OrderStructure {e} {p}) where
  well-founded : Type (ℓ-max e p)
  well-founded = ∀ {a : OrderElement os} → acc a

  weakly-extensional : Type (ℓ-max e p)
  weakly-extensional = ∀ {a b : OrderElement os} → (∀ {c} → (c ≺ a → c ≺ b) × (c ≺ b → c ≺ a)) → a ≡ b

  order-transitive : Type (ℓ-max e p)
  order-transitive = ∀ {a b c : OrderElement os} → a ≺ b → b ≺ c → a ≺ c

record Order : Type (ℓ-suc (ℓ-max e p)) where
  no-eta-equality
  field
    order-os : OrderStructure {e} {p}
    oe-set : isSet (OrderElement order-os)
    ≺-prop : ∀ {x y : OrderElement order-os} → isProp (x ≺ y)

record WellFoundedExtensional : Type (ℓ-suc (ℓ-max e p)) where
  no-eta-equality
  field
    wfext-order : Order {e} {p}

  open Order wfext-order public

  field
    wfext-well-founded : well-founded order-os
    wfext-weakly-extensional : weakly-extensional order-os

record Ordinal : Type (ℓ-suc (ℓ-max e p)) where
  no-eta-equality
  field
    ordinal-wfext : WellFoundedExtensional {e} {p}

  open WellFoundedExtensional ordinal-wfext public

  field
    ordinal-transitive : order-transitive order-os

record Simulation {e₁ p₁ e₂ p₂} (A : WellFoundedExtensional {e₁} {p₁}) (B : WellFoundedExtensional {e₂} {p₂}) : Type (ℓ-max (ℓ-max e₁ e₂) (ℓ-max p₁ p₂)) where
  no-eta-equality
  private
    aos : OrderStructure {e₁} {p₁}
    aos = A .WellFoundedExtensional.order-os

    bos : OrderStructure {e₂} {p₂}
    bos = B .WellFoundedExtensional.order-os
  field
    sim-f : OrderElement aos → OrderElement bos
    sim-f-preserves-≺ : ∀ {a b} → a ≺ b → sim-f a ≺ sim-f b
    sim-f-image-initial : ∀ {a b} → b ≺ sim-f a → ∃[ a' ∈ OrderElement aos ] a' ≺ a × (sim-f a' ≡ b)
