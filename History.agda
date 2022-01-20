------------------------------------------------------------------------
-- An `Event` can also represent a `History` of events perceived by it.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)

module History (n : ℕ) (Msg : Set) where

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin)
open import Data.Product using (_×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; fromInj₁)
open import Event n Msg
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≢_; refl)

private
  variable
    p p′ p″ : Fin n
    m       : Msg

History = Event

private
  variable
    e  : Event p
    e′ : Event p′
    e″ : Event p″

data _∈_ : Event p → History p′ → Set where
  here   : e ∈ e
  there₁ : e ∈ e′ → e ∈ send m e′
  there₂ : e ∈ e′ → e ∈ recv e″ e′
  there₃ : e ∈ e″ → e ∈ recv e″ e′

data _∈⁻_ : Event p → History p → Set where
  here   : e ∈⁻ e
  there₁ : e ∈⁻ e′ → e ∈⁻ send m e′
  there₂ : e ∈⁻ e′ → e ∈⁻ recv e″ e′

∈-trans : e ∈ e′ → e′ ∈ e″ → e ∈ e″
∈-trans here       y          = y
∈-trans (there₁ x) here       = there₁ x
∈-trans (there₁ x) (there₁ y) = there₁ (∈-trans x (∈-trans (there₁ here) y))
∈-trans (there₁ x) (there₂ y) = there₂ (∈-trans x (∈-trans (there₁ here) y))
∈-trans (there₁ x) (there₃ y) = there₃ (∈-trans x (∈-trans (there₁ here) y))
∈-trans (there₂ x) here       = there₂ x
∈-trans (there₂ x) (there₁ y) = there₁ (∈-trans x (∈-trans (there₂ here) y))
∈-trans (there₂ x) (there₂ y) = there₂ (∈-trans x (∈-trans (there₂ here) y))
∈-trans (there₂ x) (there₃ y) = there₃ (∈-trans x (∈-trans (there₂ here) y))
∈-trans (there₃ x) here       = there₃ x
∈-trans (there₃ x) (there₁ y) = there₁ (∈-trans x (∈-trans (there₃ here) y))
∈-trans (there₃ x) (there₂ y) = there₂ (∈-trans x (∈-trans (there₃ here) y))
∈-trans (there₃ x) (there₃ y) = there₃ (∈-trans x (∈-trans (there₃ here) y))

-- This is the Lemma 2.2 of the "holy grail" paper
∈↔⊏ : e ≢ᵉ e′ → (e ∈ e′ → e ⊏ e′) × (e ⊏ e′ → e ∈ e′)
proj₁ (∈↔⊏ e≢ᵉe′) = fromInj₁ (λ x → ⊥-elim (e≢ᵉe′ x)) ∘ ∈→⊏
  where
  ∈→⊏ : e ∈ e′ → e ⊏ e′ ⊎ e ≡ᵉ e′
  ∈→⊏ here        = inj₂ refl
  ∈→⊏ (there₁ x) with ∈→⊏ x
  ... | inj₁ y    = inj₁ (trans y processOrder₁)
  ... | inj₂ refl = inj₁ processOrder₁
  ∈→⊏ (there₂ x) with ∈→⊏ x
  ... | inj₁ y    = inj₁ (trans y processOrder₂)
  ... | inj₂ refl = inj₁ processOrder₂
  ∈→⊏ (there₃ x) with ∈→⊏ x
  ... | inj₁ y    = inj₁ (trans y send⊏recv)
  ... | inj₂ refl = inj₁ send⊏recv
proj₂ (∈↔⊏ _) = ⊏→∈
  where
  ⊏→∈ : e ⊏ e′ → e ∈ e′
  ⊏→∈ processOrder₁ = there₁ here
  ⊏→∈ processOrder₂ = there₂ here
  ⊏→∈ send⊏recv     = there₃ here
  ⊏→∈ (trans x y)   = ∈-trans (⊏→∈ x) (⊏→∈ y)
