------------------------------------------------------------------------
-- Defines `Event` and happens-before relation `_⊏_`, proves `_⊏_` is a
-- strict partial order.
--
-- Also defines (causal) `History` and sub-history relation `_⊆_`, proves
-- `_⊆_` is isomorphic to `_⊑_` (the reflexive closure of `_⊏_`).
------------------------------------------------------------------------

open import Data.Nat as ℕ

module Event (n : ℕ) (Msg : Set)  where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin)
open import Data.Nat.Properties as ℕₚ
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

Pid = Fin n

private
  variable
    p p′ p″ : Pid
    m       : Msg

data Event : Pid → Set where
  init : Event p
  send : Msg → Event p → Event p
  recv : Event p′ → Event p → Event p

private
  variable
    e  : Event p
    e′ : Event p′
    e″ : Event p″

data _⊏_ : Event p → Event p′ → Set where
  processOrder₁ : e ⊏ send m e
  processOrder₂ : e ⊏ recv e′ e
  send⊏recv     : e ⊏ recv e  e′
  trans         : e ⊏ e′ → e′ ⊏ e″ → e ⊏ e″

data _⊑_ : Event p → Event p′ → Set where
  refl : e ⊑ e
  lift : e ⊏ e′ → e ⊑ e′

------------------------------------------------------------------------
-- `_⊏_` is a strict partial order.

size : Event p → ℕ
size init        = zero
size (send _ e)  = suc (size e)
size (recv e e′) = suc (size e + size e′)

⊏-monotonic : e ⊏ e′ → size e < size e′
⊏-monotonic processOrder₁ = s≤s ≤-refl
⊏-monotonic processOrder₂ = s≤s (≤-stepsˡ _ ≤-refl)
⊏-monotonic send⊏recv     = s≤s (≤-stepsʳ _ ≤-refl)
⊏-monotonic (trans x y)   = ≤-trans (⊏-monotonic x) (<⇒≤ (⊏-monotonic y))

⊏-irreflexive : ¬ e ⊏ e
⊏-irreflexive x = 1+n≰n (⊏-monotonic x)

⊏-transitive : e ⊏ e′ → e′ ⊏ e″ → e ⊏ e″
⊏-transitive = trans

⊏-asymmetric : e ⊏ e′ → ¬ e′ ⊏ e
⊏-asymmetric x y = ⊥-elim (⊏-irreflexive (⊏-transitive x y))

⊏-antisymmetric : e ⊏ e′ → e′ ⊏ e → e ≡ e′
⊏-antisymmetric x y = ⊥-elim (⊏-irreflexive (⊏-transitive x y))

------------------------------------------------------------------------
-- `Event` can also be used as (causal) `History`.

History = Event

data _⊆_ : History p → History p′ → Set where
  here   : e ⊆ e
  there₁ : e ⊆ e′ → e ⊆ send m e′
  there₂ : e ⊆ e′ → e ⊆ recv e″ e′
  there₃ : e ⊆ e″ → e ⊆ recv e″ e′

⊆→⊑ : e ⊆ e′ → e ⊑ e′
⊆→⊑ here       = refl
⊆→⊑ (there₁ x) with ⊆→⊑ x
... | refl     = lift processOrder₁
... | lift y   = lift (trans y processOrder₁)
⊆→⊑ (there₂ x) with ⊆→⊑ x
... | refl     = lift processOrder₂
... | lift y   = lift (trans y processOrder₂)
⊆→⊑ (there₃ x) with ⊆→⊑ x
... | refl     = lift send⊏recv
... | lift y   = lift (trans y send⊏recv)

⊆-transitive : e ⊆ e′ → e′ ⊆ e″ → e ⊆ e″
⊆-transitive here       y          = y
⊆-transitive (there₁ x) here       = there₁ x
⊆-transitive (there₁ x) (there₁ y) = there₁ (⊆-transitive x (⊆-transitive (there₁ here) y))
⊆-transitive (there₁ x) (there₂ y) = there₂ (⊆-transitive x (⊆-transitive (there₁ here) y))
⊆-transitive (there₁ x) (there₃ y) = there₃ (⊆-transitive x (⊆-transitive (there₁ here) y))
⊆-transitive (there₂ x) here       = there₂ x
⊆-transitive (there₂ x) (there₁ y) = there₁ (⊆-transitive x (⊆-transitive (there₂ here) y))
⊆-transitive (there₂ x) (there₂ y) = there₂ (⊆-transitive x (⊆-transitive (there₂ here) y))
⊆-transitive (there₂ x) (there₃ y) = there₃ (⊆-transitive x (⊆-transitive (there₂ here) y))
⊆-transitive (there₃ x) here       = there₃ x
⊆-transitive (there₃ x) (there₁ y) = there₁ (⊆-transitive x (⊆-transitive (there₃ here) y))
⊆-transitive (there₃ x) (there₂ y) = there₂ (⊆-transitive x (⊆-transitive (there₃ here) y))
⊆-transitive (there₃ x) (there₃ y) = there₃ (⊆-transitive x (⊆-transitive (there₃ here) y))

⊑→⊆ : e ⊑ e′ → e ⊆ e′
⊑→⊆ refl     = here
⊑→⊆ (lift x) = ⊏→⊆ x
  where
  ⊏→⊆ : e ⊏ e′ → e ⊆ e′
  ⊏→⊆ processOrder₁ = there₁ here
  ⊏→⊆ processOrder₂ = there₂ here
  ⊏→⊆ send⊏recv     = there₃ here
  ⊏→⊆ (trans x y)   = ⊆-transitive (⊏→⊆ x) (⊏→⊆ y)
