------------------------------------------------------------------------
-- Defines `Event` and happens-before relation `_≺_`, proves `_≺_` is a
-- strict partial order.
------------------------------------------------------------------------

module Event (Pid : Set) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat as ℕ
open import Data.Nat.Properties as ℕₚ
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

private
  variable
    p p′ p″ q : Pid

data Event : Pid → Set where
  init : Event p
  send : Event p → Event p
  recv : Event p → Event q → Event p

private
  variable
    e  : Event p
    e′ : Event p′
    e″ : Event p″

data _≺_ : Event p → Event q → Set where
  processOrder₁ : e  ≺ send e
  processOrder₂ : e  ≺ recv e e′
  send≺receive  : e′ ≺ recv e e′
  trans         : e ≺ e′ → e′ ≺ e″ → e ≺ e″

------------------------------------------------------------------------
-- `_≺_` is a strict partial order.

size : Event p → ℕ
size init        = zero
size (send e)    = suc (size e)
size (recv e e′) = suc (size e + size e′)

≺-monotonic : e ≺ e′ → size e < size e′
≺-monotonic processOrder₁ = s≤s ≤-refl
≺-monotonic processOrder₂ = s≤s (≤-stepsʳ _ ≤-refl)
≺-monotonic send≺receive  = s≤s (≤-stepsˡ _ ≤-refl)
≺-monotonic (trans x y)   = ≤-trans (≺-monotonic x) (<⇒≤ (≺-monotonic y))

≺-irreflexive : ¬ e ≺ e
≺-irreflexive x = 1+n≰n (≺-monotonic x)

≺-transitive : e ≺ e′ → e′ ≺ e″ → e ≺ e″
≺-transitive = trans

≺-asymmetric : e ≺ e′ → ¬ e′ ≺ e
≺-asymmetric x y = ⊥-elim (≺-irreflexive (≺-transitive x y))

≺-antisymmetric : e ≺ e′ → e′ ≺ e → e ≡ e′
≺-antisymmetric x y = ⊥-elim (≺-irreflexive (≺-transitive x y))
