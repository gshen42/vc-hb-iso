------------------------------------------------------------------------
-- Defines `Event` and happens-before relation `_⊏_`, proves `_⊏_` is a
-- strict partial order.
------------------------------------------------------------------------

open import Data.Nat

module Event (n : ℕ) (Msg : Set) where

open import Data.Fin using (Fin)
open import Data.Nat.Properties
open import Relation.Nullary using (¬_)

Pid = Fin n

private
  variable
    p p′ p″ : Pid
    m       : Msg

data Event : Pid → Set where
  init : Event p
  send : Msg      → Event p → Event p
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

------------------------------------------------------------------------
-- Indexed equality and inequality of events
-- Note that we shouldn't use `_≡_` because `Event` is indexed

infix 4 _≡ᵉ_ _≢ᵉ_

data _≡ᵉ_ : Event p → Event p′ → Set where
  refl : e ≡ᵉ e

_≢ᵉ_ : Event p → Event p′ → Set
e ≢ᵉ e′ = ¬ (e ≡ᵉ e′)

------------------------------------------------------------------------
-- `_⊏_` is a strict partial order.

size : Event p → ℕ
size init        = zero
size (send _ e)  = suc (size e)
size (recv e e′) = suc (size e + size e′)

⊏-mono : e ⊏ e′ → size e < size e′
⊏-mono processOrder₁ = s≤s ≤-refl
⊏-mono processOrder₂ = s≤s (≤-stepsˡ _ ≤-refl)
⊏-mono send⊏recv     = s≤s (≤-stepsʳ _ ≤-refl)
⊏-mono (trans x y)   = ≤-trans (⊏-mono x) (<⇒≤ (⊏-mono y))

⊏-irrefl : ¬ e ⊏ e
⊏-irrefl x = 1+n≰n (⊏-mono x)

⊏-trans : e ⊏ e′ → e′ ⊏ e″ → e ⊏ e″
⊏-trans = trans

⊏-asym : e ⊏ e′ → ¬ e′ ⊏ e
⊏-asym x y with () ← ⊏-irrefl (⊏-trans x y)

⊏-antisym : e ⊏ e′ → e′ ⊏ e → e ≡ᵉ e′
⊏-antisym x y with () ← ⊏-irrefl (⊏-trans x y)
