------------------------------------------------------------------------
-- Defines the execution of CBCAST as a transition system.
------------------------------------------------------------------------

open import Data.Nat using (ℕ; _+_; _≤_)

module CBCAST (n : ℕ) (Msg : Set) where

open import Data.Fin using (Fin; _≟_)
open import Data.List.NonEmpty using (List⁺; [_]; head; _∷⁺_)
open import Data.Product using (_×_; ∃; _,_; ∃-syntax; -,_)
import Event as Event
import Execution as Execution
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)
open import Relation.Nullary using (yes; no)
open import VectorClock n

record Msgᶜ : Set where
  field
    msg    : Msg
    sender : Fin n
    vc     : VC


open Event n Msgᶜ
open Execution n Msgᶜ

record Processᶜ (p : Fin n) : Set where
  field
    history : List⁺ (Event p)
    vc      : VC


Stateᶜ : Set
Stateᶜ = (p : Pid) → Processᶜ p

s₀ᶜ : Stateᶜ
s₀ᶜ _ = record { history = [ init ] ; vc = vc₀ }

updateᶜ : Stateᶜ → Fin n → (∀ {p} → Event p → Event p) → (VC → VC) → Stateᶜ
updateᶜ s p f g p′ with p ≟ p′
... | yes _ = let record { history = h′ ; vc = v′} = s p′
              in record { history = f (head h′) ∷⁺ h′ ; vc = g v′}
... | no  _ = s p′

deliverable : ∀ {p} → Msgᶜ → Processᶜ p → Set
deliverable (record { sender = sender ; vc = vcₘ }) (record { vc = vcₚ }) =
  ∀ k → ((k ≡ sender) → _[_] vcₘ k ≡ _[_] vcₚ k + 1) ×
        ((k ≢ sender) → _[_] vcₘ k ≤ _[_] vcₚ k)

data _—⟶ᶜ_ : Stateᶜ → Stateᶜ → Set where
  send : ∀ {s} p m →
         s —⟶ᶜ updateᶜ s p (send record { msg = m; sender = p; vc = tick p (Processᶜ.vc (s p)) }) (tick p)
  recv : ∀ {s} p p′ m {e} →
         p ≢ p′ →
         e ∈ Processᶜ.history (s p′) →
         ∃[ e′ ] e ≡ send m e′ →
         deliverable m (s p) →
         s —⟶ᶜ updateᶜ s p (recv e) (combine (Msgᶜ.vc m))

data _—⟶*ᶜ_ : Stateᶜ → Stateᶜ → Set where
  lift  : ∀ {s s′} → s —⟶ᶜ s′ → s —⟶*ᶜ s′
  refl  : ∀ {s} → s —⟶*ᶜ s
  trans : ∀ {s s′ s″} → s —⟶*ᶜ s′ → s′ —⟶*ᶜ s″ → s —⟶*ᶜ s″

reachableᶜ : Stateᶜ → Set
reachableᶜ = s₀ᶜ —⟶*ᶜ_

inductionᶜ : ∀ (P : Stateᶜ → Set) →
             P s₀ᶜ →
             (∀ {s s′} → reachableᶜ s → P s → s —⟶ᶜ s′ → P s′) →
             ∀ {s} → reachableᶜ s → P s

↓ᶜ : Stateᶜ → State

reachableᶜ⇒reachable : ∀ sᶜ → reachableᶜ sᶜ → reachable (↓ᶜ sᶜ)

causal-deliveryᶜ : ∀ sᶜ → reachableᶜ sᶜ →
                   causal-delivery (↓ᶜ sᶜ)
