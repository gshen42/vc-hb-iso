------------------------------------------------------------------------
-- Defines the execution of a distributed system as a transition system.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)

module Execution (n : ℕ) (Msg : Set) where

open import Data.Fin using (Fin; _≟_)
open import Data.List using (List)
open import Data.List.NonEmpty using (List⁺; _∷_; head; tail; [_]; _∷⁺_; toList)
open import Data.List.Membership.Propositional renaming (_∈_ to _∈′_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Product using (∃; _,_; ∃-syntax; -,_)
open import Event n Msg
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)
open import Relation.Nullary using (yes; no)

-- The state of a process is a non-empty list of events that happened on
-- it in order from most recent to oldest.
Process : Pid → Set
Process p = List⁺ (Event p)

-- The state of a ditributed system is a map from process id to process
-- state.
State : Set
State = (p : Pid) → Process p

s₀ : State
s₀ _ = [ init ]

update : State → Pid → (∀ {p} → Event p → Event p) → State
update s p f p′ with p ≟ p′
... | yes _ = f (head (s p′)) ∷⁺ s p′
... | no  _ = s p′

_∈_ : ∀ {A : Set} → A → List⁺ A → Set
x ∈ xs = x ∈′ (toList xs)

data _—⟶_ : State → State → Set where
  send : ∀ {s} p m →
         s —⟶ update s p (send m)
  recv : ∀ {s} p p′ e →
         p ≢ p′ →
         ∃[ e′ ] ∃[ m ] e ≡ send m e′ →
         e ∈ s p′ →
         s —⟶ update s p (recv e)

data _—⟶*_ : State → State → Set where
  lift : ∀ {s s′} → s —⟶ s′ → s —⟶* s′
  refl : ∀ {s} → s —⟶* s
  tran : ∀ {s s′ s″} → s —⟶* s′ → s′ —⟶* s″ → s —⟶* s″

reachable : State → Set
reachable = s₀ —⟶*_

-- Induction principle for reachable states.
induction : ∀ (P : State → Set) →
            P s₀ →
            (∀ s s′ → reachable s → P s → s —⟶ s′ → P s′) →
            ∀ {s} → reachable s → P s
induction P P₀ Pstep r = Pstep→Psteps Pstep _ _ refl P₀ r
  where
  Pstep→Psteps : (∀ s s′ → reachable s → P s → s —⟶  s′ → P s′) →
                 ∀ s s′ → reachable s → P s → s —⟶* s′ → P s′
  Pstep→Psteps Pstep _ _ r Ps (lift a)   = Pstep _ _ r Ps a
  Pstep→Psteps Pstep _ _ r Ps refl       = Ps
  Pstep→Psteps Pstep _ _ r Ps (tran a b) = Pstep→Psteps Pstep _ _ (tran r a) (Pstep→Psteps Pstep _ _ r Ps a) b

-- Receives are well-formed, i.e., the last event of the sending process is a send event.
wf-recv : ∀ {s} → reachable s →
          ∀ p p′ (e : Event p) (e′ : Event p′) →
          recv e′ e ∈ s p →
          ∃[ e″ ] ∃[ m ] e′ ≡ send m e″
wf-recv = induction P P₀ Pstep
  where
  P : State → Set
  P s = ∀ p p′ e e′ → recv e′ e ∈ s p → ∃[ e″ ] ∃[ m ] e′ ≡ send m e″

  P₀ : P s₀
  P₀ p p′ e e′ (here ())
  P₀ p p′ e e′ (there ())

  Pstep : ∀ s s′ → reachable s → P s → s —⟶ s′ → P s′
  Pstep _ _ _ Ps (send p _) p′ _ _ _ a         with p ≟ p′
  Pstep _ _ _ Ps (send p _) p′ _ _ _ (here ()) | yes _
  Pstep _ _ _ Ps (send p _) p′ _ _ _ (there a) | yes _ = Ps _ _ _ _ a
  Pstep _ _ _ Ps (send p _) p′ _ _ _ a         | no  _ = Ps _ _ _ _ a
  Pstep _ _ _ Ps (recv p _ _ _ _ _) p′ _ _ _ a           with p ≟ p′
  Pstep _ _ _ Ps (recv p _ _ _ t _) p′ _ _ _ (here refl) | yes _ = t
  Pstep _ _ _ Ps (recv p _ _ _ _ _) p′ _ _ _ (there a)   | yes _ = Ps _ _ _ _ a
  Pstep _ _ _ Ps (recv p _ _ _ _ _) p′ _ _ _ a           | no  _ = Ps _ _ _ _ a
