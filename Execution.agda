------------------------------------------------------------------------
-- Defines the execution of a distributed system as a transition system.
------------------------------------------------------------------------

open import Level using (0ℓ)
open import Relation.Binary using (DecSetoid)

module Execution (PidSetoid : DecSetoid 0ℓ 0ℓ) where

open DecSetoid PidSetoid using (_≟_) renaming (Carrier to Pid)

open import Data.Product using (∃; _,_; ∃-syntax; -,_)
open import Event Pid
open import Function using (_∘₂_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

-- The state of a ditributed system is a map from process id to its history.
State : Set
State = (p : Pid) → History p

s₀ : State
s₀ p = init

update : State → Pid → (∀ {p} → History p → History p) → State
update s p f p′ with p ≟ p′
... | yes _ = f (s p′)
... | no  _ = s p′

private
  variable
    s s′ s″ : State

data _==>_ : State → State → Set where
  send : ∀ p →
         s ==> update s p send
  recv : ∀ p p′ (e : Event p′) →
         p ≢ p′ →
         ∃[ e′ ] e ≡ send e′ →
         e ∈ s p′ →
         s ==> update s p (recv e)

data _==>*_ : State → State → Set where
  lift  : s ==> s′ → s ==>* s′
  refl  : s ==>* s
  trans : s ==>* s′ → s′ ==>* s″ → s ==>* s″

reachable : State → Set
reachable = s₀ ==>*_

-- Induction principle for `reachable`.
induction : ∀ (P : State → Set) →
            P s₀ →
            (∀ s s′ → P s → s ==> s′ → P s′) →
            ∀ s → reachable s → P s
induction _ P₀ Pstep _ (lift x)    = Pstep _ _ P₀ x
induction _ P₀ Pstep _ refl        = P₀
induction _ P₀ Pstep _ (trans x y) = Pstep→Psteps _ Pstep _ _ P₀ (trans x y)
  where
  Pstep→Psteps : ∀ (P : State → Set) →
               (∀ s s′ → P s → s ==>  s′ → P s′) →
               (∀ s s′ → P s → s ==>* s′ → P s′)
  Pstep→Psteps _ Pstep _ _ Ps (lift x)    = Pstep _ _ Ps x
  Pstep→Psteps _ Pstep _ _ Ps refl        = Ps
  Pstep→Psteps _ Pstep _ _ Ps (trans x y) = Pstep→Psteps _ Pstep _ _ (Pstep→Psteps _ Pstep _ _ Ps x) y

-- Induction principle for `reachable` with a generalized induction hypothesis.
induction⁺ : ∀ (P Q : State → Set) →
            Q s₀ →
            (∀ s s′ → Q s → s ==> s′ → Q s′) →
            (∀ s → Q s → P s) →
            ∀ s → reachable s → P s
induction⁺ P Q Q₀ Qstep Q→P = (Q→P _) ∘₂ induction Q Q₀ Qstep

-- Receives are well-formed, i.e., the last event of the sending process is a send event.
wf-recv : ∀ s → reachable s →
          ∀ p q (e : Event p) (e′ : Event q) →
          recv e′ e ∈ s p →
          ∃[ e″ ] e′ ≡ send e″
wf-recv = induction P P₀ Pstep
  where
  P : State → Set
  P s = ∀ p q e e′ → recv e′ e ∈ s p → ∃[ e″ ] e′ ≡ send e″

  P₀ : P s₀
  P₀ p q e e′ ()

  Pstep : ∀ s s′ → P s → s ==> s′ → P s′
  Pstep _ _ Ps (send p) q _ _ _ x          with p ≟ q
  Pstep _ _ Ps (send p) q _ _ _ (there₁ x) | yes _ = Ps _ _ _ _ x
  Pstep _ _ Ps (send p) q _ _ _ x          | no  _ = Ps _ _ _ _ x
  Pstep _ _ Ps (recv p _ _ _ _ _) q _ _ _ x          with p ≟ q
  Pstep _ _ Ps (recv p _ _ _ y _) q _ _ _ here       | yes _ = y
  Pstep _ _ Ps (recv p _ _ _ _ _) q _ _ _ (there₂ x) | yes _ = Ps _ _ _ _ x
  Pstep _ _ Ps (recv p _ _ _ _ _) q _ _ _ x          | no  _ = Ps _ _ _ _ x
