------------------------------------------------------------------------
-- Defines the execution of a distributed system as a transition system.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Nullary using (Dec; yes; no)

module Execution (Pid : Set) (_≟_ : (p : Pid) → (q : Pid) → Dec (p ≡ q)) where

open import Data.Product using (∃; _,_; ∃-syntax)
open import Event Pid
open import Function using (_∘₂_)

-- The state of a ditributed system is a map from process id to its history.
State : Set
State = (p : Pid) → History p

state₀ : State
state₀ p = init

update : State → Pid → (∀ {p} → History p → History p) → State
update s p f p′ with p ≟ p′
... | yes _ = f (s p′)
... | no  _ = s p′

data _==>_ : State → State → Set where
  send : ∀ p s →
         s ==> update s p send
  recv : ∀ p p′ (e : Event p′) e′ s →
         p ≢ p′ →
         e ≡ send e′ →
         e ∈ s p′ →
         s ==> update s p (recv e)

private
  variable
    p p′    : Pid
    e       : Event p
    e′      : Event p′
    s s′ s″ : State

data _==>*_ : State → State → Set where
  lift  : s ==> s′ → s ==>* s′
  refl  : s ==>* s
  trans : s ==>* s′ → s′ ==>* s″ → s ==>* s″

reachable : State → Set
reachable = state₀ ==>*_

-- Induction principle for `reachable`.
induction : ∀ (P : State → Set) →
            P state₀ →
            (∀ s s′ → P s → s ==> s′ → P s′) →
            ∀ s → reachable s → P s
induction _ P₀ Pstep _ (lift x)    = Pstep _ _ P₀ x
induction _ P₀ Pstep _ refl        = P₀
induction _ P₀ Pstep _ (trans x y) = helper _ Pstep _ _ P₀ (trans x y)
  where
  helper : ∀ (P : State → Set) →
           (∀ s s′ → P s → s ==>  s′ → P s′) →
           (∀ s s′ → P s → s ==>* s′ → P s′)
  helper _ Pstep _ _ Ps (lift x)    = Pstep _ _ Ps x
  helper _ Pstep _ _ Ps refl        = Ps
  helper _ Pstep _ _ Ps (trans x y) = helper _ Pstep _ _ (helper _ Pstep _ _ Ps x) y

-- Induction principle for `reachable` with a generalized induction hypothesis.
induction⁺ : ∀ (P Q : State → Set) →
            Q state₀ →
            (∀ s s′ → Q s → s ==> s′ → Q s′) →
            (∀ s → Q s → P s) →
            ∀ s → reachable s → P s
induction⁺ P Q Q₀ Qstep Q→P = (Q→P _) ∘₂ induction Q Q₀ Qstep

-- wf-recv : reachable s →
--           recv e e′ ∈ s p →
--           ∃[ e″ ] e ≡ send e″
