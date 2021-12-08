------------------------------------------------------------------------
-- Defines the execution of a distributed system as a transition system.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)

module Execution (n : ℕ) where

open import Data.Fin using (Fin; _≟_)
open import Data.List using (List)
open import Data.List.NonEmpty using (List⁺; _∷_; head; tail; [_]; _∷⁺_; toList)
open import Data.List.Membership.Propositional renaming (_∈_ to _∈′_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Product using (∃; _,_; ∃-syntax; -,_)
open import Event n
open import Function using (_∘_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)

-- The state of a ditributed system is a map from process id to its history.
State : Set
State = (p : Pid) → List⁺ (Event p)

s₀ : State
s₀ _ = [ init ]

update : State → Pid → (∀ {p} → Event p → Event p) → State
update s p f p′ with p ≟ p′
... | yes _ = let e = head (s p′) in f e ∷⁺ s p′
... | no  _ = s p′

infix 4 _∈_

_∈_ : ∀ {A : Set} → A → List⁺ A → Set
x ∈ xs = x ∈′ (toList xs)

infix 4 _—⟶_

data _—⟶_ : State → State → Set where
  send : ∀ {s} p →
         s —⟶ update s p send
  recv : ∀ {s} p p′ e →
         p ≢ p′ →
         ∃[ e′ ] e ≡ send e′ →
         e ∈ s p′ →
         s —⟶ update s p (recv e)

infix 2 _—⟶*_

data _—⟶*_ : State → State → Set where
  lift : ∀ {s s′} → s —⟶ s′ → s —⟶* s′
  refl : ∀ {s} → s —⟶* s
  tran : ∀ {s s′ s″} → s —⟶* s′ → s′ —⟶* s″ → s —⟶* s″

module —⟶-Reasoning where

  infix  1 begin_
  infixr 2 _—⟶⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {s s′} → s —⟶ s′ → s —⟶ s′
  begin_ x = x

  _—⟶⟨_⟩_ : ∀ s {s′ s″} → s —⟶ s′ → s′ —⟶* s″ → s —⟶* s″
  _—⟶⟨_⟩_ _ = tran ∘ lift

  _∎ : ∀ s → s —⟶* s
  _∎ _ = refl


reachable : State → Set
reachable = s₀ —⟶*_

-- Induction principle for reachable states.
induction : ∀ (P : State → Set) →
            P s₀ →
            (∀ s s′ → P s → s —⟶ s′ → P s′) →
            ∀ {s} → reachable s → P s
induction P P₀ Pstep x = Pstep→Psteps Pstep _ _ P₀ x
  where
  Pstep→Psteps : (∀ s s′ → P s → s —⟶  s′ → P s′) →
                 ∀ s s′ → P s → s —⟶* s′ → P s′
  Pstep→Psteps Pstep _ _ Ps (lift a)   = Pstep _ _ Ps a
  Pstep→Psteps Pstep _ _ Ps refl       = Ps
  Pstep→Psteps Pstep _ _ Ps (tran a b) = Pstep→Psteps Pstep _ _ (Pstep→Psteps Pstep _ _ Ps a) b

-- Induction principle for reachable states with a generalized induction hypothesis.
induction⁺ : ∀ (P Q : State → Set) →
            Q s₀ →
            (∀ s s′ → Q s → s —⟶ s′ → Q s′) →
            (∀ s → Q s → P s) →
            ∀ {s} → reachable s → P s
induction⁺ P Q Q₀ Qstep Q→P = (Q→P _) ∘ induction Q Q₀ Qstep

-- Induction principle for reachable executions.
induction⋆ : ∀ (P : ∀ s → reachable s → Set) →
             P s₀ refl →
             (∀ s s′ x x′ → P s x → s —⟶ s′ → P s′ x′) →
             (∀ s x x′ → P s x ≡ P s x′) →
             ∀ s (x : reachable s) → P s x
induction⋆ P P₀ Pstep P≡ s x = Pstep→Psteps Pstep _ _ _ _ P₀ x
  where
  Pstep→Psteps : (∀ s s′ x x′ → P s x → s —⟶ s′ → P s′ x′) →
                 ∀ s s′ x x′ → P s x → s —⟶* s′ → P s′ x′
  Pstep→Psteps Pstep _ _ _ _  Px (lift a) = Pstep _ _ _ _ Px a
  Pstep→Psteps Pstep _ _ x x′ Px refl rewrite P≡ _ x x′ = Px
  Pstep→Psteps Pstep _ _ x _  Px (tran a b) = Pstep→Psteps Pstep _ _ (tran x a) _ (Pstep→Psteps Pstep _ _ _ _ Px a) b

-- Receives are well-formed, i.e., the last event of the sending process is a send event.
wf-recv : ∀ {s} → reachable s →
          ∀ p p′ (e : Event p) (e′ : Event p′) →
          recv e′ e ∈ s p →
          ∃[ e″ ] e′ ≡ send e″
wf-recv = induction P P₀ Pstep
  where
  P : State → Set
  P s = ∀ p p′ e e′ → recv e′ e ∈ s p → ∃[ e″ ] e′ ≡ send e″

  P₀ : P s₀
  P₀ p p′ e e′ (here ())
  P₀ p p′ e e′ (there ())

  Pstep : ∀ s s′ → P s → s —⟶ s′ → P s′
  Pstep _ _ Ps (send p) p′ _ _ _ a         with p ≟ p′
  Pstep _ _ Ps (send p) p′ _ _ _ (here ()) | yes _
  Pstep _ _ Ps (send p) p′ _ _ _ (there a) | yes _ = Ps _ _ _ _ a
  Pstep _ _ Ps (send p) p′ _ _ _ a         | no  _ = Ps _ _ _ _ a
  Pstep _ _ Ps (recv p _ _ _ _ _) p′ _ _ _ a           with p ≟ p′
  Pstep _ _ Ps (recv p _ _ _ t _) p′ _ _ _ (here refl) | yes _ = t
  Pstep _ _ Ps (recv p _ _ _ _ _) p′ _ _ _ (there a)   | yes _ = Ps _ _ _ _ a
  Pstep _ _ Ps (recv p _ _ _ _ _) p′ _ _ _ a           | no  _ = Ps _ _ _ _ a
