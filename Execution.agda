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
open import Data.Sum using (_⊎_; inj₁; inj₂)
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
  recv : ∀ {s} p p′ {e} →
         p ≢ p′ →
         e ∈ s p′ →
         ∃[ m ] ∃[ e′ ] e ≡ send m e′ →
         s —⟶ update s p (recv e)

data _—⟶*_ : State → State → Set where
  lift  : ∀ {s s′} → s —⟶ s′ → s —⟶* s′
  refl  : ∀ {s} → s —⟶* s
  trans : ∀ {s s′ s″} → s —⟶* s′ → s′ —⟶* s″ → s —⟶* s″

reachable : State → Set
reachable = s₀ —⟶*_

-- Induction principle for reachable states.
induction : ∀ (P : State → Set) →
            P s₀ →
            (∀ {s s′} → reachable s → P s → s —⟶ s′ → P s′) →
            ∀ {s} → reachable s → P s
induction P P₀ Pstep r = Pstep→Psteps Pstep refl P₀ r
  where
  Pstep→Psteps : (∀ {s s′} → reachable s → P s → s —⟶  s′ → P s′) →
                 ∀ {s s′} → reachable s → P s → s —⟶* s′ → P s′
  Pstep→Psteps Pstep r Ps (lift a)    = Pstep r Ps a
  Pstep→Psteps Pstep r Ps refl        = Ps
  Pstep→Psteps Pstep r Ps (trans a b) = Pstep→Psteps Pstep (trans r a) (Pstep→Psteps Pstep r Ps a) b

-- Receives are well-formed, i.e., the last event of the sending process is a send event.
wf-recv : ∀ {s} → reachable s →
          ∀ p p′ (e : Event p) (e′ : Event p′) →
          recv e′ e ∈ s p →
          ∃[ m ] ∃[ e″ ] e′ ≡ send m e″
wf-recv = induction P P₀ Pstep
  where
  P : State → Set
  P s = ∀ p p′ e e′ → recv e′ e ∈ s p → ∃[ m ] ∃[ e″ ] e′ ≡ send m e″

  P₀ : P s₀
  P₀ p p′ e e′ (here ())
  P₀ p p′ e e′ (there ())

  Pstep : ∀ {s s′} → reachable s → P s → s —⟶ s′ → P s′
  Pstep _ Ps (send p _) p′ _ _ _ a         with p ≟ p′
  Pstep _ Ps (send p _) p′ _ _ _ (here ()) | yes _
  Pstep _ Ps (send p _) p′ _ _ _ (there a) | yes _ = Ps _ _ _ _ a
  Pstep _ Ps (send p _) p′ _ _ _ a         | no  _ = Ps _ _ _ _ a
  Pstep _ Ps (recv p _ _ _ _) p′ _ _ _ a           with p ≟ p′
  Pstep _ Ps (recv p _ _ _ t) p′ _ _ _ (here refl) | yes _ = t
  Pstep _ Ps (recv p _ _ _ _) p′ _ _ _ (there a)   | yes _ = Ps _ _ _ _ a
  Pstep _ Ps (recv p _ _ _ _) p′ _ _ _ a           | no  _ = Ps _ _ _ _ a

e⊏head⊎e≡head : ∀ {s} → reachable s →
                ∀ p e → e ∈ (s p) →
                e ⊏ head (s p) ⊎ e ≡ head (s p)
e⊏head⊎e≡head = induction P P₀ Pstep
  where
  P : State → Set
  P s = ∀ p e → e ∈ (s p) →
        e ⊏ head (s p) ⊎ e ≡ head (s p)

  P₀ : P s₀
  P₀ _ _ (here refl) = inj₂ refl

  Pstep : ∀ {s s′} → reachable s → P s → s —⟶ s′ → P s′
  Pstep _ Ps (send p _) q _ _           with p ≟ q
  Pstep _ Ps (send p _) q _ (here refl) | yes _ = inj₂ refl
  Pstep _ Ps (send p _) q _ (there x)   | yes _ with Ps _ _ x
  ...                                           | inj₁ a    = inj₁ (trans a processOrder₁)
  ...                                           | inj₂ refl = inj₁ processOrder₁
  Pstep _ Ps (send p _) q _ x           | no  _ = Ps _ _ x
  Pstep _ Ps (recv p _ _ _ _) q _ _           with p ≟ q
  Pstep _ Ps (recv p _ _ _ _) q _ (here refl) | yes _ = inj₂ refl
  Pstep _ Ps (recv p _ _ _ _) q _ (there x)   | yes _ with Ps _ _ x
  ...                                                 | inj₁ a    = inj₁ (trans a processOrder₂)
  ...                                                 | inj₂ refl = inj₁ processOrder₂
  Pstep _ Ps (recv p _ _ _ _) q _ x           | no  _ = Ps _ _ x

strictTotalOrder : ∀ {s} → reachable s →
                   ∀ p e e′ → e ∈ (s p) → e′ ∈ (s p) →
                   e ⊏ e′ ⊎ e′ ⊏ e ⊎ e ≡ e′
strictTotalOrder = induction P P₀ Pstep
  where
  P : State → Set
  P s = ∀ p e e′ → e ∈ (s p) → e′ ∈ (s p) →
        e ⊏ e′ ⊎ e′ ⊏ e ⊎ e ≡ e′

  P₀ : P s₀
  P₀ _ _ _ (here refl) (here refl) = inj₂ (inj₂ refl)

  Pstep : ∀ {s s′} → reachable s → P s → s —⟶ s′ → P s′
  Pstep _ Ps (send p _) p′ _ _ _           _           with p ≟ p′
  Pstep _ Ps (send p _) p′ _ _ (here refl) (here refl) | yes _ = inj₂ (inj₂ refl)
  Pstep r Ps (send p _) p′ _ _ (here refl) (there y)   | yes _ with e⊏head⊎e≡head r _ _ y
  ...                                                          | inj₁ a    = inj₂ (inj₁ (trans a processOrder₁))
  ...                                                          | inj₂ refl = inj₂ (inj₁ processOrder₁)
  Pstep r Ps (send p _) p′ _ _ (there x)   (here refl) | yes _ with e⊏head⊎e≡head r _ _ x
  ...                                                          | inj₁ a    = inj₁ (trans a processOrder₁)
  ...                                                          | inj₂ refl = inj₁ processOrder₁
  Pstep _ Ps (send p _) p′ _ _ (there x)   (there y)   | yes _ = Ps _ _ _ x y
  Pstep _ Ps (send p _) p′ _ _ x           y           | no  _ = Ps _ _ _ x y
  Pstep _ Ps (recv p _ _ _ _) p′ _ _ _           _           with p ≟ p′
  Pstep _ Ps (recv p _ _ _ _) p′ _ _ (here refl) (here refl) | yes _ = inj₂ (inj₂ refl)
  Pstep r Ps (recv p _ _ _ _) p′ _ _ (here refl) (there y)   | yes _ with e⊏head⊎e≡head r _ _ y
  ...                                                                | inj₁ a    = inj₂ (inj₁ (trans a processOrder₂))
  ...                                                                | inj₂ refl = inj₂ (inj₁ processOrder₂)
  Pstep r Ps (recv p _ _ _ _) p′ _ _ (there x)   (here refl) | yes _ with e⊏head⊎e≡head r _ _ x
  ...                                                                | inj₁ a    = inj₁ (trans a processOrder₂)
  ...                                                                | inj₂ refl = inj₁ processOrder₂
  Pstep _ Ps (recv p _ _ _ _) p′ _ _ (there x)   (there y)   | yes _ = Ps _ _ _ x y
  Pstep _ Ps (recv p _ _ _ _) p′ _ _ x           y           | no  _ = Ps _ _ _ x y

causal-delivery : State → Set
causal-delivery s = ∀ p₁ p₂ p (e₁ : Event p₁) (e₂ : Event p₂) e₁′ e₂′ →
                    recv e₁ e₁′ ∈ (s p) →
                    recv e₂ e₂′ ∈ (s p) →
                    e₁ ⊏ e₂ →
                    recv e₁ e₁′ ⊏ recv e₂ e₂′
