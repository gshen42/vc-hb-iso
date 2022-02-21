------------------------------------------------------------------------
-- Generic clock interface.
------------------------------------------------------------------------

module Clock where

open import Postulates
open import Event
open import HappensBefore
open import Data.Empty using (⊥-elim)
open import Data.Nat using (_≤_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.HeterogeneousEquality using (_≇_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contraposition)

private
  variable
    pid pid′ pid″ : ProcessId
    eid eid′ eid″ : LocalEventId
    m  : Message
    e  : Event pid  eid
    e′ : Event pid′ eid′
    e″ : Event pid″ eid″

record Clock : Set₁ where
  field
    C        : Set
    C[_]     : Event pid eid → C
    _≺_      : C → C → Set
    ≺-trans  : ∀ {c c′ c″} → c ≺ c′ → c′ ≺ c″ → c ≺ c″


module _ (clock : Clock) where
  open Clock clock

  ⊏-Preserving : Set
  ⊏-Preserving = ∀ {pid pid′} {eid eid′} {e : Event pid eid} {e′ : Event pid′ eid′} →
                 e ⊏ e′ → C[ e ] ≺ C[ e′ ]

  ⊏-Determining : Set
  ⊏-Determining = ∀ {pid pid′} {eid eid′} {e : Event pid eid} {e′ : Event pid′ eid′} →
                  C[ e ] ≺ C[ e′ ] → e ⊏ e′

  record ⊏-PreservingRules : Set where
    field
      ⊏-preserving-rule₁ : C[ e ] ≺ C[ send m e ]
      ⊏-preserving-rule₂ : C[ e ] ≺ C[ recv e′ e  ]
      ⊏-preserving-rule₃ : C[ e ] ≺ C[ recv e  e′ ]
  open ⊏-PreservingRules

  record ⊏-DeterminingRules : Set where
    field
      ⊏-determining-rule₁ : pid[ e ] ≡ pid[ e′ ] → eid[ e′ ] ≤ eid[ e ] → ¬ C[ e ] ≺ C[ e′ ]
      ⊏-determining-rule₂ : pid[ e ] ≢ pid[ e′ ] → e′ ≡ init → ¬ C[ e ] ≺ C[ e′ ]
      ⊏-determining-rule₃ : pid[ e ] ≢ pid[ e′ ] → ¬ e ⊏ e′ → ¬ C[ e ] ≺ C[ send m e′ ]
      ⊏-determining-rule₄ : pid[ e ] ≢ pid[ e′ ] → ¬ e ⊏ e′ → ¬ e ⊏ e″ → e ≇ e″ → ¬ C[ e ] ≺ C[ recv e″ e′ ]
  open ⊏-DeterminingRules

  ⊏-PreservingRules-sufficient : ⊏-PreservingRules → ⊏-Preserving
  ⊏-PreservingRules-sufficient rules processOrder₁ = ⊏-preserving-rule₁ rules
  ⊏-PreservingRules-sufficient rules processOrder₂ = ⊏-preserving-rule₂ rules
  ⊏-PreservingRules-sufficient rules send⊏recv     = ⊏-preserving-rule₃ rules
  ⊏-PreservingRules-sufficient rules (trans x y)   = ≺-trans (⊏-PreservingRules-sufficient rules x) (⊏-PreservingRules-sufficient rules y)

  ⊏-PreservingRules-necessary : ⊏-Preserving → ⊏-PreservingRules
  ⊏-preserving-rule₁ (⊏-PreservingRules-necessary x) = x processOrder₁
  ⊏-preserving-rule₂ (⊏-PreservingRules-necessary x) = x processOrder₂
  ⊏-preserving-rule₃ (⊏-PreservingRules-necessary x) = x send⊏recv

  ⊏-DetermingRules-sufficient : ⊏-DeterminingRules → ⊏-Determining
  ⊏-DetermingRules-sufficient rules {e = e} {e′ = e′} x with ⊏-dec {e = e} {e′ = e′}
  ... | inj₁ y = y
  ... | inj₂ y = ⊥-elim (contra y x)
    where
    contra : ¬ e ⊏ e′ → ¬ C[ e ] ≺ C[ e′ ]
    contra ¬e⊏e′ = contra-inductive (¬⇒⊏̸ ¬e⊏e′)
      where
      contra-inductive : e ⊏̸ e′ → ¬ C[ e ] ≺ C[ e′ ]
      contra-inductive (⊏̸-eid  x y)     = ⊏-determining-rule₁ rules x y
      contra-inductive (⊏̸-init x y)     = ⊏-determining-rule₂ rules x y
      contra-inductive (⊏̸-send x y)     = ⊏-determining-rule₃ rules x (⊏̸⇒¬ y)
      contra-inductive (⊏̸-recv x y z w) = ⊏-determining-rule₄ rules x (⊏̸⇒¬ y) (⊏̸⇒¬ z) w

  ⊏-DeterminingRules-necessary : ⊏-Determining → ⊏-DeterminingRules
  ⊏-determining-rule₁ (⊏-DeterminingRules-necessary x) y z     = contraposition x (⊏̸⇒¬ (⊏̸-eid y z))
  ⊏-determining-rule₂ (⊏-DeterminingRules-necessary x) y z     = contraposition x (⊏̸⇒¬ (⊏̸-init y z))
  ⊏-determining-rule₃ (⊏-DeterminingRules-necessary x) y z     = contraposition x (⊏̸⇒¬ (⊏̸-send y (¬⇒⊏̸ z)))
  ⊏-determining-rule₄ (⊏-DeterminingRules-necessary x) y z w u = contraposition x (⊏̸⇒¬ (⊏̸-recv y (¬⇒⊏̸ z) (¬⇒⊏̸ w) u))
