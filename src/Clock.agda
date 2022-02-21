------------------------------------------------------------------------
-- Generic clock interface.
------------------------------------------------------------------------

module Clock  where

open import Postulates
open import Event
open import HappensBefore
open import Data.Empty using (⊥-elim)
open import Data.Fin as Fin using (_≟_)
open import Data.Maybe using (Maybe)
open import Data.Nat as Nat
open import Data.Nat.Properties as ℕₚ
open import Data.Product using (_×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘′_)
open import Relation.Binary using (Tri; tri<; tri≈; tri>)
open import Relation.Binary.HeterogeneousEquality using (_≇_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)
open import Relation.Nullary using (¬_; yes; no)

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
    _≈_      : C → C → Set
    ≈-refl   : ∀ {c} → c ≈ c
--  ≈-trans  : ∀ {c c′ c″} → c ≈ c′ → c′ ≈ c″ → c ≈ c″
--  ≈-sym    : ∀ {c c′} → c ≈ c′ → c′ ≈ c
    _≺_      : C → C → Set
    ≺-irrefl : ∀ {c} → ¬ c ≺ c
    ≺-trans  : ∀ {c c′ c″} → c ≺ c′ → c′ ≺ c″ → c ≺ c″


record ⊏-Preserving (clock : Clock) : Set where
  open Clock clock

  field
    ⊏-preserving-rule₁ : C[ e ] ≺ C[ send m e ]
    ⊏-preserving-rule₂ : C[ e′ ] ≺ C[ recv e e′ ]
    ⊏-preserving-rule₃ : C[ e ] ≺ C[ recv e e′ ]

  ⊏-preserving : e ⊏ e′ → C[ e ] ≺ C[ e′ ]
  ⊏-preserving processOrder₁ = ⊏-preserving-rule₁
  ⊏-preserving processOrder₂ = ⊏-preserving-rule₂
  ⊏-preserving send⊏recv     = ⊏-preserving-rule₃
  ⊏-preserving (trans x y)   = ≺-trans (⊏-preserving x) (⊏-preserving y)

  minimal₁ : (∀ {pid} {pid′} {eid} {eid′} (e : Event pid eid) (e′ : Event pid′ eid′) → e ⊏ e′ → C[ e ] ≺ C[ e′ ]) → (C[ e ] ≺ C[ send m e ])
  minimal₁ x = x _ _ processOrder₁
  

record ⊏-Determining (clock : Clock) : Set where
  open Clock clock

  field
    ⊏-determining-rule₁ : pid[ e ] ≡ pid[ e′ ] → eid[ e′ ] ≤ eid[ e ] → ¬ C[ e ] ≺ C[ e′ ]
    ⊏-determining-rule₂ : pid[ e ] ≢ pid[ e′ ] → e′ ≡ init → ¬ C[ e ] ≺ C[ e′ ]
    ⊏-determining-rule₃ : pid[ e ] ≢ pid[ e′ ] → ¬ e ⊏ e′ → ¬ C[ e ] ≺ C[ send m e′ ]
    ⊏-determining-rule₄ : pid[ e ] ≢ pid[ e′ ] → ¬ e ⊏ e′ → ¬ e ⊏ e″ → e ≇ e″ → ¬ C[ e ] ≺ C[ recv e″ e′ ]

  ⊏-determining-contra : e ⊏̸ e′ → ¬ C[ e ] ≺ C[ e′ ]
  ⊏-determining-contra (rule₁ x y)     = ⊏-determining-rule₁ x y
  ⊏-determining-contra (rule₂ x y)     = ⊏-determining-rule₂ x y
  ⊏-determining-contra (rule₃ x y)     = ⊏-determining-rule₃ x (⊏̸⇒¬ y) 
  ⊏-determining-contra (rule₄ x y z w) = ⊏-determining-rule₄ x (⊏̸⇒¬ y) (⊏̸⇒¬ z) w 

  ⊏-determining : C[ e ] ≺ C[ e′ ] → e ⊏ e′
  ⊏-determining {e = e} {e′ = e′} x with ⊏-dec {e = e} {e′ = e′}
  ... | inj₁ y = y
  ... | inj₂ y = ⊥-elim (⊏-determining-contra (¬⇒⊏̸ y) x)
  
  minimal₁ : (∀ {pid} {pid′} {eid} {eid′} (e : Event pid eid) (e′ : Event pid′ eid′) →  e ⊏̸ e′ → ¬ C[ e ] ≺ C[ e′ ]) → (pid[ e ] ≡ pid[ e′ ] → eid[ e′ ] ≤ eid[ e ] → ¬ C[ e ] ≺ C[ e′ ])
  minimal₁ x y z = x _ _ (rule₁ y z)

  minimal₂ : (∀ {pid} {pid′} {eid} {eid′} (e : Event pid eid) (e′ : Event pid′ eid′) →  e ⊏̸ e′ → ¬ C[ e ] ≺ C[ e′ ]) → (pid[ e ] ≢ pid[ e′ ] → e′ ≡ init → ¬ C[ e ] ≺ C[ e′ ])
  minimal₂ x y z = x _ _ (rule₂ y  z)

  minimal₃ : (∀ {pid} {pid′} {eid} {eid′} (e : Event pid eid) (e′ : Event pid′ eid′) →  e ⊏̸ e′ → ¬ C[ e ] ≺ C[ e′ ]) → (pid[ e ] ≢ pid[ e′ ] → ¬ e ⊏ e′ → ¬ C[ e ] ≺ C[ send m e′ ])
  minimal₃ x y z = x _ _ (rule₃ y (¬⇒⊏̸ z) )

  minimal₄ : (∀ {pid} {pid′} {eid} {eid′} (e : Event pid eid) (e′ : Event pid′ eid′) →  e ⊏̸ e′ → ¬ C[ e ] ≺ C[ e′ ]) → (pid[ e ] ≢ pid[ e′ ] → ¬ e ⊏ e′ → ¬ e ⊏ e″ → e ≇ e″ → ¬ C[ e ] ≺ C[ recv e″ e′ ])
  minimal₄ x y z w u = x _ _ (rule₄ y (¬⇒⊏̸ z) (¬⇒⊏̸ w) u)


