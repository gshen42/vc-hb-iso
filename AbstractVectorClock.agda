------------------------------------------------------------------------
-- Defines the abstract vector clock `VC` that captures the algebraic
-- properties of the vector clock but without committing to a specific
-- representation.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)

module AbstractVectorClock (n : ℕ) (Msg : Set) where

open import Event n Msg
open import Execution n Msg

private
  variable
    p p′ p″ : Pid

data VC : Pid → Set where
  init  : VC p
  tick  : VC p  → VC p
  merge : VC p′ → VC p → VC p

private
  variable
    vc  : VC p
    vc′ : VC p′
    vc″ : VC p″

data _<_ : VC p → VC p′ → Set where
  vc<tick[vc]      : vc < tick vc
  vc<merge[vc,vc′] : vc < merge vc  vc′
  vc<merge[vc′,vc] : vc < merge vc′ vc
  trans            : vc < vc′ → vc′ < vc″ → vc < vc″

vc[_] : Event p → VC p
vc[ init ]      = init
vc[ send _ e ]  = tick vc[ e ]
vc[ recv e′ e ] = merge vc[ e′ ] vc[ e ]

⊏→< : ∀ {s} → reachable s →
      ∀ p p′ e e′ → e ∈ (s p) → e′ ∈ (s p′) →
      e ⊏ e′ → vc[ e ] < vc[ e′ ]
⊏→< _ _ _ _ _ _ _ = foo
  where
  foo : ∀ {e : Event p} {e′ : Event p′} → e ⊏ e′ → vc[ e ] < vc[ e′ ]
  foo processOrder₁ = vc<tick[vc]
  foo processOrder₂ = vc<merge[vc′,vc]
  foo send⊏recv     = vc<merge[vc,vc′]
  foo (trans x y)   = trans (foo x) (foo y)

<→⊏ : ∀ {s} → reachable s →
      ∀ p p′ e e′ → e ∈ (s p) → e′ ∈ (s p′) →
      vc[ e ] < vc[ e′ ] → e ⊏ e′
