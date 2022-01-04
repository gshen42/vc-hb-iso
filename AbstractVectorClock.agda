------------------------------------------------------------------------
-- Defines the abstract vector clock `VC` that captures the algebraic
-- properties of the vector clock but without committing to a specific
-- representation.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)

module AbstractVectorClock (n : ℕ) (Msg : Set) where

open import Data.Fin using (_≟_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Maybe using (nothing)
open import Data.Product using (_×_; proj₁; proj₂)
open import Event n Msg
open import Execution n Msg
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)

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

-- event[_] : VC p → Event p
-- event[ init ]      = init
-- event[ tick x ]    = send event[ x ]
-- event[ merge x y ] = recv event[ x ] event[ y ]

⊏↔< : ∀ {s} → reachable s →
      ∀ p p′ e e′ → e ∈ (s p) → e′ ∈ (s p′) →
      (e ⊏ e′ → vc[ e ] < vc[ e′ ]) × (vc[ e ] < vc[ e′ ] → e ⊏ e′)
proj₁ (⊏↔< _ _ _ _ _ _ _) = ⊏→<
  where
  ⊏→< : ∀ {p p′} {e : Event p} {e′ : Event p′}
        → e ⊏ e′ → vc[ e ] < vc[ e′ ]
  ⊏→< processOrder₁ = vc<tick[vc]
  ⊏→< processOrder₂ = vc<merge[vc′,vc]
  ⊏→< send⊏recv     = vc<merge[vc,vc′]
  ⊏→< (trans x y)   = trans (⊏→< x) ((⊏→< y))
proj₂ (⊏↔< a _ _ _ _ b c) = {!!}
