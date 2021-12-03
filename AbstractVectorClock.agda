------------------------------------------------------------------------
-- Defines the abstract vector clock `VC` that captures the algebraic
-- properties of the vector clock but without committing to a specific
-- representation.
------------------------------------------------------------------------

open import Level using (0ℓ)
open import Relation.Binary using (DecSetoid)

module AbstractVectorClock (PidSetoid : DecSetoid 0ℓ 0ℓ) where

open DecSetoid PidSetoid using (_≟_) renaming (Carrier to Pid)

open import Data.Product using (_×_; _,_)
open import Event Pid
open import Execution PidSetoid
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

private
  variable
    p p′ p″ q : Pid

data VC : Pid → Set where
  init  : VC p
  tick  : VC p → VC p
  merge : VC q → VC p → VC p

private
  variable
    vc  : VC p
    vc′ : VC p′
    vc″ : VC p″

data _<_ : VC p → VC q → Set where
  vc<tick[vc]      : vc < tick vc
  vc<merge[vc,vc′] : vc < merge vc  vc′
  vc<merge[vc′,vc] : vc < merge vc′ vc
  transitive       : vc < vc′ → vc′ < vc″ → vc < vc″

vc[_] : Event p → VC p
vc[ init ]      = init
vc[ send e ]    = tick vc[ e ]
vc[ recv e′ e ] = merge vc[ e′ ] vc[ e ]

event[_] : VC p → Event p
event[ init ]         = init
event[ tick vc ]      = send event[ vc ]
event[ merge vc′ vc ] = recv event[ vc′ ] event[ vc ]

private
  variable
    e   : Event p
    e′  : Event p′

<↔≺ : ∀ s → reachable s →
      e ∈ s p → e′ ∈ s p′ →
      (e ≺ e′ → vc[ e ] < vc[ e′ ]) × (vc[ e ] < vc[ e′ ] → e ≺ e′)
<↔≺ _ _ _ _ = ≺→< , <→≺
  where
  event∘vc : ∀ (e : Event p) → event[ vc[ e ] ] ≡ e
  event∘vc init = refl
  event∘vc (send e) rewrite event∘vc e = refl
  event∘vc (recv e′ e) rewrite event∘vc e | event∘vc e′ = refl

  ≺→< : e ≺ e′ → vc[ e ] < vc[ e′ ]
  ≺→< processOrder₁ = vc<tick[vc]
  ≺→< processOrder₂ = vc<merge[vc′,vc]
  ≺→< send≺recv     = vc<merge[vc,vc′]
  ≺→< (trans x y)   = transitive (≺→< x) (≺→< y)

  foo : vc < vc′ → event[ vc ] ≺ event[ vc′ ]
  foo vc<tick[vc]      = processOrder₁
  foo vc<merge[vc,vc′] = send≺recv
  foo vc<merge[vc′,vc] = processOrder₂
  foo (transitive x y) = trans (foo x) (foo y)

  <→≺ : vc[ e ] < vc[ e′ ] → e ≺ e′
  <→≺ {e = e} {e′ = e′} x = subst (_≺ e′) (event∘vc e) (subst (event[ vc[ e ] ] ≺_) (event∘vc e′) (foo x))
