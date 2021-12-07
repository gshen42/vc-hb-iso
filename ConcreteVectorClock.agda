------------------------------------------------------------------------
--
------------------------------------------------------------------------

open import Data.Nat as ℕ using (ℕ; suc; _⊔_)

module ConcreteVectorClock (n : ℕ) where

import AbstractVectorClock as AbstractVectorClock
open import Data.Fin using (Fin)
import Data.Fin.Properties as Finₚ
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Vec as Vec
open import Data.Vec.Relation.Binary.Pointwise.Inductive using (Pointwise)
open import Function using (const)

Pid = Fin n

private
  variable
    p q : Pid

record VCᶜ (_ : Pid) : Set where
  constructor wrap
  field       unwrap : Vec ℕ n

open VCᶜ

_<ᶜ_ : VCᶜ p → VCᶜ q → Set
(wrap x) <ᶜ (wrap y) = Pointwise ℕ._≤_ x y × ∃[ i ] lookup x i ℕ.< lookup y i

initᶜ : VCᶜ p
unwrap (initᶜ {p}) = updateAt p (const 1) (replicate 0)

tickᶜ : VCᶜ p → VCᶜ p
unwrap (tickᶜ {p} (wrap x)) = updateAt p suc x

combineᶜ : VCᶜ q → VCᶜ p → VCᶜ p
unwrap (combineᶜ (wrap x) (wrap y)) = zipWith _⊔_ x y

mergeᶜ : VCᶜ q → VCᶜ p → VCᶜ p
mergeᶜ x y = tickᶜ (combineᶜ x y)

PidSetoid = Finₚ.≡-decSetoid n
open AbstractVectorClock PidSetoid

private
  variable
    vc  : VC p
    vc′ : VC q

vc→vcᶜ : VC p → VCᶜ p
vc→vcᶜ init        = initᶜ
vc→vcᶜ (tick x)    = tickᶜ (vc→vcᶜ x)
vc→vcᶜ (merge x y) = mergeᶜ (vc→vcᶜ x) (vc→vcᶜ y)

<→<ᶜ : vc < vc′ → (vc→vcᶜ vc) <ᶜ (vc→vcᶜ vc′)
<→<ᶜ vc<tick[vc]      = {!!}
<→<ᶜ vc<merge[vc,vc′] = {!!}
<→<ᶜ vc<merge[vc′,vc] = {!!}
<→<ᶜ (transitive x y) = {!!}

<ᶜ→< : ∀ p q (vc : VC p) (vc′ : VC q) → (vc→vcᶜ vc) <ᶜ (vc→vcᶜ vc′) → vc < vc′
<ᶜ→< p q init init t        = {!!}
<ᶜ→< p q init (tick x) t    = {!!}
<ᶜ→< p q init (merge x y) t = {!!}
<ᶜ→< p q (AbstractVectorClock.tick vc) vc′ x = {!!}
<ᶜ→< p q (AbstractVectorClock.merge vc vc₁) vc′ x = {!!}
