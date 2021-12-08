------------------------------------------------------------------------
--
------------------------------------------------------------------------

open import Data.Nat as ℕ hiding (_≟_)

module VectorClock (n : ℕ) where

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; _≟_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
import Data.Nat.Properties as ℕₚ
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Vec as Vec
open import Event n
open import Execution n
open import Function using (const)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)

VC : Set
VC = Vec ℕ n

_<ᶜ_ : VC → VC → Set
x <ᶜ y = (∀ i → lookup x i ≤ lookup y i) × (∃[ j ] lookup x j < lookup y j)

initᶜ : Pid → VC
initᶜ p = updateAt p (const 1) (replicate 0)

tickᶜ : Pid → VC → VC
tickᶜ p x = updateAt p suc x

combineᶜ : VC → VC → VC
combineᶜ x y = zipWith _⊔_ x y

mergeᶜ : Pid → VC → VC → VC
mergeᶜ p x y = tickᶜ p (combineᶜ x y)

vc : ∀ {s} → reachable s →
     ∀ p {e} → e ∈ s p → VC
vc = induction P P₀ Pstep
  where
  P : State → Set
  P s = ∀ p {e} → e ∈ s p → VC

  P₀ : ∀ p {e} → e ∈ s₀ p → VC
  P₀ p (here x) = initᶜ p

  Pstep : ∀ s s′ →
          (∀ p {e} → e ∈ s p → VC) →
          s —⟶ s′ →
          ∀ p {e} → e ∈ s′ p → VC
  Pstep _ _ Ps (send p) q x           with p ≟ q
  Pstep _ _ Ps (send p) q (here refl) | yes _ = tickᶜ p (Ps p (here refl))
  Pstep _ _ Ps (send p) q (there x)   | yes _ = Ps _ x
  Pstep _ _ Ps (send p) q x           | no  _ = Ps _ x
  Pstep _ _ Ps (recv p _ _ _ _ _) q x           with p ≟ q
  Pstep _ _ Ps (recv p _ _ _ _ y) q (here refl) | yes _ = mergeᶜ p (Ps _ y) (Ps p (here refl))
  Pstep _ _ Ps (recv p _ _ _ _ _) q (there x)   | yes _ = Ps _ x
  Pstep _ _ Ps (recv p _ _ _ _ _) q x           | no  _ = Ps _ x

<→≺ : ∀ {s} (r : reachable s) →
      ∀ p p′ e e′ → (x : e ∈ s p) → (y : e′ ∈ s p′) →
      vc r _ x <ᶜ vc r _ y →
      e ≺ e′
<→≺ = {!!}
