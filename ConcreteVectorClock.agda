------------------------------------------------------------------------
--
------------------------------------------------------------------------

open import Data.Nat as ℕ hiding (_≟_)

module ConcreteVectorClock (n : ℕ) where

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
