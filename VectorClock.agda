------------------------------------------------------------------------
--
------------------------------------------------------------------------

open import Data.Nat as ℕ

module VectorClock (n : ℕ) where

open import Data.Product using (_×_; ∃-syntax)
open import Data.Vec as Vec
open import Event n
open import Function using (const)

VC : Set
VC = Vec ℕ n

_<ᶜ_ : VC → VC → Set
x <ᶜ y = ∀  i → lookup x i ≤ lookup y i ×
         ∃[ j ] lookup x j < lookup y j

initᶜ : Pid → VC
initᶜ p = updateAt p (const 1) (replicate 0)

tickᶜ : Pid → VC → VC
tickᶜ p x = updateAt p suc x

combineᶜ : VC → VC → VC
combineᶜ x y = zipWith _⊔_ x y

mergeᶜ : Pid → VC → VC → VC
mergeᶜ p x y = tickᶜ p (combineᶜ x y)
