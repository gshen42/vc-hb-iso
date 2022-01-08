open import Data.Nat as ℕ using (ℕ)

module VectorClock (n : ℕ) where

open import Data.Fin as Fin using (Fin)
open import Data.Vec as Vec using (Vec)

VC : Set
VC = Vec ℕ n

_[_] : VC → Fin n → ℕ
_[_] = Vec.lookup

vc₀ : VC
vc₀ = Vec.replicate 0

tick : Fin n → VC → VC
tick i = Vec.updateAt i ℕ.suc

combine : VC → VC → VC
combine = Vec.zipWith ℕ._⊔_
