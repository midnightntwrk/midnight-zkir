{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.ProducerCompute (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Types ⋯
open import zkir-v4.Syntax ⋯
open import zkir-v4.ProducerStep ⋯ using (ComputeTypes)
open import zkir-v4.ProducerValuesHelpers ⋯ using (Rule)
open import zkir-v4.ProducerValues ⋯ using (module Rules)
open import zkir-v4.ProducerAlgebra ⋯ using (module Algebra)
open import zkir-v4.ProducerCurveValues ⋯
open import zkir-v4.ProducerByteValues ⋯
open import Data.Product using (_,_)

-- The VM handles effects separately.  Every successful pure computation
-- writes exactly the names and types inferred for its instruction.
compute-types : ComputeTypes
compute-types sig Γ m i store = result i
  where
  module R = Rules sig Γ m store
  module A = Algebra sig Γ m store

  result : ∀ i → Rule sig Γ m i
  result (encode x os) = R.encode-value x os
  result (assert x) = R.assert-value x
  result (cond-select g a b o) = R.selected g a b o
  result (constrain-bits x n) = R.bit-value x n
  result (constrain-eq a b) = R.equal-constraint a b
  result (constrain-to-boolean x) = R.bool-constraint x
  result (copy x o) = A.copy-types x o
  result (impact _ _) _ ()
  result (ec-mul p s o) = ec-mul-types sig Γ m p s o store
  result (ec-mul-generator s o) = ec-mul-generator-types sig Γ m s o store
  result (hash-to-curve xs o) = R.hash-curve xs o
  result (into-coordinates p (x , y)) = into-coordinates-types sig Γ m store p x y
  result (from-coordinates (x , y) o) = from-coordinates-types sig Γ m store x y o
  result (into-bytes32 a o) = into32-types sig Γ m store a o
  result (from-bytes32 a t o) = from32-types sig Γ m store a t o
  result (reverse-bytes a o) = reverse32-types sig Γ m store a o
  result (bytes32-into-low-high x (lo , hi)) = R.into-parts x lo hi
  result (bytes32-from-low-high xy o) = parts-types sig Γ m store xy o
  result (div-mod-power-of-two x n os) = R.divide-value x n os
  result (reconstitute-field d a n o) = R.reconstitute-value d a n o
  result (transient-hash xs o) = R.transient xs o
  result (persistent-hash a xs o) = R.persistent-value a xs o
  result (keccak256 a xs o) = R.keccak-value a xs o
  result (test-eq a b o) = R.test-value a b o
  result (add a b o) = A.add-types a b o
  result (mul a b o) = A.mul-types a b o
  result (neg x o) = A.neg-types x o
  result (inv x o) = A.inv-types x o
  result (not x o) = R.native-not x o
  result (less-than a b n o) = R.less-value a b n o
  result (jubjub-scalar-from-native x o) = R.native-scalar x o
  result (public-input _ _ _) _ ()
  result (private-input _ _ _) _ ()
  result (circuit-output _) _ ()
  result (slice x start n o) = slice-types sig Γ m store x start n o
  result (nth x n o) = R.nth-value x n o
  result (concat xs o) = concat-types sig Γ m store xs o
  result (reverse x o) = reverse-types sig Γ m store x o
  result (load-constant t raw o) = R.load-value t raw o
  result (sha512 a xs o) = R.sha-value a xs o
  result (and xs o) = R.and-value xs o
  result (or xs o) = R.or-value xs o
  result (xor xs o) = R.xor-value xs o
  result (to-bytes x o) = to-bytes-types sig Γ m store x o
  result (from-bytes x t o) = from-bytes-types sig Γ m store x t o
  result (bytes-into-natives x os) = R.into-natives x os
  result (bytes-from-natives xs n o) = R.from-natives xs n o
  result (inner-proof _ _) _ ()
  result (prepare-verification _ _ _ _ _) _ ()
  result (accumulate _ _) _ ()
  result (verify-accumulator _) _ ()
