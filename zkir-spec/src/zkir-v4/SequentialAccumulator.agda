{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.SequentialAccumulator (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Circuit ⋯
open import zkir-v4.CircuitBridge ⋯ using (shared-backward)
open import zkir-v4.Encoding ⋯ using (encode-accumulator)
open import zkir-v4.Operations ⋯ using (apply-writes; compute; resolve-all-Fr)
open import zkir-v4.Syntax ⋯
open import zkir-v4.Types ⋯

open import Data.List using (List; []; _∷_; _++_; allFin; map; zip)
open import Data.Maybe using (just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
import Data.Vec as Vec
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

carried-fields : List Identifier
carried-fields = "%a0" ∷ "%a1" ∷ "%a2" ∷ "%a3" ∷ "%a4" ∷ "%a5" ∷
                 "%a6" ∷ "%a7" ∷ "%a8" ∷ "%a9" ∷ "%a10" ∷ "%a11" ∷ []

-- The enumeration exposes the write names even when the curve coordinates
-- are abstract, so lookups at unrelated concrete names reduce directly.
limb-values : Accumulator → List Fr
limb-values a = map (Vec.lookup (g1-to-fields (proj₁ a))) (allFin 5) ++
  (1ᶠ ∷ map (Vec.lookup (g1-to-fields (proj₂ a))) (allFin 5) ++ (1ᶠ ∷ []))

limbs-encode : ∀ a → limb-values a ≡ encode-accumulator a
limbs-encode (l , r) with g1-to-fields l | g1-to-fields r
... | a Vec.∷ b Vec.∷ c Vec.∷ d Vec.∷ e Vec.∷ Vec.[]
    | f Vec.∷ g Vec.∷ h Vec.∷ i Vec.∷ j Vec.∷ Vec.[] = refl

carry-writes : Accumulator → List (Identifier × IrValue)
carry-writes a = zip carried-fields (map val-native (limb-values a))

encoded-state : CircuitState → Accumulator → CircuitState
encoded-state st a = record st { mem = apply-writes (CircuitState.mem st) (carry-writes a) }

encode-computes : ∀ st a → CircuitState.mem st "%carried" ≡ just (val-accumulator a) →
  compute (CircuitState.mem st) (encode (var "%carried") carried-fields) ≡ just (carry-writes a)
encode-computes st a found rewrite found | sym (limbs-encode a) = refl

encode-carried : ∀ src w st {after} a →
  CircuitState.mem st "%carried" ≡ just (val-accumulator a) →
  stepᶜ src w st (lower (encode (var "%carried") carried-fields)) ≡ just after →
  after ≡ encoded-state st a
encode-carried src w st a found ran
  with shared-backward src w st (encode (var "%carried") carried-fields) ran
... | ws , computed , state
  rewrite just-injective (trans (sym computed) (encode-computes st a found)) = state

resolve-carried-fields : ∀ st a →
  resolve-all-Fr (CircuitState.mem (encoded-state st a)) (map var carried-fields)
    ≡ just (encode-accumulator a)
resolve-carried-fields st a rewrite sym (limbs-encode a) = refl
