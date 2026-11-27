{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.CircuitEvents (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Syntax ⋯
open import zkir-v4.Semantics ⋯ using (ins; insert-proof)
open import zkir-v4.CircuitProof ⋯ using (Common)
open import zkir-v4.CircuitPure ⋯ using (Special)
open import zkir-v4.CircuitExtraction ⋯ using (event; empty)

open import Data.Empty using (⊥-elim)
open import Data.Maybe using (just)
open import Data.Product using (_,_)
open import Data.String using () renaming (_≟_ to _≟str_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)

inserted-value : ∀ id v m → ins id v m id ≡ just v
inserted-value id v m with id ≟str id
... | yes _ = refl
... | no ne = ⊥-elim (ne refl)

inserted-proof : ∀ id v m → insert-proof id v m id ≡ just v
inserted-proof id v m with id ≟str id
... | yes _ = refl
... | no ne = ⊥-elim (ne refl)

Eventless : Instruction → Set
Eventless i = ∀ before after → event before after i ≡ just empty

common-eventless : ∀ i → Common i → Eventless i
common-eventless (encode _ _) _ _ _ = refl
common-eventless (assert _) ()
common-eventless (cond-select _ _ _ _) ()
common-eventless (constrain-bits _ _) _ _ _ = refl
common-eventless (constrain-eq _ _) ()
common-eventless (constrain-to-boolean _) _ _ _ = refl
common-eventless (copy _ _) _ _ _ = refl
common-eventless (impact _ _) ()
common-eventless (ec-mul _ _ _) _ _ _ = refl
common-eventless (ec-mul-generator _ _) _ _ _ = refl
common-eventless (hash-to-curve _ _) _ _ _ = refl
common-eventless (into-coordinates _ _) _ _ _ = refl
common-eventless (from-coordinates _ _) _ _ _ = refl
common-eventless (into-bytes32 _ _) _ _ _ = refl
common-eventless (from-bytes32 _ _ _) _ _ _ = refl
common-eventless (reverse-bytes _ _) _ _ _ = refl
common-eventless (bytes32-into-low-high _ _) _ _ _ = refl
common-eventless (bytes32-from-low-high (_ , _) _) ()
common-eventless (div-mod-power-of-two _ _ _) ()
common-eventless (reconstitute-field _ _ _ _) ()
common-eventless (transient-hash _ _) _ _ _ = refl
common-eventless (persistent-hash _ _ _) ()
common-eventless (keccak256 _ _ _) ()
common-eventless (test-eq _ _ _) ()
common-eventless (add _ _ _) _ _ _ = refl
common-eventless (mul _ _ _) _ _ _ = refl
common-eventless (neg _ _) _ _ _ = refl
common-eventless (inv _ _) _ _ _ = refl
common-eventless (not _ _) _ _ _ = refl
common-eventless (less-than _ _ _ _) ()
common-eventless (jubjub-scalar-from-native _ _) _ _ _ = refl
common-eventless (slice _ _ _ _) _ _ _ = refl
common-eventless (nth _ _ _) _ _ _ = refl
common-eventless (concat _ _) _ _ _ = refl
common-eventless (reverse _ _) _ _ _ = refl
common-eventless (load-constant _ _ _) _ _ _ = refl
common-eventless (sha512 _ _ _) ()
common-eventless (and _ _) _ _ _ = refl
common-eventless (or _ _) _ _ _ = refl
common-eventless (xor _ _) _ _ _ = refl
common-eventless (to-bytes _ _) _ _ _ = refl
common-eventless (from-bytes _ _ _) _ _ _ = refl
common-eventless (bytes-into-natives _ _) _ _ _ = refl
common-eventless (bytes-from-natives _ _ _) _ _ _ = refl
common-eventless (public-input _ _ _) ()
common-eventless (private-input _ _ _) ()
common-eventless (circuit-output _) ()
common-eventless (inner-proof _ _) ()
common-eventless (prepare-verification _ _ _ _ _) ()
common-eventless (accumulate _ _) ()
common-eventless (verify-accumulator _) ()

special-eventless : ∀ {m i} → Special m i → Eventless i
special-eventless (Special.assertion _ _) _ _ = refl
special-eventless (Special.selection _ _ _) _ _ = refl
special-eventless (Special.equality-test _ _ _) _ _ = refl
special-eventless (Special.equality-constraint _ _ _ _) _ _ = refl
special-eventless (Special.comparison _ _ _ _ _ _ _) _ _ = refl
special-eventless (Special.parts _ _) _ _ = refl
special-eventless (Special.persistent _) _ _ = refl
special-eventless (Special.keccak-hash _) _ _ = refl
special-eventless (Special.sha-hash _) _ _ = refl
