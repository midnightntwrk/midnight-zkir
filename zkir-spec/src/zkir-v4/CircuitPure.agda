{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.CircuitPure (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Types ⋯
open import zkir-v4.Syntax ⋯
open import zkir-v4.Semantics ⋯ hiding (write; writes)
open import zkir-v4.Circuit ⋯
open import zkir-v4.CircuitBridge ⋯ using (WriteAgreement; write-agreed; write-backward; guard-pass)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Nat using (ℕ; _^_; _<_; _<?_; _≤_)
open import Data.Product using (_×_; _,_; ∃)
open import Data.Vec using (toList)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Nullary.Negation using (contradiction)

-- Dynamic side conditions for operations where preprocessing and the
-- circuit use different contracts.  Each describes an operand domain
-- or a primitive codec agreement.  They are independent of the outputs
-- and the success of either complete walk.
data Special (m : Mem) : Instruction → Set where
  assertion : ∀ {x} b → resolveᶠ m x ≡ just (χ b) → Special m (assert x)
  selection : ∀ {g a b o x y} → resolve m a ≡ just x → resolve m b ≡ just y
            → select-supported (typeof x) ≡ true → Special m (cond-select g a b o)
  equality-test : ∀ {a b o x y} → resolve m a ≡ just x → resolve m b ≡ just y
                → typeof x ≡ typeof y → Special m (test-eq a b o)
  equality-constraint : ∀ {a b x y} → resolve m a ≡ just x → resolve m b ≡ just y
                      → typeof x ≡ typeof y → ¬ (typeof x ≡ accumulator)
                      → Special m (constrain-eq a b)
  comparison : ∀ {a b n o x y} → resolveᶠ m a ≡ just x → resolveᶠ m b ≡ just y
             → n < FR-BITS → valFr x < 2 ^ n → valFr y < 2 ^ n
             → valFr x < 2 ^ even4 n → valFr y < 2 ^ even4 n
             → Special m (less-than a b n o)
  parts : ∀ {lo hi o} (x : Fr) → resolve m hi ≡ just (val-native x)
        → Special m (bytes32-from-low-high (lo , hi) o)
  persistent : ∀ {a xs o} → (∀ vs → resolve-all-Fr m xs ≡ just vs
                             → persistent-hash-circuit-fn a vs ≡ persistent-hash-fn a vs)
             → Special m (persistent-hash a xs o)
  keccak-hash : ∀ {a xs o} → (∀ vs → resolve-all-Fr m xs ≡ just vs
                              → keccak-circuit-fn a vs ≡ keccak-fn a vs)
              → Special m (keccak256 a xs o)
  sha-hash : ∀ {a xs o} → (∀ vs → resolve-all-Fr m xs ≡ just vs
                           → sha512-circuit-fn a vs ≡ sha512-fn a vs)
           → Special m (sha512 a xs o)

special-off : ∀ p src st i → Special (State.mem st) i
            → step p src st i ≡ (compute (State.mem st) i >>= λ ws →
                                just (record st { mem = apply-writes (State.mem st) ws }))
special-off _ _ _ _ (assertion _ _) = refl
special-off _ _ _ _ (selection _ _ _) = refl
special-off _ _ _ _ (equality-test _ _ _) = refl
special-off _ _ _ _ (equality-constraint _ _ _ _) = refl
special-off _ _ _ _ (comparison _ _ _ _ _ _ _) = refl
special-off _ _ _ _ (parts _ _) = refl
special-off _ _ _ _ (persistent _) = refl
special-off _ _ _ _ (keccak-hash _) = refl
special-off _ _ _ _ (sha-hash _) = refl

special-checked : Instruction → Bool
special-checked (bytes32-from-low-high _ _) = false
special-checked _ = true

private
  eq-contract : ∀ x y → ¬ (typeof x ≡ accumulator) → constrainEq? x y ≡ valEq? x y
  eq-contract (val-native _) _ _ = refl
  eq-contract (val-bytes _) _ _ = refl
  eq-contract (val-byte _) _ _ = refl
  eq-contract (val-bool _) _ _ = refl
  eq-contract (val-accumulator _) _ neq = contradiction refl neq
  eq-contract (val-jubjub-point _) _ _ = refl
  eq-contract (val-jubjub-scalar _) _ _ = refl
  eq-contract (val-secp256k1-point _) _ _ = refl
  eq-contract (val-secp256k1-base _) _ _ = refl
  eq-contract (val-secp256k1-scalar _) _ _ = refl
  eq-contract (val-secp256r1-point _) _ _ = refl
  eq-contract (val-secp256r1-base _) _ _ = refl
  eq-contract (val-secp256r1-scalar _) _ _ = refl
  eq-contract (val-curve25519-point _) _ _ = refl
  eq-contract (val-curve25519-base _) _ _ = refl
  eq-contract (val-curve25519-scalar _) _ _ = refl

-- All uses of a checked write are supplied by the actual circuit walk.
-- Factoring out that continuation gives both proof directions at once.
special-agree : ∀ src w st i → Special (CircuitState.mem st) i
              → stepᶜ src w st (lower i)
                ≡ (compute (CircuitState.mem st) i >>= write (special-checked i) w st)
special-agree src w st (assert x) (assertion false val) rewrite val with 0ᶠ ≟ᶠ 0ᶠ
... | yes _ = refl
... | no ne = contradiction refl ne
special-agree src w st (assert x) (assertion true val) rewrite val with 1ᶠ ≟ᶠ 0ᶠ
... | yes eq = contradiction eq 1ᶠ≢0ᶠ
... | no _ with 1ᶠ ≟ᶠ 1ᶠ
...   | yes _ = refl
...   | no ne = contradiction refl ne
special-agree src w st (cond-select g a b o) (selection {x = x} {y} av bv sup)
  rewrite av | bv | sup with resolve𝔹 (CircuitState.mem st) g
... | nothing = refl
... | just flag with typeof x ≟T typeof y
...   | yes _ = refl
...   | no _ = refl
special-agree src w st (test-eq a b o) (equality-test {x = x} {y} av bv same)
  rewrite av | bv | guard-pass (typeof x ≟T typeof y) same (valEq? x y)
  with valEq? x y
... | nothing = refl
... | just _ = refl
special-agree src w st (constrain-eq a b) (equality-constraint {x = x} {y} av bv same supported)
  rewrite av | bv | eq-contract x y supported | guard-pass (typeof x ≟T typeof y) same (valEq? x y)
  with valEq? x y
... | nothing = refl
... | just true = refl
... | just false = refl
special-agree src w st (less-than a b n o) (comparison {x = x} {y} ra rb n-ok xa ya xc yc)
  rewrite ra | rb
  with n <? FR-BITS | valFr x <? 2 ^ n | valFr y <? 2 ^ n
     | valFr x <? 2 ^ even4 n | valFr y <? 2 ^ even4 n | valFr x <? valFr y
... | no bad | _ | _ | _ | _ | _ = contradiction n-ok bad
... | yes _ | no bad | _ | _ | _ | _ = contradiction xa bad
... | yes _ | yes _ | no bad | _ | _ | _ = contradiction ya bad
... | yes _ | yes _ | yes _ | no bad | _ | _ = contradiction xc bad
... | yes _ | yes _ | yes _ | yes _ | no bad | _ = contradiction yc bad
... | yes _ | yes _ | yes _ | yes _ | yes _ | yes _ = refl
... | yes _ | yes _ | yes _ | yes _ | yes _ | no _ = refl
special-agree src w st (bytes32-from-low-high (lo , hi) o) (parts x val)
  rewrite val with resolve (CircuitState.mem st) lo
... | nothing = refl
... | just l with bytes32-from-parts l (val-native x)
...   | nothing = refl
...   | just _ = refl
special-agree src w st (persistent-hash a xs o) (persistent law)
  with resolve-all-Fr (CircuitState.mem st) xs in resolved
... | nothing = refl
... | just vs rewrite law vs refl with persistent-hash-fn a vs
...   | nothing = refl
...   | just _ = refl
special-agree src w st (keccak256 a xs o) (keccak-hash law)
  with resolve-all-Fr (CircuitState.mem st) xs in resolved
... | nothing = refl
... | just vs rewrite law vs refl with keccak-fn a vs
...   | nothing = refl
...   | just _ = refl
special-agree src w st (sha512 a xs o) (sha-hash law)
  with resolve-all-Fr (CircuitState.mem st) xs in resolved
... | nothing = refl
... | just vs rewrite law vs refl with sha512-fn a vs
...   | nothing = refl
...   | just _ = refl

special-forward : ∀ src w st i ws → Special (CircuitState.mem st) i
                → compute (CircuitState.mem st) i ≡ just ws
                → WriteAgreement (special-checked i) w ws
                → stepᶜ src w st (lower i) ≡ just (record st { mem = apply-writes (CircuitState.mem st) ws })
special-forward src w st i ws shape calc writes-ok
  rewrite special-agree src w st i shape | calc = write-agreed (special-checked i) w st ws writes-ok

special-backward : ∀ src w st i {final} → Special (CircuitState.mem st) i
                 → stepᶜ src w st (lower i) ≡ just final
                 → ∃ λ ws → compute (CircuitState.mem st) i ≡ just ws
                           × final ≡ record st { mem = apply-writes (CircuitState.mem st) ws }
special-backward src w st i shape success rewrite special-agree src w st i shape
  with compute (CircuitState.mem st) i
... | nothing with () ← success
... | just ws = ws , refl , write-backward (special-checked i) w st ws success
