{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.SynthesisDomains (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Types ⋯
open import zkir-v4.Syntax ⋯
open import zkir-v4.Operations ⋯ hiding (write)
open import zkir-v4.Circuit ⋯
open import zkir-v4.CircuitBackward ⋯ using (PureAdmissible; common-op; bit-constraint-op; division-op; reconstitution-op; special-op)
open import zkir-v4.CircuitProof ⋯ using (Common)
open import zkir-v4.CircuitPure ⋯ using (Special; assertion; selection; equality-test; equality-constraint; comparison; parts; persistent; keccak-hash; sha-hash)
open import Data.Bool using (true; false)
open import Data.List using (List)
open import Data.Maybe using (just; nothing; _>>=_)
open import Data.Nat using (_^_; _<_; _<?_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Nullary.Negation using (contradiction)

data PureInstruction : Instruction → Set where
  ordinary : ∀ {i} → Common i → PureInstruction i
  bit-form : ∀ {x n} → PureInstruction (constrain-bits x n)
  division-form : ∀ {x n os} → PureInstruction (div-mod-power-of-two x n os)
  reconstitution-form : ∀ {d m n o} → PureInstruction (reconstitute-field d m n o)
  assertion-form : ∀ {x} → PureInstruction (assert x)
  selection-form : ∀ {g a b o} → PureInstruction (cond-select g a b o)
  equality-test-form : ∀ {a b o} → PureInstruction (test-eq a b o)
  equality-constraint-form : ∀ {a b} → PureInstruction (constrain-eq a b)
  comparison-form : ∀ {a b n o} → PureInstruction (less-than a b n o)
  parts-form : ∀ {l h o} → PureInstruction (bytes32-from-low-high (l , h) o)
  persistent-form : ∀ {a xs o} → PureInstruction (persistent-hash a xs o)
  keccak-hash-form : ∀ {a xs o} → PureInstruction (keccak256 a xs o)
  sha-hash-form : ∀ {a xs o} → PureInstruction (sha512 a xs o)

-- Width checks use source parameters.  Assertions and comparisons have
-- stricter VM value checks.  The other three clauses concern the
-- independently supplied hash primitive for the instruction's alignment.
PureResidual : Mem → Instruction → Set
PureResidual m i@(constrain-bits _ _) = preprocess-bit-bounds i ≡ true
PureResidual m i@(div-mod-power-of-two _ _ _) = preprocess-bit-bounds i ≡ true
PureResidual m i@(reconstitute-field _ _ _ _) = preprocess-bit-bounds i ≡ true
PureResidual m (assert a) = ∀ x → resolveᶠ m a ≡ just x → ¬ (x ≡ 0ᶠ) → x ≡ 1ᶠ
PureResidual m (less-than a b n _) = n < FR-BITS ×
  (∀ x y → resolveᶠ m a ≡ just x → resolveᶠ m b ≡ just y
    → valFr x < 2 ^ even4 n → valFr y < 2 ^ even4 n → valFr x < 2 ^ n × valFr y < 2 ^ n)
PureResidual m (persistent-hash a xs _) = ∀ vs → resolve-all-Fr m xs ≡ just vs
  → persistent-hash-circuit-fn a vs ≡ persistent-hash-fn a vs
PureResidual m (keccak256 a xs _) = ∀ vs → resolve-all-Fr m xs ≡ just vs
  → keccak-circuit-fn a vs ≡ keccak-fn a vs
PureResidual m (sha512 a xs _) = ∀ vs → resolve-all-Fr m xs ≡ just vs
  → sha512-circuit-fn a vs ≡ sha512-fn a vs
PureResidual _ _ = ⊤

private
  eq-supported : ∀ x y {b} → valEq? x y ≡ just b → ¬ (typeof x ≡ accumulator)
  eq-supported (val-native _) y ok ()
  eq-supported (val-bytes _) y ok ()
  eq-supported (val-byte _) y ok ()
  eq-supported (val-bool _) y ok ()
  eq-supported (val-jubjub-point _) y ok ()
  eq-supported (val-jubjub-scalar _) y ok ()
  eq-supported (val-secp256k1-point _) y ok ()
  eq-supported (val-secp256k1-base _) y ok ()
  eq-supported (val-secp256k1-scalar _) y ok ()
  eq-supported (val-secp256r1-point _) y ok ()
  eq-supported (val-secp256r1-base _) y ok ()
  eq-supported (val-secp256r1-scalar _) y ok ()
  eq-supported (val-curve25519-point _) y ok ()
  eq-supported (val-curve25519-base _) y ok ()
  eq-supported (val-curve25519-scalar _) y ok ()
  eq-supported (val-accumulator _) y ()

pure-domain : ∀ src w st i {after} → PureInstruction i → PureResidual (CircuitState.mem st) i
            → stepᶜ src w st (lower i) ≡ just after → PureAdmissible (CircuitState.mem st) i
pure-domain _ _ _ _ (ordinary c) _ _ = common-op c
pure-domain _ _ _ _ bit-form width _ = bit-constraint-op width
pure-domain _ _ _ _ division-form width _ = division-op width
pure-domain _ _ _ _ reconstitution-form width _ = reconstitution-op width
pure-domain _ _ _ _ persistent-form law _ = special-op (persistent law)
pure-domain _ _ _ _ keccak-hash-form law _ = special-op (keccak-hash law)
pure-domain _ _ _ _ sha-hash-form law _ = special-op (sha-hash law)
pure-domain src w st (assert a) assertion-form canonical ok with resolveᶠ (CircuitState.mem st) a in r
... | nothing with () ← ok
... | just x with x ≟ᶠ 0ᶠ
...   | yes _ with () ← ok
...   | no nz with refl ← canonical x refl nz = special-op (assertion true r)
pure-domain src w st (cond-select g a b o) selection-form _ ok with resolve𝔹 (CircuitState.mem st) g
... | nothing with () ← ok
... | just flag with resolve (CircuitState.mem st) a in ra
...   | nothing with () ← ok
...   | just x with resolve (CircuitState.mem st) b in rb
...     | nothing with () ← ok
...     | just y with typeof x ≟T typeof y
...       | no _ with () ← ok
...       | yes _ with select-supported (typeof x) in sup
...         | false with () ← ok
...         | true = special-op (selection ra rb sup)
pure-domain src w st (test-eq a b o) equality-test-form _ ok with resolve (CircuitState.mem st) a in ra
... | nothing with () ← ok
... | just x with resolve (CircuitState.mem st) b in rb
...   | nothing with () ← ok
...   | just y with typeof x ≟T typeof y
...     | no _ with () ← ok
...     | yes same = special-op (equality-test ra rb same)
pure-domain src w st (constrain-eq a b) equality-constraint-form _ ok with resolve (CircuitState.mem st) a in ra
... | nothing with () ← ok
... | just x with resolve (CircuitState.mem st) b in rb
...   | nothing with () ← ok
...   | just y with typeof x ≟T typeof y
...     | no _ with () ← ok
...     | yes same with valEq? x y in eq
...       | nothing with () ← ok
...       | just _ = special-op (equality-constraint ra rb same (eq-supported x y eq))
pure-domain src w st (less-than a b n o) comparison-form (width , tight) ok with resolveᶠ (CircuitState.mem st) a in ra
... | nothing with () ← ok
... | just x with resolveᶠ (CircuitState.mem st) b in rb
...   | nothing with () ← ok
...   | just y with valFr x <? 2 ^ even4 n | valFr y <? 2 ^ even4 n
...     | no _ | _ with () ← ok
...     | yes _ | no _ with () ← ok
...     | yes bx | yes by with tight x y refl refl bx by
...       | sx , sy = special-op (comparison ra rb width sx sy bx by)
pure-domain src w st (bytes32-from-low-high (l , h) o) parts-form _ ok with resolve (CircuitState.mem st) h in rh
... | nothing with () ← ok
... | just (val-native x) = special-op (parts x rh)
... | just (val-bytes _) with () ← ok
... | just (val-byte _) with () ← ok
... | just (val-bool _) with () ← ok
... | just (val-accumulator _) with () ← ok
... | just (val-jubjub-point _) with () ← ok
... | just (val-jubjub-scalar _) with () ← ok
... | just (val-secp256k1-point _) with () ← ok
... | just (val-secp256k1-base _) with () ← ok
... | just (val-secp256k1-scalar _) with () ← ok
... | just (val-secp256r1-point _) with () ← ok
... | just (val-secp256r1-base _) with () ← ok
... | just (val-secp256r1-scalar _) with () ← ok
... | just (val-curve25519-point _) with () ← ok
... | just (val-curve25519-base _) with () ← ok
... | just (val-curve25519-scalar _) with () ← ok
