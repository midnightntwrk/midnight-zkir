{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.SegmentEncoding (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Circuit ⋯
open import zkir-v4.CircuitBridge ⋯ using (shared-backward; shared-forward; WriteAgreement)
open import zkir-v4.Encoding ⋯ using (encode-accumulator)
open import zkir-v4.Operations ⋯ using (Mem; ∅; ins; apply-writes; compute; resolve-all-Fr)
open import zkir-v4.Protocol ⋯ using (instance-fields)
open import zkir-v4.SegmentSource ⋯
open import zkir-v4.SequentialAccumulator ⋯ using (limb-values; limbs-encode)
open import zkir-v4.SequentialSource ⋯ using (initial-state; active; resolve-padding; resolve-append)
open import zkir-v4.Syntax ⋯
open import zkir-v4.Types ⋯

open import Data.Bool using (true)
open import Data.List using (List; []; _∷_; _++_; map; zip)
open import Data.List.Properties using (++-identityʳ)
open import Data.Maybe using (just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

carry-writes : Side → Accumulator → List (Identifier × IrValue)
carry-writes side a = zip (limbs side) (map val-native (limb-values a))

encoded-state : Side → CircuitState → Accumulator → CircuitState
encoded-state side st a = record st { mem = apply-writes (CircuitState.mem st) (carry-writes side a) }

encode-computes : ∀ side st a → CircuitState.mem st (carry-id side) ≡ just (val-accumulator a) →
  compute (CircuitState.mem st) (encode (var (carry-id side)) (limbs side)) ≡ just (carry-writes side a)
encode-computes lhs st a found rewrite found | sym (limbs-encode a) = refl
encode-computes rhs st a found rewrite found | sym (limbs-encode a) = refl

encode-carried : ∀ side src w st {after} a →
  CircuitState.mem st (carry-id side) ≡ just (val-accumulator a) →
  stepᶜ src w st (lower (encode (var (carry-id side)) (limbs side))) ≡ just after →
  after ≡ encoded-state side st a
encode-carried side src w st a found ran
  with shared-backward src w st (encode (var (carry-id side)) (limbs side)) ran
... | ws , computed , state
  rewrite just-injective (trans (sym computed) (encode-computes side st a found)) = state

encode-step : ∀ side src w st a →
  CircuitState.mem st (carry-id side) ≡ just (val-accumulator a) →
  WriteAgreement true w (carry-writes side a) →
  stepᶜ src w st (lower (encode (var (carry-id side)) (limbs side))) ≡ just (encoded-state side st a)
encode-step side src w st a found =
  shared-forward src w st (encode (var (carry-id side)) (limbs side)) (carry-writes side a)
    (encode-computes side st a found)

resolve-carried-fields : ∀ side st a →
  resolve-all-Fr (CircuitState.mem (encoded-state side st a)) (map var (limbs side))
    ≡ just (encode-accumulator a)
resolve-carried-fields lhs st a rewrite sym (limbs-encode a) = refl
resolve-carried-fields rhs st a rewrite sym (limbs-encode a) = refl

resolve-child : ∀ side m n c a b carried →
  resolve-all-Fr m (map var (limbs side)) ≡ just (encode-accumulator carried) →
  m ctx ≡ just (val-native c) →
  m (from-id side) ≡ just (val-native a) →
  m (to-id side) ≡ just (val-native b) →
  resolve-all-Fr m (ops side n) ≡ just (instance-fields (carried ∷ []) (fields n c a b))
resolve-child side m n c a b carried encoded context-ok from-ok to-ok =
  trans (resolve-append m (map var (limbs side)) (imm 0ᶠ ∷ statement-operands n (from-id side) (to-id side))
    (encode-accumulator carried) (fields n c a b) encoded statement-ok)
    (cong (λ block → just (block ++ fields n c a b)) (sym (++-identityʳ (encode-accumulator carried))))
  where
  statement-ok : resolve-all-Fr m (imm 0ᶠ ∷ statement-operands n (from-id side) (to-id side))
    ≡ just (fields n c a b)
  statement-ok rewrite context-ok | from-ok | to-ok | resolve-padding m n = refl

join-memory : Fr → Fr → Fr → Fr → Accumulator → Accumulator → Mem
join-memory c a midpoint b lc rc =
  ins (carry-id rhs) (val-accumulator rc)
    (ins (carry-id lhs) (val-accumulator lc)
      (ins z (val-native b)
        (ins mid (val-native midpoint)
          (ins x (val-native a)
            (ins ctx (val-native c) ∅)))))

published : CircuitWitness → ℕ → Fr → Fr → Fr → Fr → Accumulator → Accumulator → CircuitState
published w n c a m b lc rc = record (initial-state w (join-memory c a m b lc rc))
  { pis = observed-fields n (CircuitWitness.binding-input w) c a b }

publish-step : ∀ src w n c a m b lc rc →
  stepᶜ src w (initial-state w (join-memory c a m b lc rc)) (lower (publish n z))
    ≡ just (published w n c a m b lc rc)
publish-step src w n c a m b lc rc rewrite active | resolve-padding (join-memory c a m b lc rc) n = refl
