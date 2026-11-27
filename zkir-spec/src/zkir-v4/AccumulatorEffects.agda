{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.AccumulatorEffects (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Circuit ⋯
open import zkir-v4.CircuitBridge ⋯ using (write-backward)
open import zkir-v4.CircuitEvents ⋯ using (inserted-value)
open import zkir-v4.Operations ⋯ using (ins; resolve𝔹; resolve-all-Fr; resolve-acc; resolve-accs)
open import zkir-v4.RecursiveVerification ⋯ public using (Valid)
open import zkir-v4.Syntax ⋯
open import zkir-v4.Types ⋯ using (val-accumulator)
open import zkir-v4.Validation ⋯ using (resolve-vk)

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All as All using (All)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; trans; subst)

-- These observations retain the actual inputs and outputs of a successful
-- circuit step.  A disabled preparation carries no claim of inner validity.
record Prepared (src : IrSource) (st : CircuitState) (g : Operand) (hash : List Byte)
                (ops : List Operand) (pr out : Identifier) (st′ : CircuitState) : Set where
  constructor preparation
  field
    active : Bool
    key : List Byte
    fields : List Fr
    raw : List Byte
    opening : Accumulator
    guard-ok : resolve𝔹 (CircuitState.mem st) g ≡ just active
    key-ok : resolve-vk hash (IrSource.inner-vks src) ≡ just key
    parsed : key-well-formed key ≡ true
    instance-ok : resolve-all-Fr (CircuitState.mem st) ops ≡ just fields
    proof-ok : CircuitState.proofs st pr ≡ just raw
    prepared : prepare-circuit key fields raw active ≡ just opening
    after-write : st′ ≡ record st { mem = ins out (val-accumulator opening) (CircuitState.mem st) }

  stored : CircuitState.mem st′ out ≡ just (val-accumulator opening)
  stored = trans (cong (λ s → CircuitState.mem s out) after-write) (inserted-value out _ _)

prepared-step : ∀ src w st g hash ops pr out {st′} →
  stepᶜ src w st (prepare-proof g hash ops pr out) ≡ just st′ → Prepared src st g hash ops pr out st′
prepared-step src w st g hash ops pr out ok with resolve𝔹 (CircuitState.mem st) g in flag
... | nothing = case ok of λ ()
... | just active with resolve-all-Fr (CircuitState.mem st) ops in public-fields
...   | nothing = case ok of λ ()
...   | just xs with CircuitState.proofs st pr in slot
...     | nothing = case ok of λ ()
...     | just raw with resolve-vk hash (IrSource.inner-vks src) in lookup
...       | nothing = case ok of λ ()
...       | just key with key-well-formed key in parses
...         | false = case ok of λ ()
...         | true with prepare-circuit key xs raw active in opening-ok
...           | nothing = case ok of λ ()
...           | just a = preparation active key xs raw a flag lookup parses public-fields slot opening-ok
                           (write-backward true w st ((out , val-accumulator a) ∷ []) ok)

record Folded (st : CircuitState) (ops : List Operand) (out : Identifier) (st′ : CircuitState) : Set where
  constructor folding
  field
    inputs : List Accumulator
    output : Accumulator
    resolved : resolve-accs (CircuitState.mem st) ops ≡ just inputs
    folded : fold-accumulators inputs ≡ just output
    after-write : st′ ≡ record st { mem = ins out (val-accumulator output) (CircuitState.mem st) }

  stored : CircuitState.mem st′ out ≡ just (val-accumulator output)
  stored = trans (cong (λ s → CircuitState.mem s out) after-write) (inserted-value out _ _)

fold-step : ∀ src w st ops out {st′} →
  stepᶜ src w st (fold-accs ops out) ≡ just st′ → Folded st ops out st′
fold-step src w st ops out ok with resolve-accs (CircuitState.mem st) ops in resolved
... | nothing = case ok of λ ()
... | just [] = case ok of λ ()
... | just (_ ∷ []) = case ok of λ ()
... | just (a ∷ b ∷ rest) with fold-accumulators (a ∷ b ∷ rest) in eq
...   | nothing = case ok of λ ()
...   | just f = folding (a ∷ b ∷ rest) f resolved eq (write-backward true w st ((out , val-accumulator f) ∷ []) ok)

record Exposed (st : CircuitState) (op : Operand) (st′ : CircuitState) : Set where
  constructor exposure-step
  field
    value : Accumulator
    resolved : resolve-acc (CircuitState.mem st) op ≡ just value
    after-expose : st′ ≡ record st { accs = CircuitState.accs st ++ (value ∷ []) }

  appended : CircuitState.accs st′ ≡ CircuitState.accs st ++ (value ∷ [])
  appended = cong CircuitState.accs after-expose

expose-step : ∀ src w st op {st′} → stepᶜ src w st (publish-acc op) ≡ just st′ → Exposed st op st′
expose-step src w st op ok with resolve-acc (CircuitState.mem st) op in resolved
... | nothing = case ok of λ ()
... | just a = exposure-step a resolved (sym (just-injective ok))

private
  last-valid : ∀ as {a} → All Valid (as ++ (a ∷ [])) → Valid a
  last-valid [] (good All.∷ _) = good
  last-valid (_ ∷ as) (_ All.∷ rest) = last-valid as rest

exposed-valid : ∀ {st op st′} (e : Exposed st op st′) → All Valid (CircuitState.accs st′) → Valid (Exposed.value e)
exposed-valid {st} e valid = last-valid (CircuitState.accs st) (subst (All Valid) (Exposed.appended e) valid)
