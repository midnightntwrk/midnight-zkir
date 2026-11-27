{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.BoundaryExamples (⋯ : _) (open Assumptions ⋯) where

open import zkir-v4.Types ⋯
open import zkir-v4.Syntax ⋯
open import zkir-v4.Encoding ⋯ using (pack-bytes; native-from-bytes; encode-accumulator)
open import zkir-v4.Semantics ⋯
import zkir-v4.Circuit
module C = zkir-v4.Circuit ⋯
open import zkir-v4.Validation ⋯ using (validate; resolve-vk)
open import zkir-v4.Producer ⋯ using (admissible)
open import zkir-v4.ComparisonWidths ⋯ using (check-with-comparison-cap)

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (zero; suc)
open import Data.List using (List; []; _∷_; _++_; replicate; drop; take)
open import Data.Maybe using (just; nothing; map)
open import Data.Nat using (ℕ; _≤_; _≤?_; _<?_; _+_; _*_; _^_; _∸_)
open import Data.Nat.Properties using (≤⇒≯)
open import Data.Product using (_×_; _,_)
open import Data.Vec using (toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)

-- The 32nd byte starts a new little-endian field chunk.
pack-31 : pack-bytes (replicate 31 zero) ≡ native-from-bytes (replicate 31 zero) ∷ []
pack-31 = refl

pack-32 : pack-bytes (replicate 32 (suc zero)) ≡
          native-from-bytes (replicate 31 (suc zero)) ∷ native-from-bytes (suc zero ∷ []) ∷ []
pack-32 = refl

private
  hash-source : Instruction → IrSource
  hash-source i = mk-ir-source V0 [] [] false (i ∷ []) []

-- Each byte atom starts a fresh limb.  The two atoms need three fields.
fab-exact : admissible (hash-source (persistent-hash (bytes-atom 1 ∷ bytes-atom 32 ∷ [])
  (imm 0ᶠ ∷ imm 1ᶠ ∷ imm 0ᶠ ∷ []) "%digest")) ≡ true
fab-exact = refl

fab-surplus : admissible (hash-source (persistent-hash (field-atom ∷ [])
  (imm 0ᶠ ∷ imm 1ᶠ ∷ []) "%digest")) ≡ false
fab-surplus = refl

fab-short : admissible (hash-source (sha512 (bytes-atom 32 ∷ []) (imm 0ᶠ ∷ []) "%digest")) ≡ false
fab-short = refl

fab-option : admissible (hash-source (keccak256 (option [] ∷ []) (imm 0ᶠ ∷ []) "%digest")) ≡ false
fab-option = refl

fab-compress : admissible (hash-source (sha512 (compress-atom ∷ []) (imm 0ᶠ ∷ []) "%digest")) ≡ false
fab-compress = refl

private
  comparison-source : ℕ → IrSource
  comparison-source bits = mk-ir-source V0 [] [] false
    (less-than (imm 0ᶠ) (imm 0ᶠ) bits "%out" ∷ []) []

-- All three sources pass producer admission.  The RC1 checker admits 252
-- bits and rejects the two larger widths for every witness.
comparison-252 : ∀ w → (admissible (comparison-source 252) ≡ true) ×
  (check-with-comparison-cap (comparison-source 252) w ≡ C.check-circuit (comparison-source 252) w)
comparison-252 w = refl , refl

comparison-253 : ∀ w → (admissible (comparison-source 253) ≡ true) ×
  (check-with-comparison-cap (comparison-source 253) w ≡ nothing)
comparison-253 w = refl , refl

comparison-254 : ∀ w → (admissible (comparison-source 254) ≡ true) ×
  (check-with-comparison-cap (comparison-source 254) w ≡ nothing)
comparison-254 w = refl , refl

private
  small-bytes : List Byte
  small-bytes = zero ∷ suc zero ∷ []

  sample-mem : Mem
  sample-mem = ins "%bytes" (val-bytes small-bytes)
                 (ins "%one" (val-bytes (zero ∷ []))
                   (ins "%bit" (val-bool true) ∅))

slice-at-end : compute sample-mem (slice (var "%bytes") 1 1 "%out")
               ≡ just (("%out" , val-bytes (suc zero ∷ [])) ∷ [])
slice-at-end = refl

slice-empty : compute sample-mem (slice (var "%bytes") 0 0 "%out") ≡ nothing
slice-empty = refl

nth-at-end : compute sample-mem (nth (var "%bytes") 1 "%out")
             ≡ just (("%out" , val-byte (suc zero)) ∷ [])
nth-at-end = refl

nth-over-end : compute sample-mem (nth (var "%bytes") 2 "%out") ≡ nothing
nth-over-end = refl

no-empty-gate : compute sample-mem (and [] "%out") ≡ nothing
no-empty-gate = refl

typed-gate : compute sample-mem (xor (var "%bit" ∷ var "%bit" ∷ []) "%out")
            ≡ just (("%out" , val-bool false) ∷ [])
typed-gate = refl

typed-negation : compute sample-mem (neg (var "%bit") "%out")
                ≡ just (("%out" , val-bool false) ∷ [])
typed-negation = refl

no-native-gate : compute sample-mem (and (imm 1ᶠ ∷ []) "%out") ≡ nothing
no-native-gate = refl

mixed-byte-equality : compute sample-mem (test-eq (var "%one") (var "%bytes") "%out")
                     ≡ just (("%out" , val-native 0ᶠ) ∷ [])
mixed-byte-equality = refl

legacy-reverse : compute sample-mem (reverse-bytes (var "%bytes") "%out")
                 ≡ compute sample-mem (reverse (var "%bytes") "%out")
legacy-reverse = refl

-- FromBytes sends the entire integer to the reducing field decoder.
field-input-33 : ∀ b →
  from-bytes-value jubjub-scalar (replicate 33 b)
  ≡ just (val-jubjub-scalar (jubjubScalarFromBytes (replicate 33 b)))
field-input-33 b = refl

point-input-31 : ∀ b → from-bytes-value jubjub-point (replicate 31 b) ≡ nothing
point-input-31 b = refl

k1-identity-bytes : to-bytes-value (val-secp256k1-point idK1) ≡ just (replicate 33 zero)
k1-identity-bytes with idK1 ≟K1 idK1
... | yes _ = refl
... | no bad with () ← bad refl

p256-identity-bytes : from-bytes-value secp256r1-point (replicate 33 zero)
                     ≡ just (val-secp256r1-point idP)
p256-identity-bytes = refl

reconstitution-overflow : ∀ d r bits →
  FR-ORDER ≤ valFr r + 2 ^ bits * valFr d →
  compute ∅ (reconstitute-field (imm d) (imm r) bits "%out") ≡ nothing
reconstitution-overflow d r bits overflow
  with bits ≤? 248 | bits <? FR-BITS | FR-BITS ∸ bits <? FR-BITS
     | valFr r <? 2 ^ bits | valFr d <? 2 ^ (FR-BITS ∸ bits)
... | no _ | _ | _ | _ | _ = refl
... | yes _ | no _ | _ | _ | _ = refl
... | yes _ | yes _ | no _ | _ | _ = refl
... | yes _ | yes _ | yes _ | no _ | _ = refl
... | yes _ | yes _ | yes _ | yes _ | no _ = refl
... | yes _ | yes _ | yes _ | yes _ | yes _ with valFr r + 2 ^ bits * valFr d <? FR-ORDER
... | no _ = refl
... | yes below with () ← ≤⇒≯ overflow below

private
  empty-src : IrSource
  empty-src = mk-ir-source V0 [] [] false [] []

  empty-preimage : ProofPreimage
  empty-preimage = record
    { inputs = [] ; binding-input = 0ᶠ ; comm-commitment = nothing
    ; pub-transcript-inputs = [] ; pub-transcript-outputs = []
    ; priv-transcript = [] ; inner-proofs = [] }

  slots : List (List Byte) → State
  slots raw = record
    { mem = ∅ ; pis = 0ᶠ ∷ [] ; acc-pis = [] ; exposed = []
    ; pi-skips = [] ; pti-idx = 0 ; pto-rem = [] ; priv-rem = []
    ; proofs = λ _ → nothing ; proof-rem = raw ; inner-witnesses = []
    ; outs = [] }

blank-run : preprocess empty-src empty-preimage ≡ just (slots [])
blank-run = refl

-- The missing slot is rejected before the guard is read.
missing-slot : step empty-preimage empty-src (slots [])
                 (inner-proof (imm 0ᶠ) "%proof") ≡ nothing
missing-slot = refl

surplus-slot : ∀ raw → preprocess empty-src (record empty-preimage { inner-proofs = raw ∷ [] })
                       ≡ nothing
surplus-slot raw = refl

-- A false guard consumes a slot while replacing its contents by empty bytes.
inactive-slot : ∀ raw →
  map (λ st → State.proof-rem st , State.inner-witnesses st)
    (step empty-preimage empty-src (slots (raw ∷ [])) (inner-proof (imm 0ᶠ) "%proof"))
  ≡ just ([] , [] ∷ [])
inactive-slot raw with 0ᶠ ≟ᶠ 0ᶠ
... | yes _ = refl
... | no bad with () ← bad refl

-- Static checking compares guard operands, even when their runtime
-- values might happen to coincide.
mismatched-proof-guards :
  validate (record empty-src
    { instructions =
      inner-proof (var "%g") "%proof" ∷
      prepare-verification (var "%h") [] [] "%proof" "%acc" ∷
      verify-accumulator (var "%acc") ∷ [] })
  ≡ false
mismatched-proof-guards = refl

private
  zero-guard : to𝔹 0ᶠ ≡ just false
  zero-guard with 0ᶠ ≟ᶠ 0ᶠ
  ... | yes _ = refl
  ... | no bad with () ← bad refl

  one-guard : to𝔹 1ᶠ ≡ just true
  one-guard with 1ᶠ ≟ᶠ 0ᶠ
  ... | yes eq with () ← 1ᶠ≢0ᶠ eq
  one-guard | no _ with 1ᶠ ≟ᶠ 1ᶠ
  ... | yes _ = refl
  ... | no bad with () ← bad refl

  key-digest : List Byte → List Byte
  key-digest key = toList (sha256-bytes key)

  key-found : ∀ key → resolve-vk (key-digest key) (key ∷ []) ≡ just key
  key-found key with key-digest key ≟B key-digest key
  ... | yes _ = refl
  ... | no bad with () ← bad refl

  have-proof : List Byte → State
  have-proof blob = record (slots []) { proofs = insert-proof "%proof" blob (λ _ → nothing) }

  have-key : List Byte → IrSource
  have-key key = record empty-src { inner-vks = key ∷ [] }

guarded-off-preparation : ∀ key blob →
  prepare-result (have-key key) (have-proof blob) (imm 0ᶠ)
    (key-digest key) [] "%proof" ≡ just trivial-accumulator
guarded-off-preparation key blob rewrite zero-guard | key-found key = refl

guarded-off-still-resolves-instance : ∀ key blob →
  prepare-result (have-key key) (have-proof blob) (imm 0ᶠ)
    (key-digest key) (var "%missing" ∷ []) "%proof" ≡ nothing
guarded-off-still-resolves-instance key blob rewrite zero-guard = refl

guarded-on-preparation : ∀ key blob acc →
  key-well-formed key ≡ true →
  prepare-active key [] blob ≡ just acc →
  prepare-result (have-key key) (have-proof blob) (imm 1ᶠ)
    (key-digest key) [] "%proof" ≡ just acc
guarded-on-preparation key blob acc valid prepared
  rewrite one-guard | key-found key | valid = prepared

missing-key : validate (record empty-src
  { instructions = inner-proof (var "%g") "%proof" ∷
      prepare-verification (var "%g") [] [] "%proof" "%acc" ∷
      verify-accumulator (var "%acc") ∷ [] }) ≡ false
missing-key = refl

unused-key : ∀ key → validate (have-key key) ≡ false
unused-key key = refl

dropped-accumulator : validate (record empty-src { inputs = ("%acc" ⦂ accumulator) ∷ [] })
                      ≡ false
dropped-accumulator = refl

reused-accumulator : validate (record empty-src
  { inputs = ("%acc" ⦂ accumulator) ∷ []
  ; instructions = verify-accumulator (var "%acc") ∷ verify-accumulator (var "%acc") ∷ [] })
  ≡ false
reused-accumulator = refl

private
  have-accumulators : Accumulator → Accumulator → State
  have-accumulators a b = record (slots [])
    { mem = ins "%left" (val-accumulator a) (ins "%right" (val-accumulator b) ∅) }

  impact-exposure-order : List Instruction
  impact-exposure-order =
    impact (imm 0ᶠ) (var "%ignored" ∷ []) ∷
    verify-accumulator (var "%left") ∷
    impact (imm 1ᶠ) (imm 1ᶠ ∷ []) ∷
    verify-accumulator (var "%right") ∷ []

interleaved-public-inputs : ∀ a b →
  map (λ st → full-public-inputs st , State.pi-skips st)
    (run (record empty-preimage { pub-transcript-inputs = 1ᶠ ∷ [] })
      empty-src (have-accumulators a b) impact-exposure-order)
  ≡ just ((encode-accumulator a ++ encode-accumulator b) ++ (0ᶠ ∷ 0ᶠ ∷ 1ᶠ ∷ []) ,
          just 1 ∷ nothing ∷ [])
interleaved-public-inputs a b rewrite zero-guard | one-guard
  with (1ᶠ ∷ []) ≟LFr (1ᶠ ∷ [])
... | yes _ = refl
... | no bad with () ← bad refl

folded-public-inputs : ∀ a b result →
  fold-accumulators (a ∷ b ∷ []) ≡ just result →
  map (λ st → full-public-inputs st , State.exposed st)
    (run empty-preimage empty-src (have-accumulators a b)
      (accumulate (var "%left" ∷ var "%right" ∷ []) "%fold" ∷
       verify-accumulator (var "%fold") ∷ []))
  ≡ just (encode-accumulator result ++ (0ᶠ ∷ []) , result ∷ [])
folded-public-inputs a b result folded rewrite folded = refl


private
  sample-witness : C.CircuitWitness
  sample-witness = C.mk-witness ∅ [] 0ᶠ nothing []

  sample-circuit-state : C.CircuitState
  sample-circuit-state = C.mk-state ∅ (λ _ → nothing) [] [] (0ᶠ ∷ []) []

  wide-division : Fr → Instruction
  wide-division x = div-mod-power-of-two (imm x) 249 ("%div" ∷ "%mod" ∷ [])

wide-division-preprocess : ∀ x → compute ∅ (wide-division x) ≡ nothing
wide-division-preprocess x = refl

wide-division-circuit : ∀ x →
  map C.CircuitState.mem
    (C.stepᶜ empty-src sample-witness sample-circuit-state (C.lower (wide-division x)))
  ≡ just (ins "%mod" (val-native (from-le-bits (take 249 (to-le-bits x))))
           (ins "%div" (val-native (from-le-bits (drop 249 (to-le-bits x)))) ∅))
wide-division-circuit x = refl
