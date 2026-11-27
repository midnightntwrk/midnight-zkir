{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.WitnessExamples (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Circuit ⋯
open import zkir-v4.CircuitExtraction ⋯
open import zkir-v4.CircuitBridge ⋯ using (view; prepare-forward; guard-pass)
open import zkir-v4.CircuitReplay ⋯ using (ReplayTrace; next; end; inactive-impact)
open import zkir-v4.RunShape ⋯ using (ReadyRun; instr; impact-step) renaming (empty to ready-end)
open import zkir-v4.Operations ⋯ using (∅; _≟LFr_; resolve𝔹; ins; insert-proof; χ; to𝔹; _≟B_)
open import zkir-v4.Semantics ⋯ using (ProofPreimage; State; init; preprocess; decode-inputs; step; prepare-result)
open import zkir-v4.Syntax ⋯
open import zkir-v4.Types ⋯ using (native; val-native; val-accumulator)
open import zkir-v4.CircuitProof ⋯ using (honest-witness)
open import zkir-v4.Encoding ⋯ using (encode-accumulator)
open import zkir-v4.Validation ⋯ using (validate; resolve-vk)
open import zkir-v4.ProofSlots using (keep)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-identityʳ)
open import Data.Maybe using (just; nothing)
open import Data.Unit using (tt)
open import Data.Sum using (inj₂)
open import Data.Vec using (toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (yes; no)

-- An inactive impact emits a zero, consumes no transcript field and
-- still resolves its operand in the circuit. Both executions and the
-- extractor reduce on this source for every binding input and operand.
module SkippedImpact (binding operand : Fr) where
  src = mk-ir-source V0 [] [] false (impact (imm 0ᶠ) (imm operand ∷ []) ∷ []) []
  witness = mk-witness ∅ (binding ∷ 0ᶠ ∷ []) binding nothing []
  preimage : ProofPreimage
  preimage = record
    { inputs = [] ; binding-input = binding ; comm-commitment = nothing
    ; pub-transcript-inputs = [] ; pub-transcript-outputs = [] ; priv-transcript = [] ; inner-proofs = [] }
  circuit-final = mk-state ∅ (λ _ → nothing) [] [] (binding ∷ 0ᶠ ∷ []) []
  final : State
  final = record
    { mem = ∅ ; pis = binding ∷ 0ᶠ ∷ [] ; acc-pis = [] ; exposed = [] ; pi-skips = just 1 ∷ []
    ; pti-idx = 0 ; pto-rem = [] ; priv-rem = [] ; proofs = λ _ → nothing ; proof-rem = []
    ; inner-witnesses = [] ; outs = [] }

  accepted : preprocess src preimage ≡ just final
  accepted with 0ᶠ ≟ᶠ 0ᶠ
  ... | yes _ = refl
  ... | no ne with () ← ne refl

  satisfied : satisfies src witness circuit-final
  satisfied with 0ᶠ ≟ᶠ 0ᶠ
  ... | no ne with () ← ne refl
  satisfied | yes _ with (binding ∷ 0ᶠ ∷ []) ≟LFr (binding ∷ 0ᶠ ∷ [])
  ... | no ne with () ← ne refl
  ... | yes _ = refl

  extracted : extract src witness ≡ just preimage
  extracted rewrite satisfied with 0ᶠ ≟ᶠ 0ᶠ
  ... | yes _ = refl
  ... | no ne with () ← ne refl

  start : State
  start = record final { pis = binding ∷ [] ; pi-skips = [] }

  initialized : init src preimage ≡ just start
  initialized = refl

  inactive : resolve𝔹 ∅ (imm 0ᶠ) ≡ just false
  inactive with 0ᶠ ≟ᶠ 0ᶠ
  ... | yes _ = refl
  ... | no ne with () ← ne refl

  ready-shape : ReadyRun preimage src witness start [] (IrSource.instructions src) final []
  ready-shape = instr (impact-step inactive refl tt) ready-end

  -- This witness is in the domain of constructive replay even without
  -- preparation or codec laws.  The program has one instruction and
  -- a skipped public field, so the shape is exercised at a real step.
  replay-shape : ReplayTrace src witness (view start []) (IrSource.instructions src)
                              empty circuit-final
  replay-shape = next step-ok observed (inactive-impact inactive refl) end
    where
    step-ok : stepᶜ src witness (view start []) (lower (impact (imm 0ᶠ) (imm operand ∷ [])))
              ≡ just circuit-final
    step-ok rewrite inactive = refl
    observed : event (view start []) circuit-final (impact (imm 0ᶠ) (imm operand ∷ []))
               ≡ just empty
    observed rewrite inactive = refl

-- The fixed-key program in the reference's §7.2, parameterized by the
-- processed verifier key, proof bytes, and native fixture elements.
module OnePreparation (key proof-bytes : List Byte) (enabled : Bool)
                      (binding fixture : Fr) (expected : Accumulator) where
  private
    digest = toList (sha256-bytes key)
    guard = var "%guard"
    proof-name = "%p"
    acc-name = "%a"
    instances = fixture ∷ []
    guard-field = χ enabled
    stored-bytes = keep enabled proof-bytes

  src : IrSource
  src = mk-ir-source V0 (("%guard" ⦂ native) ∷ []) [] false
    (inner-proof guard proof-name ∷
     prepare-verification guard digest (imm fixture ∷ []) proof-name acc-name ∷
     verify-accumulator (var acc-name) ∷ []) (key ∷ [])

  preimage : ProofPreimage
  preimage = record
    { inputs = guard-field ∷ [] ; binding-input = binding ; comm-commitment = nothing
    ; pub-transcript-inputs = [] ; pub-transcript-outputs = [] ; priv-transcript = []
    ; inner-proofs = proof-bytes ∷ [] }

  final : State
  final = record
    { mem = ins acc-name (val-accumulator expected) (ins "%guard" (val-native guard-field) ∅)
    ; pis = binding ∷ [] ; acc-pis = encode-accumulator expected ; exposed = expected ∷ []
    ; pi-skips = [] ; pti-idx = 0 ; pto-rem = [] ; priv-rem = []
    ; proofs = insert-proof proof-name stored-bytes (λ _ → nothing)
    ; proof-rem = [] ; inner-witnesses = stored-bytes ∷ [] ; outs = [] }

  private
    guard-self : ∀ b → to𝔹 (χ b) ≡ just b
    guard-self false with 0ᶠ ≟ᶠ 0ᶠ
    ... | yes _ = refl
    ... | no ne with () ← ne refl
    guard-self true with 1ᶠ ≟ᶠ 0ᶠ
    ... | yes ne with () ← 1ᶠ≢0ᶠ ne
    guard-self true | no _ with 1ᶠ ≟ᶠ 1ᶠ
    ... | yes _ = refl
    ... | no ne with () ← ne refl

    key-valid : validate src ≡ true
    key-valid with digest ≟B digest
    ... | yes _ = refl
    ... | no ne with () ← ne refl

    key-found : resolve-vk digest (key ∷ []) ≡ just key
    key-found with digest ≟B digest
    ... | yes _ = refl
    ... | no ne with () ← ne refl

    decoded : decode-inputs (IrSource.inputs src) (ProofPreimage.inputs preimage)
              ≡ just (ins "%guard" (val-native guard-field) ∅)
    decoded with (guard-field ∷ []) ≟LFr (guard-field ∷ [])
    ... | yes _ = refl
    ... | no ne with () ← ne refl

  private
    start : State
    start = record final
      { mem = ins "%guard" (val-native guard-field) ∅ ; acc-pis = [] ; exposed = []
      ; proofs = λ _ → nothing ; proof-rem = proof-bytes ∷ [] ; inner-witnesses = [] }
    bound = record start
      { proofs = State.proofs final ; proof-rem = [] ; inner-witnesses = stored-bytes ∷ [] }
    carried = record bound { mem = State.mem final }

    initialized : init src preimage ≡ just start
    initialized rewrite decoded = refl

    guard-lookup : resolve𝔹 (State.mem start) guard ≡ just enabled
    guard-lookup = guard-self enabled

    bound-slot : step preimage src start (inner-proof guard proof-name) ≡ just bound
    bound-slot rewrite guard-lookup = refl

    prepared-off : key-well-formed key ≡ true
                 → (if enabled then prepare-active key instances stored-bytes
                              else just trivial-accumulator) ≡ just expected
                 → prepare-result src bound guard digest (imm fixture ∷ []) proof-name ≡ just expected
    prepared-off parsed prepared rewrite guard-lookup | key-found | parsed = prepared

    preparation : key-well-formed key ≡ true
                → (if enabled then prepare-active key instances stored-bytes
                             else just trivial-accumulator) ≡ just expected
                → step preimage src bound
                    (prepare-verification guard digest (imm fixture ∷ []) proof-name acc-name)
                    ≡ just carried
    preparation parsed prepared rewrite prepared-off parsed prepared = refl

  accepted : key-well-formed key ≡ true
           → (if enabled then prepare-active key instances stored-bytes
                       else just trivial-accumulator) ≡ just expected
           → preprocess src preimage ≡ just final
  accepted parsed prepared
    rewrite key-valid | initialized | bound-slot | preparation parsed prepared = refl

  -- Synthesis parses the key on both branches. The enabled flag and
  -- actual retained proof bytes are passed to the primitive gadget.
  satisfied : key-well-formed key ≡ true
            → prepare-circuit key instances stored-bytes enabled ≡ just expected
            → satisfies src (honest-witness preimage final) (view final [])
  satisfied parsed prepared =
    conclude-source
      where
      w = honest-witness preimage final
      initial = mk-state (ins "%guard" (val-native guard-field) ∅) (λ _ → nothing)
                         (stored-bytes ∷ []) [] (binding ∷ []) []
      after-slot = record initial { proofs = State.proofs final ; proof-rem = [] }
      after-prepare = record after-slot { mem = State.mem final }
      preparation-on :
        stepᶜ src w after-slot (lower (prepare-verification guard digest (imm fixture ∷ []) proof-name acc-name))
          ≡ just after-prepare
      preparation-on = prepare-forward src w after-slot guard digest (imm fixture ∷ []) proof-name acc-name
        enabled instances stored-bytes key expected (guard-self enabled) refl refl key-found parsed prepared
        (inj₂ refl)
      public-inputs : full-public-inputsᶜ (view final []) ≡ CircuitWitness.full-pis w
      public-inputs = cong (_++ (binding ∷ [])) (++-identityʳ (encode-accumulator expected))
      conclude-source : satisfies src w (view final [])
      conclude-source rewrite key-valid | preparation-on =
        guard-pass (full-public-inputsᶜ (view final []) ≟LFr CircuitWitness.full-pis w)
          public-inputs (just (view final []))
