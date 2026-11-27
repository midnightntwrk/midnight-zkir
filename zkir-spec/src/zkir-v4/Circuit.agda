{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.Circuit (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Types ⋯
open import zkir-v4.Syntax ⋯
open import zkir-v4.Encoding ⋯ using () renaming (encode to encode-value)
open import zkir-v4.Operations ⋯ hiding (write)
open import zkir-v4.Validation ⋯ using (validate; resolve-vk)

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; map; concatMap)
open import Data.Maybe using (Maybe; just; nothing; _>>=_; fromMaybe)
open import Data.Nat using (ℕ; _+_; _⊔_; _^_; _<?_; _≤?_)
open import Data.Nat.DivMod using (_%_)
open import Data.Product using (_×_; _,_)
open import Data.Vec using (toList)
open import Function using (case_of_; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (Dec; yes; no)

-- These are the supplied fields of the Rust Preprocessed witness used
-- by synthesis.  The public-input skips are prover metadata.
record CircuitWitness : Set where
  constructor mk-witness
  field
    assign          : Mem
    full-pis        : List Fr
    binding-input   : Fr
    comm-commitment : Maybe (Fr × Fr)
    inner-proofs    : List (List Byte)

record CircuitState : Set where
  constructor mk-state
  field
    mem       : Mem
    proofs    : Identifier → Maybe (List Byte)
    proof-rem : List (List Byte)
    accs      : List Accumulator
    pis       : List Fr
    outs      : List IrValue

accumulator-pisᶜ : CircuitState → List Fr
accumulator-pisᶜ st = concatMap (encode-value ∘ val-accumulator) (CircuitState.accs st)

full-public-inputsᶜ : CircuitState → List Fr
full-public-inputsᶜ st = accumulator-pisᶜ st ++ CircuitState.pis st

-- Aligned hash contracts use the circuit FAB parser.
data HashKind : Set where
  sha256 keccak sha-512 : HashKind

digestᶜ : HashKind → Alignment → List Fr → Maybe (List Byte)
digestᶜ sha256 a xs = persistent-hash-circuit-fn a xs >>= λ bs → just (toList bs)
digestᶜ keccak a xs = keccak-circuit-fn a xs >>= λ bs → just (toList bs)
digestᶜ sha-512 a xs = sha512-circuit-fn a xs >>= λ bs → just (toList bs)

-- A shared operation uses the same value computation in both passes.
-- The other constructors express circuit-specific checks and effects.
data Constraint : Set where
  shared           : Instruction → Constraint
  bounded-bits     : ℕ → Instruction → Constraint
  legacy-from-parts : Operand → Operand → Identifier → Constraint
  non-zero         : Operand → Constraint
  chip-select      : Operand → Operand → Operand → Identifier → Constraint
  chip-eq          : Operand → Operand → Maybe Identifier → Constraint
  chip-less-than   : Operand → Operand → ℕ → Identifier → Constraint
  aligned-hash     : HashKind → Alignment → List Operand → Identifier → Constraint
  witness-cell     : IrType → Identifier → Constraint
  publish-impact   : Operand → List Operand → Constraint
  record-output    : List Operand → Constraint
  bind-proof       : Identifier → Constraint
  prepare-proof    : Operand → List Byte → List Operand → Identifier → Identifier → Constraint
  fold-accs        : List Operand → Identifier → Constraint
  publish-acc      : Operand → Constraint

record Circuit : Set where
  constructor mk-circuit
  field
    source      : IrSource
    constraints : List Constraint

lower : Instruction → Constraint
lower i@(constrain-bits _ bits) = bounded-bits bits i
lower i@(div-mod-power-of-two _ bits _) = bounded-bits bits i
lower i@(reconstitute-field _ _ bits _) = bounded-bits bits i
lower (bytes32-from-low-high (lo , hi) out) = legacy-from-parts lo hi out
lower (assert cond) = non-zero cond
lower (cond-select bit a b out) = chip-select bit a b out
lower (constrain-eq a b) = chip-eq a b nothing
lower (test-eq a b out) = chip-eq a b (just out)
lower (less-than a b bits out) = chip-less-than a b bits out
lower (persistent-hash a ops out) = aligned-hash sha256 a ops out
lower (keccak256 a ops out) = aligned-hash keccak a ops out
lower (sha512 a ops out) = aligned-hash sha-512 a ops out
lower (public-input _ t out) = witness-cell t out
lower (private-input _ t out) = witness-cell t out
lower (impact g ops) = publish-impact g ops
lower (circuit-output ops) = record-output ops
lower (inner-proof _ id) = bind-proof id
lower (prepare-verification g hash ops proof out) = prepare-proof g hash ops proof out
lower (accumulate ops out) = fold-accs ops out
lower (verify-accumulator op) = publish-acc op
lower i = shared i

-- The pass builds a witness-independent constraint list after the
-- structural proof, accumulator and key-table checks.  Fixed-key
-- parsing and chip checks take place when the constraints are evaluated.
synth : IrSource → Maybe Circuit
synth src = if validate src
            then just (mk-circuit src (map lower (IrSource.instructions src)))
            else nothing

assign-value : IrType → IrValue → Maybe IrValue
assign-value t v = guardD (typeof v ≟T t) (just v)

-- Synthesis reads declared inputs from witness memory, using Native(0)
-- if an entry is absent.  Transcript assignments require an entry.
declared-value : CircuitWitness → Identifier → IrValue
declared-value w id = fromMaybe (val-native 0ᶠ) (CircuitWitness.assign w id)

declare : CircuitWitness → Mem → List TypedIdentifier → Maybe Mem
declare w m [] = just m
declare w m (ti ∷ ts) =
  let id = TypedIdentifier.name ti in
  assign-value (TypedIdentifier.val-t ti) (declared-value w id) >>= λ v →
  declare w (ins id v m) ts

initᶜ : IrSource → CircuitWitness → Maybe CircuitState
initᶜ src w =
  declare w ∅ (IrSource.inputs src) >>= λ m →
  let make = mk-state m (λ _ → nothing) (CircuitWitness.inner-proofs w) []
      b = CircuitWitness.binding-input w
  in if IrSource.do-communications-commitment src
     then (CircuitWitness.comm-commitment w >>= λ (c , _) → just (make (b ∷ c ∷ []) []))
     else just (make (b ∷ []) [])

-- The Rust witness diagnostic compares a computed cell with a supplied
-- entry if one exists.  For canonically encoded values, comparing the
-- type and encoding determines value equality.
check-assignment : CircuitWitness → Identifier → IrValue → Maybe IrValue
check-assignment w id v with CircuitWitness.assign w id
... | nothing = just v
... | just expected =
  guardD (typeof v ≟T typeof expected)
    (guardD (encode-value v ≟LFr encode-value expected) (just v))

write-cells : Bool → CircuitWitness → Mem → List (Identifier × IrValue) → Maybe Mem
write-cells _ w m [] = just m
write-cells checked w m ((id , v) ∷ vals) =
  (if checked then check-assignment w id v else just v) >>= λ cell →
  write-cells checked w (ins id cell m) vals

write : Bool → CircuitWitness → CircuitState → List (Identifier × IrValue) → Maybe CircuitState
write checked w st vals =
  write-cells checked w (CircuitState.mem st) vals >>= λ m →
  just (record st { mem = m })

write-one : CircuitWitness → CircuitState → Identifier → IrValue → Maybe CircuitState
write-one w st id v = write true w st ((id , v) ∷ [])

-- These shared arms use HashMap::insert directly.
check-shared-writes : Instruction → Bool
check-shared-writes (from-bytes _ _ _) = false
check-shared-writes (from-bytes32 _ _ _) = false
check-shared-writes (reverse _ _) = false
check-shared-writes (reverse-bytes _ _) = false
check-shared-writes (bytes32-into-low-high _ _) = false
check-shared-writes _ = true

select-supported : IrType → Bool
select-supported (bytes _) = false
select-supported accumulator = false
select-supported _ = true

even4 : ℕ → ℕ
even4 bits = (bits + bits % 2) ⊔ 4

-- Both equality gadgets require matching types, which for Bytes
-- includes the length.  compute's equality dispatch excludes accumulators.
chip-equality : Mem → Operand → Operand → Maybe Bool
chip-equality m a b =
  resolve m a >>= λ x →
  resolve m b >>= λ y →
  guardD (typeof x ≟T typeof y) (valEq? x y)

collect-outputs : Mem → List IrType → List Operand → Maybe (List IrValue)
collect-outputs _ [] [] = just []
collect-outputs m (t ∷ ts) (op ∷ ops) =
  resolve m op >>= assign-value t >>= λ v →
  collect-outputs m ts ops >>= λ vs →
  just (v ∷ vs)
collect-outputs _ _ _ = nothing

comparison-result : ∀ {P : Set} → (IrValue → Maybe CircuitState) → Dec P → Maybe CircuitState
comparison-result put (yes _) = put (val-native 1ᶠ)
comparison-result put (no _) = put (val-native 0ᶠ)

step-with : Bool → IrSource → CircuitWitness → CircuitState → Constraint → Maybe CircuitState
step-with diagnostics src w st c = execute c
  where
  m = CircuitState.mem st

  computed : Bool → List (Identifier × IrValue) → Maybe CircuitState
  computed checked = write (if diagnostics then checked else false) w st

  computed-one : Identifier → IrValue → Maybe CircuitState
  computed-one id v = computed true ((id , v) ∷ [])

  execute : Constraint → Maybe CircuitState
  execute (shared i) = compute m i >>= computed (check-shared-writes i)
  execute (bounded-bits bits i) =
    guardD (bits ≤? FR-BITS) (bounded-compute m i >>= computed true)
  execute (legacy-from-parts lo hi out) =
    resolveᶠ m hi >>= λ high →
    resolve m lo >>= λ low →
    bytes32-from-parts low (val-native high) >>= λ bs →
    computed false ((out , val-bytes bs) ∷ [])
  execute (non-zero op) =
    resolveᶠ m op >>= λ x →
    case x ≟ᶠ 0ᶠ of λ { (yes _) → nothing ; (no _) → just st }
  execute (chip-select bit a b out) =
    resolve𝔹 m bit >>= λ g →
    resolve m a >>= λ x →
    resolve m b >>= λ y →
    guardD (typeof x ≟T typeof y)
      (if select-supported (typeof x)
       then computed-one out (if g then x else y)
       else nothing)
  execute (chip-eq a b nothing) =
    chip-equality m a b >>= λ g →
    if g then just st else nothing
  execute (chip-eq a b (just out)) =
    chip-equality m a b >>= λ g →
    computed-one out (val-native (χ g))
  execute (chip-less-than a b bits out) =
    resolveᶠ m a >>= λ x →
    resolveᶠ m b >>= λ y →
    guardD (valFr x <? 2 ^ even4 bits)
      (guardD (valFr y <? 2 ^ even4 bits)
        (comparison-result (computed-one out) (valFr x <? valFr y)))
  execute (aligned-hash kind alignment ops out) =
    resolve-all-Fr m ops >>= λ xs →
    digestᶜ kind alignment xs >>= λ bs →
    computed-one out (val-bytes bs)
  execute (witness-cell t id) =
    CircuitWitness.assign w id >>= assign-value t >>= λ v →
    write diagnostics w st ((id , v) ∷ [])
  execute (publish-impact g ops) =
    resolve𝔹 m g >>= λ active →
    resolve-all-Fr m ops >>= λ xs →
    let values = if active then xs else map (λ _ → 0ᶠ) ops in
    just (record st { pis = CircuitState.pis st ++ values })
  execute (record-output ops) =
    collect-outputs m (IrSource.outputs src) ops >>= λ vs →
    just (record st { outs = CircuitState.outs st ++ vs })
  execute (bind-proof id) with CircuitState.proof-rem st
  ... | [] = nothing
  ... | bs ∷ rest =
    just (record st { proofs = insert-proof id bs (CircuitState.proofs st)
                    ; proof-rem = rest })
  execute (prepare-proof g hash ops id out) =
    resolve𝔹 m g >>= λ active →
    resolve-all-Fr m ops >>= λ instance-values →
    CircuitState.proofs st id >>= λ bytes →
    resolve-vk hash (IrSource.inner-vks src) >>= λ vk →
    if key-well-formed vk
    then (prepare-circuit vk instance-values bytes active >>= λ acc →
          computed-one out (val-accumulator acc))
    else nothing
  execute (fold-accs ops out) =
    resolve-accs m ops >>= λ where
      accs@(_ ∷ _ ∷ _) →
        fold-accumulators accs >>= λ acc →
        computed-one out (val-accumulator acc)
      _ → nothing
  execute (publish-acc op) =
    resolve-acc m op >>= λ acc →
    just (record st { accs = CircuitState.accs st ++ (acc ∷ []) })

stepᶜ : IrSource → CircuitWitness → CircuitState → Constraint → Maybe CircuitState
stepᶜ = step-with true

run-with : Bool → IrSource → CircuitWitness → CircuitState → List Constraint → Maybe CircuitState
run-with diagnostics src w st [] = just st
run-with diagnostics src w st (c ∷ cs) =
  step-with diagnostics src w st c >>= λ st′ → run-with diagnostics src w st′ cs

runᶜ : IrSource → CircuitWitness → CircuitState → List Constraint → Maybe CircuitState
runᶜ = run-with true

-- The communications gadget reads declared names from final circuit
-- memory and commits to their encodings followed by typed outputs.
encode-inputs : Mem → List TypedIdentifier → List Fr
encode-inputs _ [] = []
encode-inputs m (ti ∷ ts) with m (TypedIdentifier.name ti)
... | nothing = encode-inputs m ts
... | just v  = encode-value v ++ encode-inputs m ts

encode-outputs : CircuitState → List Fr
encode-outputs st = concatMap encode-value (CircuitState.outs st)

finish-commitment : IrSource → CircuitWitness → CircuitState → Maybe CircuitState
finish-commitment src w st =
  if IrSource.do-communications-commitment src
  then (CircuitWitness.comm-commitment w >>= λ (c , r) →
       guardD
         (c ≟ᶠ transient-commit
           (encode-inputs (CircuitState.mem st) (IrSource.inputs src)
             ++ encode-outputs st) r)
         (just st))
  else just st

finishᶜ : IrSource → CircuitWitness → CircuitState → Maybe CircuitState
finishᶜ src w st =
  guardD (full-public-inputsᶜ st ≟LFr CircuitWitness.full-pis w)
    (finish-commitment src w st)

check-witness-with : Bool → Circuit → CircuitWitness → Maybe CircuitState
check-witness-with diagnostics (mk-circuit src constraints) w =
  initᶜ src w >>= λ st →
  run-with diagnostics src w st constraints >>= finishᶜ src w

check-witness : Circuit → CircuitWitness → Maybe CircuitState
check-witness = check-witness-with true

check-with : Bool → IrSource → CircuitWitness → Maybe CircuitState
check-with diagnostics src w = synth src >>= λ c → check-witness-with diagnostics c w

check-circuit : IrSource → CircuitWitness → Maybe CircuitState
check-circuit = check-with true

-- The two blocks are produced by the constraint run before concatenation.
satisfies : IrSource → CircuitWitness → CircuitState → Set
satisfies src w st = check-circuit src w ≡ just st

-- The chip relations use the same assigned inputs, proof slots and public
-- checks in both modes.  Computed-value diagnostics are disabled here.
satisfies-constraints : IrSource → CircuitWitness → CircuitState → Set
satisfies-constraints src w st = check-with false src w ≡ just st
