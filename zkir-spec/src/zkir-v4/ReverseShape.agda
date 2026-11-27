{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.ReverseShape (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Syntax ⋯
open import zkir-v4.Types ⋯
open import zkir-v4.Circuit ⋯
open import zkir-v4.CircuitBridge ⋯ using (view; witness-cell-backward)
open import zkir-v4.CircuitBackward ⋯
open import zkir-v4.CircuitClosedEffects ⋯
open import zkir-v4.CircuitEffects ⋯ using (PreparationBackward)
open import zkir-v4.CircuitEvents ⋯
open import zkir-v4.CircuitExtraction ⋯
open import zkir-v4.CircuitInputs ⋯ using (ValidDeclarations)
open import zkir-v4.CircuitProperties ⋯ using (Trace; SatisfiedRun; satisfying-run)
open import zkir-v4.CircuitReplay ⋯
open import zkir-v4.Encoding ⋯ using () renaming (encode to encode-value)
open import zkir-v4.EncodingProperties ⋯ using (EncodingLaws)
open import zkir-v4.Operations ⋯ using (eval-guard; resolve𝔹; resolve-all-Fr; default-val)
open import zkir-v4.ProofSlots using (keep)
open import zkir-v4.Semantics ⋯ using (ProofPreimage; State; preprocess; ins; insert-proof)
open import zkir-v4.StatementSoundness ⋯ using (WitnessShape)
open import zkir-v4.SynthesisDomains ⋯

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)

-- A disabled source read still has a circuit cell.  In that branch
-- its value must equal the default used by preprocessing.
ReadResidual : CircuitWitness → CircuitState → Maybe Operand → IrType → Identifier → Set
ReadResidual w st g t id = Σ Bool λ active →
  (eval-guard (CircuitState.mem st) g ≡ just active) ×
  (if active then valid-type t ≡ true else CircuitWitness.assign w id ≡ just (default-val t))

read-always-active : ∀ w st g t id
                   → eval-guard (CircuitState.mem st) g ≡ just true → valid-type t ≡ true
                   → ReadResidual w st g t id
read-always-active w st g t id bit valid = true , bit , valid

immediate-true : ∀ st → resolve𝔹 (CircuitState.mem st) (imm 1ᶠ) ≡ just true
immediate-true st with 1ᶠ ≟ᶠ 0ᶠ
... | yes equal = ⊥-elim (1ᶠ≢0ᶠ equal)
... | no _ with 1ᶠ ≟ᶠ 1ᶠ
...   | yes _ = refl
...   | no different = ⊥-elim (different refl)

-- The circuit consumes the slot even when the source guard is false.
-- In that branch its bytes must agree with the canonical empty slot.
SlotResidual : CircuitState → Operand → Set
SlotResidual st g = Σ Bool λ active →
  (resolve𝔹 (CircuitState.mem st) g ≡ just active) ×
  (∀ {blob tail} → CircuitState.proof-rem st ≡ blob ∷ tail → keep active blob ≡ blob)

slot-always-active : ∀ st g → resolve𝔹 (CircuitState.mem st) g ≡ just true → SlotResidual st g
slot-always-active st g bit = true , bit , λ _ → refl

private
  data Form : Instruction → Set where
    pure-form : ∀ {i} → PureInstruction i → Form i
    closed-form : ∀ {i} → ClosedEffect i → Form i
    impact-form : ∀ {g ops} → Form (impact g ops)
    public-form : ∀ {g t id} → Form (public-input g t id)
    private-form : ∀ {g t id} → Form (private-input g t id)
    slot-form : ∀ {g id} → Form (inner-proof g id)

  form : (i : Instruction) → Form i
  form (encode _ _) = pure-form (ordinary refl)
  form (assert _) = pure-form assertion-form
  form (cond-select _ _ _ _) = pure-form selection-form
  form (constrain-bits _ _) = pure-form bit-form
  form (constrain-eq _ _) = pure-form equality-constraint-form
  form (constrain-to-boolean _) = pure-form (ordinary refl)
  form (copy _ _) = pure-form (ordinary refl)
  form (impact _ _) = impact-form
  form (ec-mul _ _ _) = pure-form (ordinary refl)
  form (ec-mul-generator _ _) = pure-form (ordinary refl)
  form (hash-to-curve _ _) = pure-form (ordinary refl)
  form (into-coordinates _ _) = pure-form (ordinary refl)
  form (from-coordinates _ _) = pure-form (ordinary refl)
  form (into-bytes32 _ _) = pure-form (ordinary refl)
  form (from-bytes32 _ _ _) = pure-form (ordinary refl)
  form (reverse-bytes _ _) = pure-form (ordinary refl)
  form (bytes32-into-low-high _ _) = pure-form (ordinary refl)
  form (bytes32-from-low-high (_ , _) _) = pure-form parts-form
  form (div-mod-power-of-two _ _ _) = pure-form division-form
  form (reconstitute-field _ _ _ _) = pure-form reconstitution-form
  form (transient-hash _ _) = pure-form (ordinary refl)
  form (persistent-hash _ _ _) = pure-form persistent-form
  form (keccak256 _ _ _) = pure-form keccak-hash-form
  form (test-eq _ _ _) = pure-form equality-test-form
  form (add _ _ _) = pure-form (ordinary refl)
  form (mul _ _ _) = pure-form (ordinary refl)
  form (neg _ _) = pure-form (ordinary refl)
  form (inv _ _) = pure-form (ordinary refl)
  form (not _ _) = pure-form (ordinary refl)
  form (less-than _ _ _ _) = pure-form comparison-form
  form (jubjub-scalar-from-native _ _) = pure-form (ordinary refl)
  form (public-input _ _ _) = public-form
  form (private-input _ _ _) = private-form
  form (circuit-output _) = closed-form output-effect
  form (slice _ _ _ _) = pure-form (ordinary refl)
  form (nth _ _ _) = pure-form (ordinary refl)
  form (concat _ _) = pure-form (ordinary refl)
  form (reverse _ _) = pure-form (ordinary refl)
  form (load-constant _ _ _) = pure-form (ordinary refl)
  form (sha512 _ _ _) = pure-form sha-hash-form
  form (and _ _) = pure-form (ordinary refl)
  form (or _ _) = pure-form (ordinary refl)
  form (xor _ _) = pure-form (ordinary refl)
  form (to-bytes _ _) = pure-form (ordinary refl)
  form (from-bytes _ _ _) = pure-form (ordinary refl)
  form (bytes-into-natives _ _) = pure-form (ordinary refl)
  form (bytes-from-natives _ _ _) = pure-form (ordinary refl)
  form (inner-proof _ _) = slot-form
  form (prepare-verification _ _ _ _ _) = closed-form prepare-effect
  form (accumulate _ _) = closed-form fold-effect
  form (verify-accumulator _) = closed-form expose-effect

  residual : ∀ {i} → CircuitWitness → CircuitState → Form i → Set
  residual w st (pure-form {i} _) = PureResidual (CircuitState.mem st) i
  residual w st (closed-form _) = ⊤
  residual w st impact-form = ⊤
  residual w st (public-form {g} {t} {id}) = ReadResidual w st g t id
  residual w st (private-form {g} {t} {id}) = ReadResidual w st g t id
  residual w st (slot-form {g}) = SlotResidual st g

-- These conditions concern one instruction's unchecked behavior at the
-- circuit memory where it executes.  They contain no execution trace.
CircuitResidual : CircuitWitness → CircuitState → Instruction → Set
CircuitResidual w st i = residual w st (form i)

private
  unbind : ∀ {A B : Set} (x : Maybe A) (f : A → Maybe B) {y}
         → (x >>= f) ≡ just y → Σ A λ v → (x ≡ just v) × (f v ≡ just y)
  unbind nothing _ ()
  unbind (just v) _ ok = v , refl , ok

  Origin : CircuitWitness → CircuitState → CircuitState → Instruction → Set
  Origin w st after i =
    Σ Fragment λ local → (event st after i ≡ just local)
                      × ReplayAction w (CircuitState.mem st) (CircuitState.proof-rem st) i local

  pure-event : ∀ {m i} → PureAdmissible m i → Eventless i
  pure-event (common-op {i} lowering) = common-eventless i lowering
  pure-event (bit-constraint-op _) _ _ = refl
  pure-event (division-op _) _ _ = refl
  pure-event (reconstitution-op _) _ _ = refl
  pure-event (special-op support) = special-eventless support

  closed-event : ∀ {i} → ClosedEffect i → Eventless i
  closed-event prepare-effect _ _ = refl
  closed-event fold-effect _ _ = refl
  closed-event expose-effect _ _ = refl
  closed-event output-effect _ _ = refl

  derive-origin : ∀ src w st after i (f : Form i)
                → residual w st f
                → stepᶜ src w st (lower i) ≡ just after
                → Origin w st after i
  derive-origin src w st after i (pure-form p) allowed accepted =
    empty , pure-event admissible st after , pure admissible
    where admissible = pure-domain src w st i p allowed accepted
  derive-origin src w st after i (closed-form c) _ _ =
    empty , closed-event c st after , closed c
  derive-origin src w st after (impact g ops) impact-form _ accepted
    with unbind (resolve𝔹 (CircuitState.mem st) g) _ accepted
  ... | true , bit , rest
    with unbind (resolve-all-Fr (CircuitState.mem st) ops) _ rest
  ...   | values , resolved , _ =
    record empty { impacts = values } , observed , active-impact bit resolved
    where
    observed : event st after (impact g ops) ≡ just (record empty { impacts = values })
    observed rewrite bit | resolved = refl
  derive-origin src w st after (impact g ops) impact-form _ accepted
    | false , bit , rest
    with unbind (resolve-all-Fr (CircuitState.mem st) ops) _ rest
  ... | values , resolved , _ = empty , observed , inactive-impact bit resolved
    where
    observed : event st after (impact g ops) ≡ just empty
    observed rewrite bit = refl
  derive-origin src w st after (public-input g t id) public-form (true , bit , admissible) accepted
    with witness-cell-backward src w st t id accepted
  ... | v , _ , _ , refl =
    record empty { public-reads = encode-value v } , observed , active-public {v = v} bit admissible
    where
    observed : event st (record st { mem = ins id v (CircuitState.mem st) }) (public-input g t id)
             ≡ just (record empty { public-reads = encode-value v })
    observed rewrite bit | inserted-value id v (CircuitState.mem st) = refl
  derive-origin src w st after (public-input g t id) public-form (false , bit , defaulted) _ =
    empty , observed , inactive-public bit defaulted
    where
    observed : event st after (public-input g t id) ≡ just empty
    observed rewrite bit = refl
  derive-origin src w st after (private-input g t id) private-form (true , bit , admissible) accepted
    with witness-cell-backward src w st t id accepted
  ... | v , _ , _ , refl =
    record empty { private-reads = encode-value v } , observed , active-private {v = v} bit admissible
    where
    observed : event st (record st { mem = ins id v (CircuitState.mem st) }) (private-input g t id)
             ≡ just (record empty { private-reads = encode-value v })
    observed rewrite bit | inserted-value id v (CircuitState.mem st) = refl
  derive-origin src w st after (private-input g t id) private-form (false , bit , defaulted) _ =
    empty , observed , inactive-private bit defaulted
    where
    observed : event st after (private-input g t id) ≡ just empty
    observed rewrite bit = refl
  derive-origin src w st after (inner-proof g id) slot-form (active , bit , normal) accepted
    with CircuitState.proof-rem st
  ... | [] with () ← accepted
  derive-origin src w st after (inner-proof g id) slot-form (active , bit , normal) accepted
    | blob ∷ tail with refl ← just-injective accepted =
    record empty { proofs = blob ∷ [] } , observed , inner-slot bit refl (normal refl)
    where
    observed : event st (record st
                          { proofs = insert-proof id blob (CircuitState.proofs st)
                          ; proof-rem = tail }) (inner-proof g id)
             ≡ just (record empty { proofs = blob ∷ [] })
    observed rewrite bit | inserted-proof id blob (CircuitState.proofs st) | normal refl = refl

Along : ∀ {src st target} w is → Trace src w st (map lower is) target → Set
Along w [] Trace.end = ⊤
Along {st = st} w (i ∷ is) (Trace.next _ rest) = CircuitResidual w st i × Along w is rest

-- A source-side restriction can establish each local condition without
-- referring to any particular execution.
source-along : ∀ {src st target w is}
             → All (λ i → ∀ before → CircuitResidual w before i) is
             → (path : Trace src w st (map lower is) target) → Along w is path
source-along [] Trace.end = tt
source-along {st = st} (local ∷ later) (Trace.next _ rest) = local st , source-along later rest

reconstruct-trace : ∀ src w st is target
                  → (path : Trace src w st (map lower is) target)
                  → Along w is path
                  → Σ Fragment λ streams → ReplayTrace src w st is streams target
reconstruct-trace src w st [] .st Trace.end _ = empty , end
reconstruct-trace src w st (i ∷ is) target (Trace.next {st′ = after} step-ok rest) (local , later)
  with derive-origin src w st after i (form i) local step-ok
     | reconstruct-trace src w after is target rest later
... | first , observed , action | suffix , trace =
  append first suffix , next step-ok observed action trace

StableInputs : IrSource → CircuitState → CircuitState → Set
StableInputs src start target = IrSource.do-communications-commitment src ≡ true →
  encode-inputs (CircuitState.mem target) (IrSource.inputs src) ≡
  encode-inputs (CircuitState.mem start) (IrSource.inputs src)

derive-shape : ∀ src w target (checked : SatisfiedRun src w target)
             → Along w (IrSource.instructions src) (SatisfiedRun.path checked)
             → StableInputs src (SatisfiedRun.start checked) target
             → WitnessShape src w target
derive-shape src w target checked local stable
  with reconstruct-trace src w _ (IrSource.instructions src) target (SatisfiedRun.path checked) local
... | streams , trace = record
  { start = SatisfiedRun.start checked
  ; streams = streams
  ; initialized = SatisfiedRun.initialized checked
  ; path = trace
  ; input-stability = stable
  }

reverse-complete : EncodingLaws → PreparationBackward
                 → ∀ src w target (accepted : satisfies src w target)
                 → ValidDeclarations (IrSource.inputs src)
                 → let checked = satisfying-run src w target accepted in
                   Along w (IrSource.instructions src) (SatisfiedRun.path checked)
                   → StableInputs src (SatisfiedRun.start checked) target
                   → Σ ProofPreimage λ p → Σ State λ final →
                       (extract src w ≡ just p) × (preprocess src p ≡ just final)
                       × (view final (CircuitState.proof-rem target) ≡ target)
reverse-complete encoding prepare src w target accepted declarations local stable =
  extraction-complete-using encoding prepare src w _ target _ (SatisfiedRun.validated checked)
    declarations (WitnessShape.initialized shape) accepted (WitnessShape.path shape)
    (WitnessShape.input-stability shape)
  where
  checked = satisfying-run src w target accepted
  shape = derive-shape src w target checked local stable
