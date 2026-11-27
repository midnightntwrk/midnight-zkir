{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.GuardedExamples (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Types ⋯
open import zkir-v4.Syntax ⋯
open import zkir-v4.Semantics ⋯ using (ProofPreimage; State; preprocess; Mem; ∅; ins; to𝔹; χ; _≟B_; _≟LFr_; resolve𝔹; ProofStore)
open import zkir-v4.Circuit ⋯
open import zkir-v4.CircuitBridge ⋯ using (write-backward)
open import zkir-v4.CircuitEffects ⋯ using (PreparationBackward)
open import zkir-v4.CircuitProperties ⋯ using (Trace; next; end; SatisfiedRun; satisfying-run)
open import zkir-v4.Encoding ⋯ using (decode; low-bits)
open import zkir-v4.ReverseShape ⋯ using (immediate-true)
open import zkir-v4.Validation ⋯ using (validate; resolve-vk)
open import zkir-v4.ProofSlots as Slots using (keep; Canonical)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ)
open import Data.Product using (∃; _×_; _,_)
import Data.Vec.Base as Vec
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Relation.Nullary using (Dec; yes; no; does)

private
  one-bit : to𝔹 1ᶠ ≡ just true
  one-bit = immediate-true (mk-state ∅ (λ _ → nothing) [] [] [] [])

  zero-bit : to𝔹 0ᶠ ≡ just false
  zero-bit with 0ᶠ ≟ᶠ 0ᶠ
  ... | yes _ = refl
  ... | no neq = ⊥-elim (neq refl)

  bit-value : ∀ x b → to𝔹 x ≡ just b → x ≡ χ b
  bit-value x b ok with x ≟ᶠ 0ᶠ
  ... | yes equal with refl ← just-injective ok = equal
  bit-value x b ok | no _ with x ≟ᶠ 1ᶠ
  ... | yes equal with refl ← just-injective ok = equal
  bit-value x b ok | no _ | no _ with () ← ok

  accepts-test : ∀ {A : Set} (d : Dec A) → A → does d ≡ true
  accepts-test (yes _) _ = refl
  accepts-test (no reject) proof = ⊥-elim (reject proof)

  input-memory : Fr → Mem
  input-memory x = ins "%guard" (val-native x) ∅

  install : CircuitState → Identifier → Accumulator → CircuitState
  install st id a = record st { mem = ins id (val-accumulator a) (CircuitState.mem st) }

  start-state : CircuitWitness → Fr → CircuitState
  start-state w x = mk-state (input-memory x) (λ _ → nothing)
    (CircuitWitness.inner-proofs w) [] (CircuitWitness.binding-input w ∷ []) []

  guard-op = var "%guard"
  always = imm 1ᶠ

-- The field parameters stand for the four literals in §§7.2–7.3.
-- A witness supplies the declared guard, binding input and proof slots.
module Examples (key : List Byte) (instance-value first-impact left-impact right-impact : Fr) where

  digest = Vec.toList (sha256-bytes key)
  table = key ∷ []
  inner-instance = instance-value ∷ []
  inner-operands = imm instance-value ∷ []

  one-source : IrSource
  one-source = mk-ir-source V0 ("%guard" ⦂ native ∷ []) [] false
    (inner-proof guard-op "%p" ∷
     prepare-verification guard-op digest inner-operands "%p" "%a" ∷
     verify-accumulator (var "%a") ∷ []) table

  fold-source : IrSource
  fold-source = mk-ir-source V0 ("%guard" ⦂ native ∷ []) [] false
    (inner-proof always "%p" ∷
     prepare-verification always digest inner-operands "%p" "%a" ∷
     impact always (imm first-impact ∷ []) ∷
     inner-proof guard-op "%q" ∷
     prepare-verification guard-op digest inner-operands "%q" "%b" ∷
     accumulate (var "%a" ∷ var "%b" ∷ []) "%c" ∷
     verify-accumulator (var "%c") ∷
     impact guard-op (imm left-impact ∷ imm right-impact ∷ []) ∷ []) table

  private
    self-test = accepts-test (digest ≟B digest) refl

    found-key : resolve-vk digest table ≡ just key
    found-key with digest ≟B digest
    ... | yes _ = refl
    ... | no neq = ⊥-elim (neq refl)

  one-valid : validate one-source ≡ true
  one-valid rewrite self-test = refl

  fold-valid : validate fold-source ≡ true
  fold-valid rewrite accepts-test (1ᶠ ≟ᶠ 1ᶠ) refl | self-test = refl

  one-statement : Fr → List Fr
  one-statement binding = binding ∷ []

  fold-impacts : Bool → List Fr
  fold-impacts false = first-impact ∷ []
  fold-impacts true = first-impact ∷ left-impact ∷ right-impact ∷ []

  fold-statement : Fr → Bool → List Fr
  fold-statement binding false = binding ∷ first-impact ∷ 0ᶠ ∷ 0ᶠ ∷ []
  fold-statement binding true = binding ∷ first-impact ∷ left-impact ∷ right-impact ∷ []

  private
    initial : ∀ src w → IrSource.inputs src ≡ ("%guard" ⦂ native ∷ [])
      → IrSource.do-communications-commitment src ≡ false
      → ∀ {start} → initᶜ src w ≡ just start
      → ∃ λ guard → (declared-value w "%guard" ≡ val-native guard) × start ≡ start-state w guard
    initial src w refl refl ok with declared-value w "%guard"
    ... | val-native x = x , refl , sym (just-injective ok)
    ... | val-bool _ with () ← ok
    ... | val-byte _ with () ← ok
    ... | val-bytes _ with () ← ok
    ... | val-jubjub-point _ with () ← ok
    ... | val-jubjub-scalar _ with () ← ok
    ... | val-secp256k1-point _ with () ← ok
    ... | val-secp256k1-base _ with () ← ok
    ... | val-secp256k1-scalar _ with () ← ok
    ... | val-secp256r1-point _ with () ← ok
    ... | val-secp256r1-base _ with () ← ok
    ... | val-secp256r1-scalar _ with () ← ok
    ... | val-curve25519-point _ with () ← ok
    ... | val-curve25519-base _ with () ← ok
    ... | val-curve25519-scalar _ with () ← ok
    ... | val-accumulator _ with () ← ok

    read-preparation : ∀ src w st g name out blob {after}
      → CircuitState.proofs st name ≡ just blob
      → IrSource.inner-vks src ≡ table
      → stepᶜ src w st (prepare-proof g digest inner-operands name out) ≡ just after
      → ∃ λ active → ∃ λ a → resolve𝔹 (CircuitState.mem st) g ≡ just active
        × key-well-formed key ≡ true
        × prepare-circuit key inner-instance blob active ≡ just a
        × after ≡ install st out a
    read-preparation src w st g name out blob slot table-ok accepted
      rewrite slot | table-ok | found-key with resolve𝔹 (CircuitState.mem st) g
    ... | nothing with () ← accepted
    read-preparation src w st g name out blob slot table-ok accepted | just active
      with key-well-formed key
    ... | false with () ← accepted
    read-preparation src w st g name out blob slot table-ok accepted | just active | true
      with prepare-circuit key inner-instance blob active in prepared
    ... | nothing with () ← accepted
    ... | just a = active , a , refl , refl , prepared ,
        write-backward true w st ((out , val-accumulator a) ∷ []) accepted

    record OneRun (w : CircuitWitness) (target : CircuitState) : Set where
      constructor one-run
      field
        active : Bool
        raw : List Byte
        a : Accumulator
        guard-value : declared-value w "%guard" ≡ val-native (χ active)
        parsed : key-well-formed key ≡ true
        prepared : prepare-circuit key inner-instance raw active ≡ just a
        carried : CircuitState.accs target ≡ a ∷ []
        statement : CircuitState.pis target ≡ one-statement (CircuitWitness.binding-input w)

    one-walk : ∀ w x slots {target} →
      declared-value w "%guard" ≡ val-native x →
      Trace one-source w (record (start-state w x) { proof-rem = slots })
        (map lower (IrSource.instructions one-source)) target → OneRun w target
    one-walk w x [] from-witness (next () _)
    one-walk w x (raw ∷ _) from-witness (next refl (next {st = before} ok rest))
      with read-preparation one-source w before guard-op "%p" "%a" raw refl refl ok
    ... | active , a , guard-ok , parsed , prepared , refl
      with next refl end ← rest =
      one-run active raw a (trans from-witness (cong val-native (bit-value x active guard-ok)))
        parsed prepared refl refl

    one-observe : ∀ w target → satisfies one-source w target → OneRun w target
    one-observe w target ok with satisfying-run one-source w target ok
    ... | record { initialized = init-ok ; path = path }
      with initial one-source w refl refl init-ok
    ... | x , actual , refl = one-walk w x _ actual path

    record FoldRun (w : CircuitWitness) (target : CircuitState) : Set where
      constructor fold-run
      field
        active : Bool
        raw-first raw-second : List Byte
        a b carried-acc : Accumulator
        guard-value : declared-value w "%guard" ≡ val-native (χ active)
        parsed : key-well-formed key ≡ true
        prepared-first : prepare-circuit key inner-instance raw-first true ≡ just a
        prepared-second : prepare-circuit key inner-instance raw-second active ≡ just b
        folded : fold-accumulators (a ∷ b ∷ []) ≡ just carried-acc
        carried : CircuitState.accs target ≡ carried-acc ∷ []
        statement : CircuitState.pis target ≡ fold-statement (CircuitWitness.binding-input w) active

    finish-fold : ∀ w x slots raw-first raw-second a b active
      (proofs : ProofStore) {target} →
      let before = mk-state (ins "%b" (val-accumulator b) (ins "%a" (val-accumulator a) (input-memory x)))
                     proofs slots [] (CircuitWitness.binding-input w ∷ first-impact ∷ []) []
      in declared-value w "%guard" ≡ val-native x
      → to𝔹 x ≡ just active
      → key-well-formed key ≡ true
      → prepare-circuit key inner-instance raw-first true ≡ just a
      → prepare-circuit key inner-instance raw-second active ≡ just b
      → Trace fold-source w before
          (fold-accs (var "%a" ∷ var "%b" ∷ []) "%c" ∷
           publish-acc (var "%c") ∷
           publish-impact guard-op (imm left-impact ∷ imm right-impact ∷ []) ∷ []) target
      → FoldRun w target
    finish-fold w x slots p q a b active proofs actual bit-ok parsed first second
      (next {st = before} folded rest)
      with fold-accumulators (a ∷ b ∷ []) in fold-ok
    ... | nothing with () ← folded
    ... | just c
      with refl ← write-backward true w before (("%c" , val-accumulator c) ∷ []) folded
      with next refl (next impact-ok end) ← rest
      with active | bit-ok | second
    ... | false | bit-false | second-false rewrite bit-false
      with refl ← just-injective impact-ok =
        fold-run false p q a b c (trans actual (cong val-native (bit-value x false bit-false)))
          parsed first second-false fold-ok refl refl
    ... | true | bit-true | second-true rewrite bit-true
      with refl ← just-injective impact-ok =
        fold-run true p q a b c (trans actual (cong val-native (bit-value x true bit-true)))
          parsed first second-true fold-ok refl refl

    second-walk : ∀ w x p a slots (proofs : ProofStore) {target} →
      let before = mk-state (ins "%a" (val-accumulator a) (input-memory x))
                     proofs slots [] (CircuitWitness.binding-input w ∷ first-impact ∷ []) []
      in declared-value w "%guard" ≡ val-native x
      → prepare-circuit key inner-instance p true ≡ just a
      → Trace fold-source w before
          (map lower (inner-proof guard-op "%q" ∷
            prepare-verification guard-op digest inner-operands "%q" "%b" ∷
            accumulate (var "%a" ∷ var "%b" ∷ []) "%c" ∷
            verify-accumulator (var "%c") ∷
            impact guard-op (imm left-impact ∷ imm right-impact ∷ []) ∷ [])) target
      → FoldRun w target
    second-walk w x p a [] proofs actual first (next () _)
    second-walk w x p a (q ∷ later) proofs actual first
      (next refl (next {st = before} ok rest))
      with read-preparation fold-source w before guard-op "%q" "%b" q refl refl ok
    ... | active , b , bit-ok , parsed , second , refl =
      finish-fold w x later p q a b active _ actual bit-ok parsed first second rest

    fold-walk : ∀ w x slots {target} →
      declared-value w "%guard" ≡ val-native x →
      Trace fold-source w (record (start-state w x) { proof-rem = slots })
        (map lower (IrSource.instructions fold-source)) target → FoldRun w target
    fold-walk w x [] actual (next () _)
    fold-walk w x (p ∷ later) actual (next refl (next {st = before} ok rest))
      with read-preparation fold-source w before always "%p" "%a" p refl refl ok
    ... | active , a , bit-ok , _ , first , refl
      with refl ← just-injective (trans (sym one-bit) bit-ok)
      with next impact-ok next-steps ← rest
      rewrite one-bit with refl ← just-injective impact-ok =
        second-walk w x p a later _ actual first next-steps

    fold-observe : ∀ w target → satisfies fold-source w target → FoldRun w target
    fold-observe w target ok with satisfying-run fold-source w target ok
    ... | record { initialized = init-ok ; path = path }
      with initial fold-source w refl refl init-ok
    ... | x , actual , refl = fold-walk w x _ actual path

  one-guards : Bool → List Bool
  one-guards active = active ∷ []

  fold-guards : Bool → List Bool
  fold-guards active = true ∷ active ∷ []

  fold-skips : Bool → List (Maybe ℕ)
  fold-skips true = nothing ∷ nothing ∷ []
  fold-skips false = nothing ∷ just 2 ∷ []

  -- The preimage erases bytes from inactive slots and reproduces both public blocks.
  record Replay (src : IrSource) (w : CircuitWitness) (target : CircuitState)
                (guards : Bool → List Bool) (statement : Fr → Bool → List Fr)
                (impacts : Bool → List Fr) (skips : Bool → List (Maybe ℕ)) : Set where
    field
      active : Bool
      preimage : ProofPreimage
      final : State
      guard-value : declared-value w "%guard" ≡ val-native (χ active)
      declared-input : ProofPreimage.inputs preimage ≡ χ active ∷ []
      canonical-slots : Canonical (guards active) (ProofPreimage.inner-proofs preimage)
      impact-inputs : ProofPreimage.pub-transcript-inputs preimage ≡ impacts active
      skip-list : State.pi-skips final ≡ skips active
      accepted : preprocess src preimage ≡ just final
      same-carried : State.exposed final ≡ CircuitState.accs target
      same-statement : State.pis final ≡ CircuitState.pis target
      expected-statement : State.pis final ≡ statement (CircuitWitness.binding-input w) active

  private
    make-preimage : Fr → Bool → List Fr → List (List Byte) → ProofPreimage
    make-preimage binding active impacts slots = record
      { inputs = χ active ∷ []
      ; binding-input = binding
      ; comm-commitment = nothing
      ; pub-transcript-inputs = impacts
      ; pub-transcript-outputs = []
      ; priv-transcript = []
      ; inner-proofs = slots
      }

    native-decoded : ∀ x → decode native (x ∷ []) ≡ just (val-native x)
    native-decoded x with (x ∷ []) ≟LFr (x ∷ [])
    ... | yes _ = refl
    ... | no reject = ⊥-elim (reject refl)

    slot-canonical : ∀ active (raw : List Byte) → Canonical (one-guards active) (keep active raw ∷ [])
    slot-canonical false _ = Slots.inactive Slots.end
    slot-canonical true _ = Slots.active Slots.end

    run-one : ∀ binding active raw a → key-well-formed key ≡ true
      → (if active then prepare-active key inner-instance raw else just trivial-accumulator) ≡ just a
      → ∃ λ final →
          preprocess one-source (make-preimage binding active [] (keep active raw ∷ [])) ≡ just final
          × State.exposed final ≡ a ∷ []
          × State.pis final ≡ one-statement binding
          × State.pi-skips final ≡ []
    run-one binding false raw a _ prepared
      with refl ← just-injective prepared
      rewrite one-valid | native-decoded 0ᶠ | zero-bit | zero-bit | found-key = _ , refl , refl , refl , refl
    run-one binding true raw a parsed prepared
      rewrite one-valid | native-decoded 1ᶠ | one-bit | one-bit | found-key | parsed | prepared =
      _ , refl , refl , refl , refl

    run-fold : ∀ binding active p q a b c → key-well-formed key ≡ true
      → prepare-active key inner-instance p ≡ just a
      → (if active then prepare-active key inner-instance q else just trivial-accumulator) ≡ just b
      → fold-accumulators (a ∷ b ∷ []) ≡ just c
      → ∃ λ final →
          preprocess fold-source (make-preimage binding active (fold-impacts active) (p ∷ keep active q ∷ []))
            ≡ just final
          × State.exposed final ≡ c ∷ []
          × State.pis final ≡ fold-statement binding active
          × State.pi-skips final ≡ fold-skips active
    run-fold binding false p q a b c parsed first second folded
      with refl ← just-injective second
      rewrite fold-valid | native-decoded 0ᶠ | one-bit | found-key | parsed | first
      with (first-impact ∷ []) ≟LFr (first-impact ∷ [])
    ... | no reject = ⊥-elim (reject refl)
    ... | yes _ rewrite zero-bit | zero-bit | folded | zero-bit = _ , refl , refl , refl , refl
    run-fold binding true p q a b c parsed first second folded
      rewrite fold-valid | native-decoded 1ᶠ | one-bit | found-key | parsed | first
      with (first-impact ∷ []) ≟LFr (first-impact ∷ [])
    ... | no reject = ⊥-elim (reject refl)
    ... | yes _ rewrite one-bit | one-bit | second | folded | one-bit with (left-impact ∷ right-impact ∷ []) ≟LFr (left-impact ∷ right-impact ∷ [])
    ...   | no reject = ⊥-elim (reject refl)
    ...   | yes _ = _ , refl , refl , refl , refl

  one-replay : PreparationBackward → ∀ w target → satisfies one-source w target →
    Replay one-source w target one-guards (λ b _ → one-statement b) (λ _ → []) (λ _ → [])
  one-replay prepare w target sat with one-observe w target sat
  ... | one-run active raw a guard-value parsed prepared carried statement
    with run-one (CircuitWitness.binding-input w) active raw a parsed
      (prepare key inner-instance raw active a parsed prepared)
  ... | final , accepted , exposed , suffix , skips = record
    { active = active
    ; preimage = make-preimage (CircuitWitness.binding-input w) active [] (keep active raw ∷ [])
    ; final = final
    ; guard-value = guard-value
    ; declared-input = refl
    ; canonical-slots = slot-canonical active raw
    ; impact-inputs = refl
    ; skip-list = skips
    ; accepted = accepted
    ; same-carried = trans exposed (sym carried)
    ; same-statement = trans suffix (sym statement)
    ; expected-statement = suffix
    }

  fold-replay : PreparationBackward → ∀ w target → satisfies fold-source w target →
    Replay fold-source w target fold-guards fold-statement fold-impacts fold-skips
  fold-replay prepare w target sat with fold-observe w target sat
  ... | fold-run active p q a b c guard-value parsed first second folded carried statement
    with run-fold (CircuitWitness.binding-input w) active p q a b c parsed
      (prepare key inner-instance p true a parsed first) (prepare key inner-instance q active b parsed second) folded
  ... | final , accepted , exposed , suffix , skips = record
    { active = active
    ; preimage = make-preimage (CircuitWitness.binding-input w) active (fold-impacts active) (p ∷ keep active q ∷ [])
    ; final = final
    ; guard-value = guard-value
    ; declared-input = refl
    ; canonical-slots = Slots.active (slot-canonical active q)
    ; impact-inputs = refl
    ; skip-list = skips
    ; accepted = accepted
    ; same-carried = trans exposed (sym carried)
    ; same-statement = trans suffix (sym statement)
    ; expected-statement = suffix
    }

private
  literal : ℕ → Fr
  literal n = from-le-bits (low-bits 8 n)

-- The examples use binding input 99.  Replay holds for every binding input.
module Documented (key : List Byte) = Examples key (literal 123) (literal 42) (literal 7) (literal 8)
