{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.SequentialSource (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Syntax ⋯
open import zkir-v4.Types ⋯
open import zkir-v4.Circuit ⋯
open import zkir-v4.CircuitProperties ⋯ using (satisfying-run; SatisfiedRun; Trace; next; end)
open import zkir-v4.CircuitBridge ⋯ using (write-backward)
open import zkir-v4.Operations ⋯ using (Mem; ∅; ins; resolveᶠ; resolve-all-Fr; to𝔹; _≟B_; insert-proof)
open import zkir-v4.ReverseShape ⋯ using (immediate-true)
open import zkir-v4.Validation ⋯ using (resolve-vk; validate)
open import zkir-v4.Encoding ⋯ using (encode-accumulator)
open import zkir-v4.SequentialAccumulator ⋯ using (carried-fields; encoded-state; encode-carried; resolve-carried-fields)
open import zkir-v4.Protocol ⋯ using (instance-fields; instance-width; KeyArity; KeySchema)

open import Data.Bool using (true; false)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _++_; map; length; replicate)
open import Data.List.Properties using (++-identityʳ; length-replicate)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_)
open import Data.Product using (_×_; _,_; ∃)
open import Data.Vec using (toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; trans)
open import Relation.Nullary using (yes; no; does; Dec)

-- The statement length carries the level, so field reduction cannot
-- identify two level encodings.  The circuit supplies the first field
-- from its witness and the canonical statement fixes it to zero.
observed-fields : ℕ → Fr → Fr → Fr → Fr → List Fr
observed-fields n binding ctx start finish = binding ∷ ctx ∷ start ∷ finish ∷ replicate n 0ᶠ

fields : ℕ → Fr → Fr → Fr → List Fr
fields n = observed-fields n 0ᶠ

carried-count : ℕ → ℕ
carried-count zero = 0
carried-count (suc _) = 1

fields-width : ∀ n ctx start finish → length (fields n ctx start finish) ≡ 4 + n
fields-width n _ _ _ = cong (4 +_) (length-replicate n)

counter-instance-width : ∀ n ctx start finish as → length as ≡ carried-count n →
  length (instance-fields as (fields n ctx start finish)) ≡ carried-count n * 12 + (4 + n)
counter-instance-width n ctx start finish as count-ok = trans (instance-width as (fields n ctx start finish))
  (cong₂ (λ count width → count * 12 + width) count-ok (fields-width n ctx start finish))

InnerSchema : KeyArity → (ℕ → List Byte) → ℕ → Set
InnerSchema arity keys limit = ∀ n → suc n ≤ limit → KeySchema arity (keys n) (carried-count n) (4 + n)

iterate : ℕ → Fr → Fr
iterate zero x = x
iterate (suc n) x = iterate n x +ᶠ 1ᶠ

key-digest : List Byte → List Byte
key-digest key = toList (sha256-bytes key)

pinned-key : ∀ key → resolve-vk (key-digest key) (key ∷ []) ≡ just key
pinned-key key with key-digest key ≟B key-digest key
... | yes _ = refl
... | no bad = ⊥-elim (bad refl)

ctx start previous finish carried opening folded : Identifier
ctx = "%context"
start = "%start"
previous = "%previous"
finish = "%finish"
carried = "%carried"
opening = "%opening"
folded = "%folded"

private
  native-inputs : List TypedIdentifier
  native-inputs = ctx ⦂ native ∷ start ⦂ native ∷ previous ⦂ native ∷ []

  statement-operands : ℕ → Operand → Operand → List Operand
  statement-operands n a b = var ctx ∷ a ∷ b ∷ replicate n (imm 0ᶠ)

child-operands : ℕ → List Operand
child-operands n = imm 0ᶠ ∷ statement-operands n (var start) (var previous)

preparation-operands : ℕ → List Operand
preparation-operands zero = child-operands zero
preparation-operands (suc n) = map var carried-fields ++ child-operands (suc n)

preparation-operands-width : ∀ n → length (preparation-operands n) ≡ carried-count n * 12 + (4 + n)
preparation-operands-width zero = refl
preparation-operands-width (suc n) = cong (17 +_) (length-replicate n)

advance : Instruction
advance = add (var previous) (imm 1ᶠ) finish

publish : ℕ → Instruction
publish n = impact (imm 1ᶠ) (statement-operands (suc n) (var start) (var finish))

private
  read-proof : Instruction
  read-proof = inner-proof (imm 1ᶠ) "%proof"

prepare : List Byte → List Operand → Instruction
prepare key ops = prepare-verification (imm 1ᶠ) (key-digest key) ops "%proof" opening

source : (ℕ → List Byte) → ℕ → IrSource
source keys zero = mk-ir-source V0 (ctx ⦂ native ∷ []) [] false
  (impact (imm 1ᶠ) (statement-operands zero (var ctx) (var ctx)) ∷ []) []
source keys (suc zero) = mk-ir-source V0 native-inputs [] false
  (advance ∷ publish zero ∷ read-proof ∷ prepare (keys zero) (preparation-operands zero) ∷
   verify-accumulator (var opening) ∷ []) (keys zero ∷ [])
source keys (suc (suc n)) = mk-ir-source V0 (carried ⦂ accumulator ∷ native-inputs) [] false
  (advance ∷ publish (suc n) ∷ encode (var carried) carried-fields ∷ read-proof ∷
   prepare (keys (suc n)) (preparation-operands (suc n)) ∷
   accumulate (var opening ∷ var carried ∷ []) folded ∷ verify-accumulator (var folded) ∷ [])
  (keys (suc n) ∷ [])

private
  reflexive-test : ∀ {P : Set} (d : Dec P) → P → does d ≡ true
  reflexive-test (yes _) _ = refl
  reflexive-test (no bad) p = ⊥-elim (bad p)

  active-guard = reflexive-test (1ᶠ ≟ᶠ 1ᶠ) refl
  key-matches = λ key → reflexive-test (key-digest key ≟B key-digest key) refl

validated : ∀ keys n → validate (source keys n) ≡ true
validated keys zero = refl
validated keys (suc zero) rewrite active-guard | key-matches (keys zero) = refl
validated keys (suc (suc n)) rewrite active-guard | key-matches (keys (suc n)) = refl

-- The first step exposes only its child opening.  Every further step folds
-- that opening with the accumulator already carried by the child.
data Carries : List Accumulator → List Accumulator → Set where
  single : ∀ {a} → Carries (a ∷ []) (a ∷ [])
  batch : ∀ {a b f} → fold-accumulators (a ∷ b ∷ []) ≡ just f → Carries (f ∷ []) (a ∷ b ∷ [])

data Observation (keys : ℕ → List Byte) (binding : Fr) : ℕ → List Fr → List Accumulator → Set where
  initial : ∀ ctx → Observation keys binding zero (observed-fields zero binding ctx ctx ctx) []
  advanced : ∀ {n child outer} ctx start previous raw opening →
    length child ≡ carried-count n →
    prepare-circuit (keys n) (instance-fields child (fields n ctx start previous)) raw true ≡ just opening →
    Carries outer (opening ∷ child) →
    Observation keys binding (suc n)
      (observed-fields (suc n) binding ctx start (previous +ᶠ 1ᶠ)) outer

observation-count : ∀ {keys binding n stmt accs} →
  Observation keys binding n stmt accs → length accs ≡ carried-count n
observation-count (initial _) = refl
observation-count (advanced _ _ _ _ _ _ _ single) = refl
observation-count (advanced _ _ _ _ _ _ _ (batch _)) = refl

active : to𝔹 1ᶠ ≡ just true
active = immediate-true (mk-state ∅ (λ _ → nothing) [] [] [] [])

initial-state : CircuitWitness → Mem → CircuitState
initial-state w m = mk-state m (λ _ → nothing) (CircuitWitness.inner-proofs w) []
  (CircuitWitness.binding-input w ∷ []) []

private
  native-value : ∀ v → typeof v ≡ native → ∃ λ x → v ≡ val-native x
  native-value (val-native x) refl = x , refl
  native-value (val-bytes _) ()
  native-value (val-byte _) ()
  native-value (val-bool _) ()
  native-value (val-accumulator _) ()
  native-value (val-jubjub-point _) ()
  native-value (val-jubjub-scalar _) ()
  native-value (val-secp256k1-point _) ()
  native-value (val-secp256k1-base _) ()
  native-value (val-secp256k1-scalar _) ()
  native-value (val-secp256r1-point _) ()
  native-value (val-secp256r1-base _) ()
  native-value (val-secp256r1-scalar _) ()
  native-value (val-curve25519-point _) ()
  native-value (val-curve25519-base _) ()
  native-value (val-curve25519-scalar _) ()

  accumulator-value : ∀ v → typeof v ≡ accumulator → ∃ λ a → v ≡ val-accumulator a
  accumulator-value (val-native _) ()
  accumulator-value (val-bytes _) ()
  accumulator-value (val-byte _) ()
  accumulator-value (val-bool _) ()
  accumulator-value (val-accumulator a) refl = a , refl
  accumulator-value (val-jubjub-point _) ()
  accumulator-value (val-jubjub-scalar _) ()
  accumulator-value (val-secp256k1-point _) ()
  accumulator-value (val-secp256k1-base _) ()
  accumulator-value (val-secp256k1-scalar _) ()
  accumulator-value (val-secp256r1-point _) ()
  accumulator-value (val-secp256r1-base _) ()
  accumulator-value (val-secp256r1-scalar _) ()
  accumulator-value (val-curve25519-point _) ()
  accumulator-value (val-curve25519-base _) ()
  accumulator-value (val-curve25519-scalar _) ()

  declared-next : ∀ w m id t ds {out} → declare w m (id ⦂ t ∷ ds) ≡ just out →
    typeof (declared-value w id) ≡ t × declare w (ins id (declared-value w id) m) ds ≡ just out
  declared-next w m id t ds ok with typeof (declared-value w id) ≟T t
  ... | yes typed = typed , ok
  ... | no _ with () ← ok

declared-native : ∀ w m id ds {out} → declare w m (id ⦂ native ∷ ds) ≡ just out →
  ∃ λ x → declare w (ins id (val-native x) m) ds ≡ just out
declared-native w m id ds ok with declared-next w m id native ds ok
... | typed , rest with native-value (declared-value w id) typed
...   | x , same rewrite same = x , rest

declared-accumulator : ∀ w m id ds {out} → declare w m (id ⦂ accumulator ∷ ds) ≡ just out →
  ∃ λ a → declare w (ins id (val-accumulator a) m) ds ≡ just out
declared-accumulator w m id ds ok with declared-next w m id accumulator ds ok
... | typed , rest with accumulator-value (declared-value w id) typed
...   | a , same rewrite same = a , rest

install-native : Mem → Fr → Fr → Fr → Mem
install-native m c s p = ins previous (val-native p) (ins start (val-native s) (ins ctx (val-native c) m))

private
  declared-natives : ∀ w m {out} → declare w m native-inputs ≡ just out →
    ∃ λ c → ∃ λ s → ∃ λ p → out ≡ install-native m c s p
  declared-natives w m ok with declared-native w m ctx (start ⦂ native ∷ previous ⦂ native ∷ []) ok
  ... | c , rest with declared-native w (ins ctx (val-native c) m) start (previous ⦂ native ∷ []) rest
  ...   | s , rest′ with declared-native w (ins start (val-native s) (ins ctx (val-native c) m)) previous [] rest′
  ...     | p , out = c , s , p , sym (just-injective out)

resolve-padding : ∀ m n → resolve-all-Fr m (replicate n (imm 0ᶠ)) ≡ just (replicate n 0ᶠ)
resolve-padding m zero = refl
resolve-padding m (suc n) rewrite resolve-padding m n = refl

resolve-append : ∀ m ops rest xs ys →
  resolve-all-Fr m ops ≡ just xs → resolve-all-Fr m rest ≡ just ys →
  resolve-all-Fr m (ops ++ rest) ≡ just (xs ++ ys)
resolve-append m [] rest xs ys refl right = right
resolve-append m (op ∷ ops) rest xs ys left right with resolveᶠ m op
... | nothing with () ← left
resolve-append m (op ∷ ops) rest xs ys left right | just x with resolve-all-Fr m ops in values
... | nothing with () ← left
resolve-append m (op ∷ ops) rest xs ys left right | just x | just tail with refl ← just-injective left
  rewrite resolve-append m ops rest tail ys values right = refl

install : CircuitState → Identifier → IrValue → CircuitState
install st id a = record st { mem = ins id a (CircuitState.mem st) }

after-add : CircuitWitness → Mem → Fr → Fr → Fr → CircuitState
after-add w m c s p = install (initial-state w (install-native m c s p)) finish (val-native (p +ᶠ 1ᶠ))

private
  add-result : ∀ src w m c s p {after} →
    stepᶜ src w (initial-state w (install-native m c s p)) (lower advance) ≡ just after →
    after ≡ after-add w m c s p
  add-result src w m c s p = write-backward true w (initial-state w (install-native m c s p))
    ((finish , val-native (p +ᶠ 1ᶠ)) ∷ [])

after-publish : ℕ → CircuitWitness → Mem → Fr → Fr → Fr → CircuitState
after-publish n w m c s p = record (after-add w m c s p)
  { pis = observed-fields (suc n) (CircuitWitness.binding-input w) c s (p +ᶠ 1ᶠ) }

publish-step : ∀ src n w m c s p →
  stepᶜ src w (after-add w m c s p) (lower (publish n)) ≡ just (after-publish n w m c s p)
publish-step src n w m c s p rewrite active
  | resolve-padding (CircuitState.mem (after-add w m c s p)) (suc n) = refl

private
  publish-result : ∀ src n w m c s p {after} →
    stepᶜ src w (after-add w m c s p) (lower (publish n)) ≡ just after →
    after ≡ after-publish n w m c s p
  publish-result src n w m c s p ok =
    just-injective (trans (sym ok) (publish-step src n w m c s p))

  walked-base : ∀ keys w c {final} →
    Trace (source keys zero) w (initial-state w (ins ctx (val-native c) ∅))
      (map lower (IrSource.instructions (source keys zero))) final →
    Observation keys (CircuitWitness.binding-input w) zero (CircuitState.pis final) (CircuitState.accs final)
  walked-base keys w c (next passed end) rewrite active with refl ← just-injective passed = initial c

  observe-base : ∀ keys w final → satisfies (source keys zero) w final →
    Observation keys (CircuitWitness.binding-input w) zero (CircuitState.pis final) (CircuitState.accs final)
  observe-base keys w final ok with satisfying-run (source keys zero) w final ok
  ... | record { initialized = init-ok ; path = path }
    with declare w ∅ (ctx ⦂ native ∷ []) in declared
  ...   | nothing with () ← init-ok
  observe-base keys w final ok | record { initialized = init-ok ; path = path } | just m
    with declared-native w ∅ ctx [] declared
  ...   | c , mem-ok with refl ← just-injective init-ok | refl ← just-injective mem-ok = walked-base keys w c path

  prepare-result : ∀ src w st key ns xs raw {after} →
    resolve-all-Fr (CircuitState.mem st) ns ≡ just xs →
    CircuitState.proofs st "%proof" ≡ just raw →
    resolve-vk (key-digest key) (IrSource.inner-vks src) ≡ just key →
    stepᶜ src w st (lower (prepare key ns)) ≡ just after →
    ∃ λ a → prepare-circuit key xs raw true ≡ just a × after ≡ install st opening (val-accumulator a)
  prepare-result src w st key ns xs raw values found pinned ok
    rewrite active | values | found | pinned with key-well-formed key
  ... | false with () ← ok
  prepare-result src w st key ns xs raw values found pinned ok | true
    with prepare-circuit key xs raw true
  ... | nothing with () ← ok
  prepare-result src w st key ns xs raw values found pinned ok | true | just a =
    a , refl , write-backward true w st ((opening , val-accumulator a) ∷ []) ok

  proof-result : ∀ src w st {after} →
    stepᶜ src w st (lower read-proof) ≡ just after →
    ∃ λ raw → ∃ λ slots → after ≡ record st
      { proofs = insert-proof "%proof" raw (CircuitState.proofs st) ; proof-rem = slots }
  proof-result src w st ok with CircuitState.proof-rem st
  ... | [] with () ← ok
  proof-result src w st ok | raw ∷ slots = raw , slots , sym (just-injective ok)

  first-tail : ∀ keys w m c s p {final} →
    Trace (source keys 1) w (after-publish zero w m c s p)
      (map lower (read-proof ∷ prepare (keys zero) (child-operands zero) ∷ verify-accumulator (var opening) ∷ [])) final →
    Observation keys (CircuitWitness.binding-input w) 1 (CircuitState.pis final) (CircuitState.accs final)
  first-tail keys w m c s p (next {st = st} bound (next {st = before} ok tail))
    with raw , slots , refl ← proof-result (source keys 1) w st bound
    with prepare-result (source keys 1) w before (keys zero) (child-operands zero)
      (fields zero c s p) raw refl refl (pinned-key (keys zero)) ok
  ... | a , prepared , refl with next refl end ← tail = advanced c s p raw a refl prepared single

  fold-tail : ∀ keys n w st c s p raw a b {final} →
    CircuitState.mem st opening ≡ just (val-accumulator a) →
    CircuitState.mem st carried ≡ just (val-accumulator b) →
    CircuitState.accs st ≡ [] →
    CircuitState.pis st ≡ observed-fields (suc (suc n)) (CircuitWitness.binding-input w) c s (p +ᶠ 1ᶠ) →
    prepare-circuit (keys (suc n)) (instance-fields (b ∷ []) (fields (suc n) c s p)) raw true ≡ just a →
    Trace (source keys (suc (suc n))) w st
      (map lower (accumulate (var opening ∷ var carried ∷ []) folded ∷ verify-accumulator (var folded) ∷ [])) final →
    Observation keys (CircuitWitness.binding-input w) (suc (suc n)) (CircuitState.pis final) (CircuitState.accs final)
  fold-tail keys n w st c s p raw a b opened child no-acc statement prepared (next ok rest)
    rewrite opened | child with fold-accumulators (a ∷ b ∷ []) in folded-ok
  ... | nothing with () ← ok
  fold-tail keys n w st c s p raw a b opened child no-acc statement prepared (next ok rest) | just f
    with refl ← write-backward true w st ((folded , val-accumulator f) ∷ []) ok
    with next refl end ← rest
    rewrite no-acc | statement = advanced c s p raw a refl prepared (batch folded-ok)

  resolve-child : ∀ m n c s p →
    m ctx ≡ just (val-native c) → m start ≡ just (val-native s) → m previous ≡ just (val-native p) →
    resolve-all-Fr m (child-operands (suc n)) ≡ just (fields (suc n) c s p)
  resolve-child m n c s p ctx-ok start-ok prev-ok
    rewrite ctx-ok | start-ok | prev-ok | resolve-padding m n = refl

resolve-predecessor : ∀ n w c s p b →
  let st = after-publish (suc n) w (ins carried (val-accumulator b) ∅) c s p
      m = CircuitState.mem (encoded-state st b)
  in resolve-all-Fr m (map var carried-fields ++ child-operands (suc n))
    ≡ just (instance-fields (b ∷ []) (fields (suc n) c s p))
resolve-predecessor n w c s p b =
  trans (resolve-append m (map var carried-fields) (child-operands (suc n))
    (encode-accumulator b) (fields (suc n) c s p)
    (resolve-carried-fields st b) (resolve-child m n c s p refl refl refl))
    (cong (λ block → just (block ++ fields (suc n) c s p)) (sym (++-identityʳ (encode-accumulator b))))
  where
  st = after-publish (suc n) w (ins carried (val-accumulator b) ∅) c s p
  m = CircuitState.mem (encoded-state st b)

private
  later-tail : ∀ keys n w c s p b {final} →
    let outer-source = source keys (suc (suc n))
        after-statement = after-publish (suc n) w (ins carried (val-accumulator b) ∅) c s p
        ops = map var carried-fields ++ child-operands (suc n)
    in Trace outer-source w after-statement
      (map lower (encode (var carried) carried-fields ∷ read-proof ∷ prepare (keys (suc n)) ops ∷
        accumulate (var opening ∷ var carried ∷ []) folded ∷ verify-accumulator (var folded) ∷ [])) final →
    Observation keys (CircuitWitness.binding-input w) (suc (suc n)) (CircuitState.pis final) (CircuitState.accs final)
  later-tail keys n w c s p b (next {st = st} encoded (next {st = encoded-st} bound (next {st = before} prepared tail)))
    with refl ← encode-carried (source keys (suc (suc n))) w st b refl encoded
    with raw , slots , refl ← proof-result (source keys (suc (suc n))) w encoded-st bound
    with prepare-result (source keys (suc (suc n))) w before (keys (suc n))
      (map var carried-fields ++ child-operands (suc n))
      (instance-fields (b ∷ []) (fields (suc n) c s p)) raw
      (resolve-predecessor n w c s p b)
      refl (pinned-key (keys (suc n))) prepared
  ... | a , opening-ok , refl = fold-tail keys n w _ c s p raw a b refl refl refl refl opening-ok tail

  walked-first : ∀ keys w m c s p {final} →
    Trace (source keys 1) w (initial-state w (install-native m c s p))
      (map lower (IrSource.instructions (source keys 1))) final →
    Observation keys (CircuitWitness.binding-input w) 1 (CircuitState.pis final) (CircuitState.accs final)
  walked-first keys w m c s p (next added (next published tail))
    with refl ← add-result (source keys 1) w m c s p added
    with refl ← publish-result (source keys 1) zero w m c s p published = first-tail keys w m c s p tail

  walked-later : ∀ keys n w c s p b {final} →
    Trace (source keys (suc (suc n))) w (initial-state w (install-native (ins carried (val-accumulator b) ∅) c s p))
      (map lower (IrSource.instructions (source keys (suc (suc n))))) final →
    Observation keys (CircuitWitness.binding-input w) (suc (suc n)) (CircuitState.pis final) (CircuitState.accs final)
  walked-later keys n w c s p b (next added (next published tail))
    with refl ← add-result (source keys (suc (suc n))) w (ins carried (val-accumulator b) ∅) c s p added
    with refl ← publish-result (source keys (suc (suc n))) (suc n) w _ c s p published = later-tail keys n w c s p b tail

observe : ∀ keys n w final → satisfies (source keys n) w final →
  Observation keys (CircuitWitness.binding-input w) n (CircuitState.pis final) (CircuitState.accs final)
observe keys zero = observe-base keys
observe keys 1 w final ok with satisfying-run (source keys 1) w final ok
... | record { initialized = init-ok ; path = path } with declare w ∅ native-inputs in declared
...   | nothing with () ← init-ok
observe keys 1 w final ok | record { initialized = init-ok ; path = path } | just m
  with declared-natives w ∅ declared
... | c , s , p , refl with refl ← just-injective init-ok = walked-first keys w ∅ c s p path
observe keys (suc (suc n)) w final ok with satisfying-run (source keys (suc (suc n))) w final ok
... | record { initialized = init-ok ; path = path }
  with declare w ∅ (carried ⦂ accumulator ∷ native-inputs) in declared
...   | nothing with () ← init-ok
observe keys (suc (suc n)) w final ok | record { initialized = init-ok ; path = path } | just m
  with declared-accumulator w ∅ carried native-inputs declared
... | b , rest with declared-natives w (ins carried (val-accumulator b) ∅) rest
...   | c , s , p , refl with refl ← just-injective init-ok = walked-later keys n w c s p b path
