{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.CircuitAccumulatorFrame (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Circuit ⋯
open import zkir-v4.CircuitBridge ⋯ using
  (assert-backward; bounded-backward; shared-backward; witness-cell-backward; write-backward)
open import zkir-v4.CircuitProperties ⋯ as CircuitTrace using (Trace)
open import zkir-v4.Operations ⋯ hiding (write; writes)
open import zkir-v4.Producer ⋯
open import zkir-v4.ProducerByteValues ⋯ using (parts-length)
open import zkir-v4.ProducerCompute ⋯ using (compute-types)
open import zkir-v4.ProducerResiduals ⋯ using (bound-bits; bound-division; bound-reconstitution)
open import zkir-v4.ProducerStep ⋯ using (final-bindings; prepare-binding; fold-binding; output-binding)
open import zkir-v4.ProducerStore ⋯
open import zkir-v4.ProducerValuesHelpers ⋯ using (checked; take-result; binary-output; skip)
open import zkir-v4.Protocol ⋯ using (exposure)
open import zkir-v4.Syntax ⋯
open import zkir-v4.Types ⋯
open import zkir-v4.Validation ⋯ using (resolve-vk)

open import Data.Bool using (true; false)
import Data.Bool as B
open import Data.List using (List; []; _∷_; _++_; length; map)
open import Data.List.Properties using (++-identityʳ)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (_^_; _<?_; _<ᵇ_)
open import Data.Product using (_×_; _,_; ∃)
open import Data.Vec using (Vec; toList)
open import Data.Vec.Properties using (length-toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import Relation.Nullary using (yes; no)

record CircuitWrites (st : CircuitState) (i : Instruction) (after : CircuitState) (bs : Env) : Set where
  constructor writes-step
  field
    values : List (Identifier × IrValue)
    types : writes-types values ≡ bs
    memory : CircuitState.mem after ≡ apply-writes (CircuitState.mem st) values
    accs : ∃ λ suffix → (length suffix ≡ exposure i)
                       × (CircuitState.accs after ≡ CircuitState.accs st ++ suffix)

private
  writes-only : ∀ st i after {bs} ws → exposure i ≡ 0 → writes-types ws ≡ bs
    → after ≡ record st { mem = apply-writes (CircuitState.mem st) ws }
    → CircuitWrites st i after bs
  writes-only st i after ws no-exposure types refl =
    writes-step ws types refl ([] , sym no-exposure , sym (++-identityʳ (CircuitState.accs st)))

  common-writes : ∀ s w st i after Γ {bs} → lower i ≡ shared i → exposure i ≡ 0
    → StoreTyped Γ (CircuitState.mem st) → bindings (IrSource.outputs s) Γ i ≡ just bs
    → stepᶜ s w st (lower i) ≡ just after → CircuitWrites st i after bs
  common-writes s w st i after Γ shared-ok no-exposure typed binds ok
    with shared-backward s w st i {result = after}
      (subst (λ c → stepᶜ s w st c ≡ just after) shared-ok ok)
  ... | ws , computed , installed = writes-only st i after ws no-exposure
    (compute-types (IrSource.outputs s) Γ (CircuitState.mem st) i typed binds computed) installed

  bounded-writes : ∀ s w st i after Γ {bs} bits
    → lower i ≡ bounded-bits bits i → exposure i ≡ 0
    → preprocess-bit-bounds i ≡ true
    → (∀ m → compute m i ≡ preprocess-bounded m i)
    → StoreTyped Γ (CircuitState.mem st) → bindings (IrSource.outputs s) Γ i ≡ just bs
    → stepᶜ s w st (lower i) ≡ just after → CircuitWrites st i after bs
  bounded-writes s w st i after Γ bits lowered no-exposure limit bounded typed binds ok
    with bounded-backward s w st i bits {result = after}
      (subst (λ c → stepᶜ s w st c ≡ just after) lowered ok)
  ... | _ , ws , computed , installed = writes-only st i after ws no-exposure
    (compute-types (IrSource.outputs s) Γ (CircuitState.mem st) i typed binds
      (trans (bounded (CircuitState.mem st)) restricted)) installed
    where
    restricted : preprocess-bounded (CircuitState.mem st) i ≡ just ws
    restricted rewrite limit = computed

  one-write : ∀ w st i after {bs} id v → exposure i ≡ 0
    → (id ⦂ typeof v) ∷ [] ≡ bs
    → write-one w st id v ≡ just after → CircuitWrites st i after bs
  one-write w st i after id v no-exposure typed ok =
    writes-only st i after ((id , v) ∷ []) no-exposure typed
      (write-backward true w st ((id , v) ∷ []) ok)

  no-write : ∀ st i after {bs} → exposure i ≡ 0 → [] ≡ bs
    → CircuitState.mem after ≡ CircuitState.mem st
    → CircuitState.accs after ≡ CircuitState.accs st
    → CircuitWrites st i after bs
  no-write st i after no-exposure typed same-memory same-accs =
    writes-step [] typed same-memory
      ([] , sym no-exposure , trans same-accs (sym (++-identityʳ (CircuitState.accs st))))

  read-writes : ∀ s w st i after {bs} t id → exposure i ≡ 0 → (id ⦂ t) ∷ [] ≡ bs
    → stepᶜ s w st (witness-cell t id) ≡ just after → CircuitWrites st i after bs
  read-writes s w st i after t id no-exposure binds ok
    with witness-cell-backward s w st t id {target = after} ok
  ... | v , _ , typed , installed = writes-only st i after ((id , v) ∷ []) no-exposure
    (trans (cong (λ u → (id ⦂ u) ∷ []) typed) binds) installed

  hash-writes : ∀ {n} → (kind : HashKind) → ∀ s w st i after alignment ops id {bs}
    → exposure i ≡ 0
    → (id ⦂ bytes n) ∷ [] ≡ bs
    → (∀ xs {raw} → digestᶜ kind alignment xs ≡ just raw → length raw ≡ n)
    → stepᶜ s w st (aligned-hash kind alignment ops id) ≡ just after
    → CircuitWrites st i after bs
  hash-writes kind s w st i after a ops id no-exposure binds sized ok
    with bind-success (resolve-all-Fr (CircuitState.mem st) ops) _ ok
  ... | xs , _ , hashed with bind-success (digestᶜ kind a xs) _ hashed
  ... | raw , digested , wrote = one-write w st i after id (val-bytes raw) no-exposure
    (trans (cong (λ n → (id ⦂ bytes n) ∷ []) (sized xs digested)) binds) wrote

  digest-length : ∀ {A : Set} {n} (digest : Maybe (Vec A n)) {raw}
    → (digest >>= λ bs → just (toList bs)) ≡ just raw → length raw ≡ n
  digest-length nothing ()
  digest-length (just v) refl = length-toList v

circuit-step-writes : ∀ s w st i after Γ {bs Γ′}
  → StoreTyped Γ (CircuitState.mem st) → bindings (IrSource.outputs s) Γ i ≡ just bs
  → fold-check fresh Γ bs ≡ just Γ′
  → stepᶜ s w st (lower i) ≡ just after → CircuitWrites st i after bs
circuit-step-writes s w st i@(encode _ _) after Γ typed binds _ ok =
  common-writes s w st i after Γ refl refl typed binds ok
circuit-step-writes s w st i@(constrain-to-boolean _) after Γ typed binds _ ok =
  common-writes s w st i after Γ refl refl typed binds ok
circuit-step-writes s w st i@(copy _ _) after Γ typed binds _ ok =
  common-writes s w st i after Γ refl refl typed binds ok
circuit-step-writes s w st i@(ec-mul _ _ _) after Γ typed binds _ ok =
  common-writes s w st i after Γ refl refl typed binds ok
circuit-step-writes s w st i@(ec-mul-generator _ _) after Γ typed binds _ ok =
  common-writes s w st i after Γ refl refl typed binds ok
circuit-step-writes s w st i@(hash-to-curve _ _) after Γ typed binds _ ok =
  common-writes s w st i after Γ refl refl typed binds ok
circuit-step-writes s w st i@(into-coordinates _ _) after Γ typed binds _ ok =
  common-writes s w st i after Γ refl refl typed binds ok
circuit-step-writes s w st i@(from-coordinates _ _) after Γ typed binds _ ok =
  common-writes s w st i after Γ refl refl typed binds ok
circuit-step-writes s w st i@(into-bytes32 _ _) after Γ typed binds _ ok =
  common-writes s w st i after Γ refl refl typed binds ok
circuit-step-writes s w st i@(from-bytes32 _ _ _) after Γ typed binds _ ok =
  common-writes s w st i after Γ refl refl typed binds ok
circuit-step-writes s w st i@(reverse-bytes _ _) after Γ typed binds _ ok =
  common-writes s w st i after Γ refl refl typed binds ok
circuit-step-writes s w st i@(bytes32-into-low-high _ _) after Γ typed binds _ ok =
  common-writes s w st i after Γ refl refl typed binds ok
circuit-step-writes s w st i@(transient-hash _ _) after Γ typed binds _ ok =
  common-writes s w st i after Γ refl refl typed binds ok
circuit-step-writes s w st i@(add _ _ _) after Γ typed binds _ ok =
  common-writes s w st i after Γ refl refl typed binds ok
circuit-step-writes s w st i@(mul _ _ _) after Γ typed binds _ ok =
  common-writes s w st i after Γ refl refl typed binds ok
circuit-step-writes s w st i@(neg _ _) after Γ typed binds _ ok =
  common-writes s w st i after Γ refl refl typed binds ok
circuit-step-writes s w st i@(inv _ _) after Γ typed binds _ ok =
  common-writes s w st i after Γ refl refl typed binds ok
circuit-step-writes s w st i@(not _ _) after Γ typed binds _ ok =
  common-writes s w st i after Γ refl refl typed binds ok
circuit-step-writes s w st i@(jubjub-scalar-from-native _ _) after Γ typed binds _ ok =
  common-writes s w st i after Γ refl refl typed binds ok
circuit-step-writes s w st i@(slice _ _ _ _) after Γ typed binds _ ok =
  common-writes s w st i after Γ refl refl typed binds ok
circuit-step-writes s w st i@(nth _ _ _) after Γ typed binds _ ok =
  common-writes s w st i after Γ refl refl typed binds ok
circuit-step-writes s w st i@(concat _ _) after Γ typed binds _ ok =
  common-writes s w st i after Γ refl refl typed binds ok
circuit-step-writes s w st i@(reverse _ _) after Γ typed binds _ ok =
  common-writes s w st i after Γ refl refl typed binds ok
circuit-step-writes s w st i@(load-constant _ _ _) after Γ typed binds _ ok =
  common-writes s w st i after Γ refl refl typed binds ok
circuit-step-writes s w st i@(and _ _) after Γ typed binds _ ok =
  common-writes s w st i after Γ refl refl typed binds ok
circuit-step-writes s w st i@(or _ _) after Γ typed binds _ ok =
  common-writes s w st i after Γ refl refl typed binds ok
circuit-step-writes s w st i@(xor _ _) after Γ typed binds _ ok =
  common-writes s w st i after Γ refl refl typed binds ok
circuit-step-writes s w st i@(to-bytes _ _) after Γ typed binds _ ok =
  common-writes s w st i after Γ refl refl typed binds ok
circuit-step-writes s w st i@(from-bytes _ _ _) after Γ typed binds _ ok =
  common-writes s w st i after Γ refl refl typed binds ok
circuit-step-writes s w st i@(bytes-into-natives _ _) after Γ typed binds _ ok =
  common-writes s w st i after Γ refl refl typed binds ok
circuit-step-writes s w st i@(bytes-from-natives _ _ _) after Γ typed binds _ ok =
  common-writes s w st i after Γ refl refl typed binds ok
circuit-step-writes s w st i@(constrain-bits x n) after Γ typed binds fresh-ok ok =
  bounded-writes s w st i after Γ n refl refl
    (bound-bits sig Γ x n (trans (cong (λ bs → bs >>= fold-check fresh Γ) binds) fresh-ok))
    (λ _ → refl) typed binds ok
  where sig = IrSource.outputs s
circuit-step-writes s w st i@(div-mod-power-of-two x n os) after Γ typed binds fresh-ok ok =
  bounded-writes s w st i after Γ n refl refl
    (bound-division sig Γ x n os (trans (cong (λ bs → bs >>= fold-check fresh Γ) binds) fresh-ok))
    (λ _ → refl) typed binds ok
  where sig = IrSource.outputs s
circuit-step-writes s w st i@(reconstitute-field d m n id) after Γ typed binds fresh-ok ok =
  bounded-writes s w st i after Γ n refl refl
    (bound-reconstitution sig Γ d m n id (trans (cong (λ bs → bs >>= fold-check fresh Γ) binds) fresh-ok))
    (λ _ → refl) typed binds ok
  where sig = IrSource.outputs s
circuit-step-writes s w st i@(assert x) after Γ _ binds _ ok
  with assert-backward s w st x {result = after} ok
... | _ , _ , _ , refl =
  writes-only st i st [] refl (final-bindings {xs = expect (IrSource.outputs s) Γ native x} binds) refl
circuit-step-writes s w st i@(cond-select g a b id) after Γ typed binds _ ok
  with binary-output (IrSource.outputs s) Γ (CircuitState.mem st) selectable a b id typed
    (skip (expect (IrSource.outputs s) Γ native g) binds)
... | x , y , av , bv , same , shape rewrite av | bv
  with bind-success (resolve𝔹 (CircuitState.mem st) g) _ ok
... | flag , _ , guarded
  with checked (typeof x ≟T typeof y) guarded
... | _ , selected with flag
... | true = one-write w st i after id x refl shape
  (take-result (select-supported (typeof x)) selected)
... | false = one-write w st i after id y refl
  (trans (cong (λ t → (id ⦂ t) ∷ []) same) shape)
  (take-result (select-supported (typeof x)) selected)
circuit-step-writes s w st i@(bytes32-from-low-high (lo , hi) id) after Γ _ binds _ ok
  with bind-success (resolveᶠ (CircuitState.mem st) hi) _ ok
... | high , _ , resolved-lo with bind-success (resolve (CircuitState.mem st) lo) _ resolved-lo
... | low , _ , paired with bind-success (bytes32-from-parts low (val-native high)) _ paired
... | bs , parsed , wrote = writes-only st i after ((id , val-bytes bs) ∷ []) refl
  (trans (cong (λ n → (id ⦂ bytes n) ∷ []) (parts-length low (val-native high) parsed))
         (final-bindings {xs = expect (IrSource.outputs s) Γ native lo >>
                              expect (IrSource.outputs s) Γ native hi} binds))
  (write-backward false w st ((id , val-bytes bs) ∷ []) wrote)
circuit-step-writes s w st i@(constrain-eq a b) after Γ _ binds _ ok
  with bind-success (chip-equality (CircuitState.mem st) a b) _ ok
... | false , _ , ()
... | true , _ , written with bind-success (ty (IrSource.outputs s) Γ a) _ binds
... | t , _ , accepted = writes-only st i after [] refl
  (final-bindings {xs = demand (B.not (equal t accumulator))}
    (skip (expect (IrSource.outputs s) Γ t b) accepted))
  (sym (just-injective written))
circuit-step-writes s w st i@(test-eq a b id) after Γ _ binds _ ok
  with bind-success (chip-equality (CircuitState.mem st) a b) _ ok
... | flag , _ , wrote with bind-success (ty (IrSource.outputs s) Γ a) _ binds
... | t , _ , accepted = one-write w st i after id (val-native (χ flag)) refl
  (final-bindings {xs = demand (B.not (equal t accumulator))}
    (skip (expect (IrSource.outputs s) Γ t b) accepted)) wrote
circuit-step-writes s w st i@(less-than a b n id) after Γ _ binds _ ok
  with bind-success (resolveᶠ (CircuitState.mem st) a) _ ok
... | x , _ , other with bind-success (resolveᶠ (CircuitState.mem st) b) _ other
... | y , _ , bounds with checked (valFr x <? 2 ^ even4 n) bounds
... | _ , next-bound with checked (valFr y <? 2 ^ even4 n) next-bound
... | _ , compared with valFr x <? valFr y
... | yes _ = one-write w st i after id (val-native 1ᶠ) refl shape compared
  where
  sig = IrSource.outputs s
  shape = final-bindings {xs = expect sig Γ native a >> expect sig Γ native b >>
    demand (n <ᵇ FR-BITS)} binds
... | no _ = one-write w st i after id (val-native 0ᶠ) refl shape compared
  where
  sig = IrSource.outputs s
  shape = final-bindings {xs = expect sig Γ native a >> expect sig Γ native b >>
    demand (n <ᵇ FR-BITS)} binds
circuit-step-writes s w st i@(persistent-hash a xs id) after Γ _ binds _ ok =
  hash-writes sha256 s w st i after a xs id refl
    (final-bindings {xs = aligned-inputs (IrSource.outputs s) Γ a xs} binds)
    (λ vs → digest-length (persistent-hash-circuit-fn a vs)) ok
circuit-step-writes s w st i@(keccak256 a xs id) after Γ _ binds _ ok =
  hash-writes keccak s w st i after a xs id refl
    (final-bindings {xs = aligned-inputs (IrSource.outputs s) Γ a xs} binds)
    (λ vs → digest-length (keccak-circuit-fn a vs)) ok
circuit-step-writes s w st i@(sha512 a xs id) after Γ _ binds _ ok =
  hash-writes sha-512 s w st i after a xs id refl
    (final-bindings {xs = aligned-inputs (IrSource.outputs s) Γ a xs} binds)
    (λ vs → digest-length (sha512-circuit-fn a vs)) ok
circuit-step-writes s w st i@(public-input g t id) after Γ _ binds _ ok =
  read-writes s w st i after t id refl
    (final-bindings {xs = guard-ty (IrSource.outputs s) Γ g} binds) ok
circuit-step-writes s w st i@(private-input g t id) after Γ _ binds _ ok =
  read-writes s w st i after t id refl
    (final-bindings {xs = guard-ty (IrSource.outputs s) Γ g} binds) ok
circuit-step-writes s w st i@(impact g ops) after Γ _ binds _ ok
  with bind-success (resolve𝔹 (CircuitState.mem st) g) _ ok
... | _ , _ , resolved with bind-success (resolve-all-Fr (CircuitState.mem st) ops) _ resolved
... | _ , _ , done = no-write st i after refl
  (final-bindings {xs = expect (IrSource.outputs s) Γ native g >>
                       expect-all (IrSource.outputs s) Γ native ops} binds)
  (cong CircuitState.mem (sym (just-injective done)))
  (cong CircuitState.accs (sym (just-injective done)))
circuit-step-writes s w st i@(circuit-output ops) after Γ _ binds _ ok
  with bind-success (collect-outputs (CircuitState.mem st) (IrSource.outputs s) ops) _ ok
... | _ , _ , done = no-write st i after refl (output-binding (IrSource.outputs s) Γ ops binds)
  (cong CircuitState.mem (sym (just-injective done)))
  (cong CircuitState.accs (sym (just-injective done)))
circuit-step-writes s w st i@(inner-proof g id) after Γ _ binds _ ok
  with CircuitState.proof-rem st
... | [] with () ← ok
circuit-step-writes s w st i@(inner-proof g id) after Γ _ binds _ ok | _ ∷ _ =
  no-write st i after refl (final-bindings {xs = expect (IrSource.outputs s) Γ native g} binds)
    (cong CircuitState.mem (sym (just-injective ok)))
    (cong CircuitState.accs (sym (just-injective ok)))
circuit-step-writes s w st i@(prepare-verification g hash ops proof id) after Γ _ binds _ ok
  with bind-success (resolve𝔹 (CircuitState.mem st) g) _ ok
... | active , _ , resolved with bind-success (resolve-all-Fr (CircuitState.mem st) ops) _ resolved
... | xs , _ , found with bind-success (CircuitState.proofs st proof) _ found
... | raw , _ , selected with bind-success (resolve-vk hash (IrSource.inner-vks s)) _ selected
... | vk , _ , prepared with bind-success (prepare-circuit vk xs raw active) _
  (take-result (key-well-formed vk) prepared)
... | acc , _ , wrote = one-write w st i after id (val-accumulator acc) refl
  (prepare-binding (IrSource.outputs s) Γ g hash ops proof id binds) wrote
circuit-step-writes s w st i@(accumulate ops id) after Γ _ binds _ ok
  with bind-success (resolve-accs (CircuitState.mem st) ops) _ ok
... | [] , _ , ()
... | _ ∷ [] , _ , ()
... | accs@(_ ∷ _ ∷ _) , _ , folding with bind-success (fold-accumulators accs) _ folding
... | acc , _ , wrote = one-write w st i after id (val-accumulator acc) refl
  (fold-binding (IrSource.outputs s) Γ ops id binds) wrote
circuit-step-writes s w st i@(verify-accumulator op) after Γ _ binds _ ok
  with bind-success (resolve-acc (CircuitState.mem st) op) _ ok
... | acc , _ , done = writes-step []
  (final-bindings {xs = expect (IrSource.outputs s) Γ accumulator op} binds)
  (cong CircuitState.mem (sym (just-injective done)))
  (acc ∷ [] , refl , cong CircuitState.accs (sym (just-injective done)))

record CircuitFrame (st : CircuitState) (i : Instruction) (after : CircuitState) (Γ Γ′ : Env) : Set where
  field
    typed-after : StoreTyped Γ′ (CircuitState.mem after)
    extends : Extends Γ (CircuitState.mem st) (CircuitState.mem after)
    keeps-types : ∀ id t → type-of Γ id ≡ just t → type-of Γ′ id ≡ just t
    accs : ∃ λ suffix → (length suffix ≡ exposure i)
                       × (CircuitState.accs after ≡ CircuitState.accs st ++ suffix)

-- Freshness of the producer's bindings frames every existing cell.
circuit-step-frame : ∀ s w st i after Γ {Γ′}
  → StoreTyped Γ (CircuitState.mem st)
  → producer-step (IrSource.outputs s) Γ i ≡ just Γ′
  → stepᶜ s w st (lower i) ≡ just after → CircuitFrame st i after Γ Γ′
circuit-step-frame s w st i after Γ {Γ′} typed producer ok
  with bind-success (bindings (IrSource.outputs s) Γ i) (fold-check fresh Γ) producer
... | bs , binds , inserted =
  let effects = circuit-step-writes s w st i after Γ typed binds inserted ok
      ws = CircuitWrites.values effects
      frame = subst (λ memory → WriteFrame Γ Γ′ (CircuitState.mem st) memory ws)
        (sym (CircuitWrites.memory effects))
        (write-frame Γ (CircuitState.mem st) ws typed
          (trans (cong (fold-check fresh Γ) (CircuitWrites.types effects)) inserted))
  in record
    { typed-after = WriteFrame.typed-after frame
    ; extends = WriteFrame.extends frame
    ; keeps-types = WriteFrame.keeps-types frame
    ; accs = CircuitWrites.accs effects
    }

private
  declare-store : ∀ w ds Γ m {Γ′ m′}
    → StoreTyped Γ m
    → fold-check fresh Γ ds ≡ just Γ′
    → declare w m ds ≡ just m′ → StoreTyped Γ′ m′
  declare-store w [] Γ m typed refl refl = typed
  declare-store w ((id ⦂ t) ∷ ds) Γ m typed inserted declared
    with fold-cons fresh Γ (id ⦂ t) ds inserted
  ... | Γ₁ , head , tail with fresh-success Γ id t head
  ... | refl , _ , _ with checked (typeof (declared-value w id) ≟T t)
    (assign-declaration w id t m ds declared)
    where
    assign-declaration : ∀ w id t m ds {m′} → declare w m ((id ⦂ t) ∷ ds) ≡ just m′
      → guardD (typeof (declared-value w id) ≟T t)
          (declare w (ins id (declared-value w id) m) ds) ≡ just m′
    assign-declaration w id t m ds ok with typeof (declared-value w id) ≟T t
    ... | yes _ = ok
    ... | no _ = ok
  ... | v-type , rest =
    declare-store w ds ((id ⦂ t) ∷ Γ) (ins id (declared-value w id) m)
      (insert-typed typed v-type) tail rest

  init-memory : ∀ s w {st} → initᶜ s w ≡ just st
    → declare w ∅ (IrSource.inputs s) ≡ just (CircuitState.mem st)
  init-memory s w ok with declare w ∅ (IrSource.inputs s) in declared
  ... | nothing with () ← ok
  init-memory s w ok | just memory with IrSource.do-communications-commitment s | CircuitWitness.comm-commitment w
  ... | false | _ = cong (λ st′ → just (CircuitState.mem st′)) (just-injective ok)
  ... | true | nothing with () ← ok
  init-memory s w ok | just memory | true | just (_ , _) =
    cong (λ st′ → just (CircuitState.mem st′)) (just-injective ok)

circuit-init-store : ∀ s w {st Γ}
  → fold-check fresh [] (IrSource.inputs s) ≡ just Γ
  → initᶜ s w ≡ just st → StoreTyped Γ (CircuitState.mem st)
circuit-init-store s w {st} inserted initialized =
  declare-store w (IrSource.inputs s) [] ∅ (λ _ _ ()) inserted (init-memory s w {st} initialized)

circuit-trace-extends : ∀ {s w st final} is Γ {Γ′}
  → Trace s w st (map lower is) final
  → StoreTyped Γ (CircuitState.mem st)
  → fold-check (producer-step (IrSource.outputs s)) Γ is ≡ just Γ′
  → Extends Γ (CircuitState.mem st) (CircuitState.mem final)
circuit-trace-extends [] Γ CircuitTrace.end typed producer id t found = refl
circuit-trace-extends {s} {w} {st} (i ∷ is) Γ (CircuitTrace.next {st′ = mid} ok rest)
  typed producer id t found with fold-cons (producer-step (IrSource.outputs s)) Γ i is producer
... | next-env , head , tail =
  trans (circuit-trace-extends is next-env rest (CircuitFrame.typed-after frame) tail
          id t (CircuitFrame.keeps-types frame id t found))
        (CircuitFrame.extends frame id t found)
  where frame = circuit-step-frame s w st i mid Γ typed head ok
