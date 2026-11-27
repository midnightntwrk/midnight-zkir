{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.ProducerSupport (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Types ⋯
open import zkir-v4.Syntax ⋯
open import zkir-v4.Semantics ⋯ hiding (write)
open import zkir-v4.Circuit ⋯ using (CircuitWitness; even4; select-supported)
open import zkir-v4.CircuitBridge ⋯ using (Agrees)
open import zkir-v4.ForwardShape ⋯ using
  (Supported; Aligns; GuardedCell; shared-ok; special-ok; bit-constraint-ok; division-ok; recon-ok;
   public-ok; private-ok; impact-ok; slot-ok; prepare-ok; fold-ok; expose-ok; output-ok)
open import zkir-v4.Producer ⋯
open import zkir-v4.ProducerStore ⋯ using (StoreTyped; typed-operand; demand-success)
  renaming (bind-success to unbind)
open import zkir-v4.ProducerValuesHelpers ⋯ using (equality)
open import zkir-v4.CircuitPure ⋯ using (Special; assertion; comparison; selection; equality-test; equality-constraint; parts;
  persistent; keccak-hash; sha-hash)
open import zkir-v4.Validation ⋯ using (resolve-vk)
open import Data.Bool as B using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ; _+_; _^_; _%_; _≤_; _<_; _≤?_; _<?_)
open import Data.Nat.Properties using
  (<⇒≤; ≤-trans; <-≤-trans; ^-monoʳ-≤; m≤m+n; m≤m⊔n; ≤ᵇ⇒≤)
open import Data.Product using (_×_; _,_; ∃; proj₁)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Relation.Nullary using (Dec; yes; no; ¬_)

private
  passed : ∀ {A P : Set} (d : Dec P) (m : Maybe A) {a}
         → guardD d m ≡ just a → P × m ≡ just a
  passed (yes p) m ok = p , ok
  passed (no _) m ()

  is-one : ∀ x → to𝔹 x ≡ just true → x ≡ 1ᶠ
  is-one x ok with x ≟ᶠ 0ᶠ
  ... | yes _ with () ← ok
  is-one x ok | no _ with x ≟ᶠ 1ᶠ
  ... | no _ with () ← ok
  ... | yes equality = equality

assert-supported : ∀ {p s st x after} → step p s st (assert x) ≡ just after
                 → Special (State.mem st) (assert x)
assert-supported {st = st} {x} ok with unbind (compute (State.mem st) (assert x)) _ ok
... | _ , computed , _ with unbind (resolve𝔹 (State.mem st) x) _ computed
...   | false , _ , ()
...   | true , guard , _ with unbind (resolveᶠ (State.mem st) x) to𝔹 guard
...     | v , resolved , bit rewrite is-one v bit = assertion true resolved

private
  padded-bound : ∀ n → n ≤ even4 n
  padded-bound n = ≤-trans (m≤m+n n (n % 2)) (m≤m⊔n (n + n % 2) 4)

  pad-range : ∀ {v n} → v < 2 ^ n → v < 2 ^ even4 n
  pad-range {n = n} within = <-≤-trans within (^-monoʳ-≤ 2 (padded-bound n))

comparison-supported : ∀ {p s st a b n o after}
                     → step p s st (less-than a b n o) ≡ just after
                     → Special (State.mem st) (less-than a b n o)
comparison-supported {st = st} {a} {b} {n} {o} ok
  with unbind (compute (State.mem st) (less-than a b n o)) _ ok
... | _ , computed , _ with unbind (resolveᶠ (State.mem st) a) _ computed
...   | x , x-resolved , rest with unbind (resolveᶠ (State.mem st) b) _ rest
...     | y , y-resolved , bounds with passed (n <? FR-BITS) _ bounds
...       | width , limits with passed (valFr x <? 2 ^ n) _ limits
...         | x-in , y-limit with passed (valFr y <? 2 ^ n) _ y-limit
...           | y-in , _ =
  comparison x-resolved y-resolved width x-in y-in (pad-range {n = n} x-in) (pad-range {n = n} y-in)

bit-supported : ∀ {p s st x n after} → step p s st (constrain-bits x n) ≡ just after → n ≤ FR-BITS
bit-supported {n = n} ok with n <? FR-BITS
... | yes bound = <⇒≤ bound
... | no _ with () ← ok

division-supported : ∀ {p s st x n os after}
                   → step p s st (div-mod-power-of-two x n os) ≡ just after → n ≤ FR-BITS
division-supported {n = n} ok with n ≤? 248
... | yes bound = ≤-trans bound (≤ᵇ⇒≤ 248 FR-BITS _)
... | no _ with () ← ok

recon-supported : ∀ {p s st d m n o after}
                → step p s st (reconstitute-field d m n o) ≡ just after → n ≤ FR-BITS
recon-supported {n = n} ok with n ≤? 248
... | yes bound = ≤-trans bound (≤ᵇ⇒≤ 248 FR-BITS _)
... | no _ with () ← ok

-- FAB parsing and verifier preparation are separate primitive contracts.
-- Off-circuit preparation may skip parsing an inactive key.
PrepareDomain : IrSource → State → Operand → List Byte → List Operand → Identifier → Set
PrepareDomain src st g h ops id =
  ∀ flag vs blob key
    → resolve𝔹 (State.mem st) g ≡ just flag
    → resolve-all-Fr (State.mem st) ops ≡ just vs
    → State.proofs st id ≡ just blob
    → resolve-vk h (IrSource.inner-vks src) ≡ just key
    → prepare-compatible key vs blob flag ≡ true
      × (flag ≡ false → key-well-formed key ≡ true)

ForwardDomain : IrSource → State → Instruction → Set
ForwardDomain src st (persistent-hash a ops _) = ∀ vs → resolve-all-Fr (State.mem st) ops ≡ just vs
  → persistent-hash-circuit-fn a vs ≡ persistent-hash-fn a vs
ForwardDomain src st (keccak256 a ops _) = ∀ vs → resolve-all-Fr (State.mem st) ops ≡ just vs
  → keccak-circuit-fn a vs ≡ keccak-fn a vs
ForwardDomain src st (sha512 a ops _) = ∀ vs → resolve-all-Fr (State.mem st) ops ≡ just vs
  → sha512-circuit-fn a vs ≡ sha512-fn a vs
ForwardDomain src st (prepare-verification g h ops id _) = PrepareDomain src st g h ops id
ForwardDomain src st _ = ⊤

private
  active-parses : ∀ key (result : Maybe Accumulator) {acc}
                → (if key-well-formed key then result else nothing) ≡ just acc
                → key-well-formed key ≡ true
  active-parses key result ok with key-well-formed key
  ... | true = refl
  ... | false with () ← ok

successful-prepare-key : ∀ {p s st g h ops id out after}
                       → PrepareDomain s st g h ops id
                       → step p s st (prepare-verification g h ops id out) ≡ just after
                       → ∀ key → resolve-vk h (IrSource.inner-vks s) ≡ just key
                               → key-well-formed key ≡ true
successful-prepare-key {s = s} {st} {g} {h} {ops} {id} domain ok key key-resolved
  with unbind (prepare-result s st g h ops id) _ ok
... | acc , prepared , _ with unbind (resolve𝔹 (State.mem st) g) _ prepared
...   | flag , bit , looked with unbind (resolve-all-Fr (State.mem st) ops) _ looked
...     | vs , vals , found with unbind (State.proofs st id) _ found
...       | blob , proof , keyed with unbind (resolve-vk h (IrSource.inner-vks s)) _ keyed
...         | found-key , found , result with refl ← just-injective (trans (sym found) key-resolved)
  with flag
...           | true = active-parses found-key (prepare-active found-key vs blob) result
...           | false with domain false vs blob found-key bit vals proof found
...             | _ , parsed = parsed refl

private
  -- The first premise of each checked sequence uses the same unit value.
  before : ∀ {A : Set} (unit : Maybe ⊤) (k : Maybe A) {v}
         → (unit >> k) ≡ just v → (unit ≡ just tt) × (k ≡ just v)
  before unit k ok with unbind unit (λ _ → k) ok
  ... | tt , passed-unit , tail = passed-unit , tail

  different-type : ∀ t u → B.not (equal t u) ≡ true → ¬ (t ≡ u)
  different-type t u ok with t ≟T u
  ... | yes _ with () ← ok
  ... | no different = different

  select-type : ∀ t → selectable t ≡ true → select-supported t ≡ true
  select-type native ok = ok
  select-type (bytes _) ok = ok
  select-type byte ok = ok
  select-type bool ok = ok
  select-type accumulator ok = ok
  select-type jubjub-point ok = ok
  select-type jubjub-scalar ok = ok
  select-type secp256k1-point ok = ok
  select-type secp256k1-base ok = ok
  select-type secp256k1-scalar ok = ok
  select-type secp256r1-point ok = ok
  select-type secp256r1-base ok = ok
  select-type secp256r1-scalar ok = ok
  select-type curve25519-point ok = ok
  select-type curve25519-base ok = ok
  select-type curve25519-scalar ok = ok

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

module _ (sig : List IrType) (Γ : Env) (m : Mem) (typed : StoreTyped Γ m) where
  private
    expect-type : ∀ t op → expect sig Γ t op ≡ just tt → ty sig Γ op ≡ just t
    expect-type t op ok with unbind (ty sig Γ op) (λ u → demand (equal t u)) ok
    ... | u , found , check rewrite equality {t} {u} check = found

    operand : ∀ op t → ty sig Γ op ≡ just t → ∃ λ v → resolve m op ≡ just v × typeof v ≡ t
    operand op t = typed-operand {signature = sig} {op = op} typed

    native-operand : ∀ op → expect sig Γ native op ≡ just tt
                   → ∃ λ x → resolve m op ≡ just (val-native x)
    native-operand op ok with operand op native (expect-type native op ok)
    ... | v , resolved , has-type with native-value v has-type
    ...   | x , refl = x , resolved

    natives-resolve : ∀ ops {checks} → check-list (expect sig Γ native) ops ≡ just checks
                    → ∃ λ vs → resolve-all-Fr m ops ≡ just vs
    natives-resolve [] _ = [] , refl
    natives-resolve (op ∷ ops) ok with unbind (expect sig Γ native op) _ ok
    ... | tt , head-ok , rest with unbind (check-list (expect sig Γ native) ops) _ rest
    ...   | _ , tail-ok , _ with native-operand op head-ok | natives-resolve ops tail-ok
    ...     | x , x-ok | vs , vs-ok rewrite x-ok | vs-ok = x ∷ vs , refl

  impact-supported : ∀ g ops {bs} → bindings sig Γ (impact g ops) ≡ just bs
                   → ∃ λ vs → resolve-all-Fr m ops ≡ just vs
  impact-supported g ops ok
    with before (expect sig Γ native g >> expect-all sig Γ native ops) (just []) ok
  ... | checks , _ with before (expect sig Γ native g) (expect-all sig Γ native ops) checks
  ...   | _ , operands-ok with unbind (check-list (expect sig Γ native) ops) _ operands-ok
  ...     | _ , checked , _ = natives-resolve ops checked

  parts-supported : ∀ lo hi o {bs} → bindings sig Γ (bytes32-from-low-high (lo , hi) o) ≡ just bs
                  → Special m (bytes32-from-low-high (lo , hi) o)
  parts-supported lo hi o ok with before (expect sig Γ native lo >> expect sig Γ native hi) (one sig Γ o bytes32) ok
  ... | lo-hi-ok , _ with before (expect sig Γ native lo) (expect sig Γ native hi) lo-hi-ok
  ...   | _ , hi-ok with native-operand hi hi-ok
  ...     | x , resolved = parts x resolved

  selection-supported : ∀ g a b o {bs} → bindings sig Γ (cond-select g a b o) ≡ just bs
                      → Special m (cond-select g a b o)
  selection-supported g a b o ok
    with before (expect sig Γ native g) (binary sig Γ selectable a b o) ok
  ... | _ , rest with unbind (ty sig Γ a) _ rest
  ...   | t , a-type , checks with before (expect sig Γ t b >> demand (selectable t)) (one sig Γ o t) checks
  ...     | selected , _ with before (expect sig Γ t b) (demand (selectable t)) selected
  ...       | b-check , enabled with operand a t a-type | operand b t (expect-type t b b-check)
  ...         | x , x-ok , xt | y , y-ok , _ =
    selection x-ok y-ok (subst (λ t → select-supported t ≡ true) (sym xt)
      (select-type t (demand-success {selectable t} enabled)))

  private
    equality-operands : ∀ a b (out : IrType → Maybe Env) {bs}
                      → (ty sig Γ a >>= (λ t → expect sig Γ t b >> (demand (B.not (equal t accumulator)) >> out t)))
                        ≡ just bs
                      → ∃ λ x → ∃ λ y → resolve m a ≡ just x × resolve m b ≡ just y
                      × (typeof x ≡ typeof y) × ¬ (typeof x ≡ accumulator)
    equality-operands a b out ok with unbind (ty sig Γ a) _ ok
    ... | t , a-type , checks with before (expect sig Γ t b) (demand (B.not (equal t accumulator)) >> out t) checks
    ...   | b-check , rest with before (demand (B.not (equal t accumulator))) (out t) rest
    ...     | allowed , _ with operand a t a-type | operand b t (expect-type t b b-check)
    ...       | x , x-ok , xt | y , y-ok , yt =
      x , y , x-ok , y-ok , trans xt (sym yt) ,
      λ x-acc → different-type t accumulator (demand-success {B.not (equal t accumulator)} allowed)
        (trans (sym xt) x-acc)

  equality-test-supported : ∀ a b o {bs} → bindings sig Γ (test-eq a b o) ≡ just bs
                          → Special m (test-eq a b o)
  equality-test-supported a b o ok with equality-operands a b (λ _ → one sig Γ o native) ok
  ... | _ , _ , x-ok , y-ok , same , _ = equality-test x-ok y-ok same

  equality-constraint-supported : ∀ a b {bs} → bindings sig Γ (constrain-eq a b) ≡ just bs
                                → Special m (constrain-eq a b)
  equality-constraint-supported a b ok with equality-operands a b (λ _ → just []) ok
  ... | _ , _ , x-ok , y-ok , same , non-acc = equality-constraint x-ok y-ok same non-acc

-- The typed SSA trace supplies each alignment premise from the writes
-- that this step made and their preservation by all following steps.
record WitnessCells (s : IrSource) (w : CircuitWitness) (st : State) (i : Instruction) : Set where
  field
    public-cell : ∀ {g t id} → i ≡ public-input g t id → GuardedCell w st g id t (State.pto-rem st)
    private-cell : ∀ {g t id} → i ≡ private-input g t id → GuardedCell w st g id t (State.priv-rem st)
    prepared-cell : ∀ {g h ops id out} → i ≡ prepare-verification g h ops id out
      → ∀ acc → prepare-result s st g h ops id ≡ just acc → Agrees w out (val-accumulator acc)
    folded-cell : ∀ {ops out} → i ≡ accumulate ops out
      → ∀ acc → fold-result (State.mem st) ops ≡ just acc → Agrees w out (val-accumulator acc)

support-step : ∀ {s p w st after i Γ bs}
        → StoreTyped Γ (State.mem st)
        → bindings (IrSource.outputs s) Γ i ≡ just bs
        → step p s st i ≡ just after
        → (∀ checked → Aligns w st i checked)
        → WitnessCells s w st i
        → ForwardDomain s st i
        → Supported s w st i
support-step {i = encode _ _} _ _ _ align _ _ = shared-ok refl (align _)
support-step {s} {p} {w} {st} {after} {assert op} _ _ succeeded align _ _ =
  special-ok (assert-supported {p = p} {s = s} {st = st} {x = op} {after = after} succeeded) (align _)
support-step {s} {_} {_} {st} {_} {cond-select g a b o} {Γ} typed inferred _ align _ _ =
  special-ok (selection-supported (IrSource.outputs s) Γ (State.mem st) typed g a b o inferred) (align _)
support-step {s} {p} {_} {st} {after} {constrain-bits x n} _ _ succeeded align _ _ =
  bit-constraint-ok (bit-supported {p = p} {s = s} {st = st} {x = x} {n = n} {after = after} succeeded) (align _)
support-step {s} {_} {_} {st} {_} {constrain-eq a b} {Γ} typed inferred _ align _ _ =
  special-ok (equality-constraint-supported (IrSource.outputs s) Γ (State.mem st) typed a b inferred) (align _)
support-step {i = constrain-to-boolean _} _ _ _ align _ _ = shared-ok refl (align _)
support-step {i = copy _ _} _ _ _ align _ _ = shared-ok refl (align _)
support-step {s} {_} {_} {st} {_} {impact g ops} {Γ} typed inferred _ _ _ _ =
  impact-ok (λ _ → impact-supported (IrSource.outputs s) Γ (State.mem st) typed g ops inferred)
support-step {i = ec-mul _ _ _} _ _ _ align _ _ = shared-ok refl (align _)
support-step {i = ec-mul-generator _ _} _ _ _ align _ _ = shared-ok refl (align _)
support-step {i = hash-to-curve _ _} _ _ _ align _ _ = shared-ok refl (align _)
support-step {i = into-coordinates _ _} _ _ _ align _ _ = shared-ok refl (align _)
support-step {i = from-coordinates _ _} _ _ _ align _ _ = shared-ok refl (align _)
support-step {i = into-bytes32 _ _} _ _ _ align _ _ = shared-ok refl (align _)
support-step {i = from-bytes32 _ _ _} _ _ _ align _ _ = shared-ok refl (align false)
support-step {i = reverse-bytes _ _} _ _ _ align _ _ = shared-ok refl (align false)
support-step {i = bytes32-into-low-high _ _} _ _ _ align _ _ = shared-ok refl (align false)
support-step {s} {_} {_} {st} {_} {bytes32-from-low-high (lo , hi) o} {Γ} typed inferred _ align _ _ =
  special-ok (parts-supported (IrSource.outputs s) Γ (State.mem st) typed lo hi o inferred) (align false)
support-step {s} {p} {_} {st} {after} {div-mod-power-of-two x n os} _ _ succeeded align _ _ =
  division-ok (division-supported {p = p} {s = s} {st = st} {x = x} {n = n} {os = os} {after = after} succeeded) (align _)
support-step {s} {p} {_} {st} {after} {reconstitute-field d m n o} _ _ succeeded align _ _ =
  recon-ok (recon-supported {p = p} {s = s} {st = st} {d = d} {m = m} {n = n} {o = o} {after = after} succeeded) (align _)
support-step {i = transient-hash _ _} _ _ _ align _ _ = shared-ok refl (align _)
support-step {i = persistent-hash _ _ _} _ _ _ align _ domain = special-ok (persistent domain) (align _)
support-step {i = keccak256 _ _ _} _ _ _ align _ domain = special-ok (keccak-hash domain) (align _)
support-step {s} {_} {_} {st} {_} {test-eq a b o} {Γ} typed inferred _ align _ _ =
  special-ok (equality-test-supported (IrSource.outputs s) Γ (State.mem st) typed a b o inferred) (align _)
support-step {i = add _ _ _} _ _ _ align _ _ = shared-ok refl (align _)
support-step {i = mul _ _ _} _ _ _ align _ _ = shared-ok refl (align _)
support-step {i = neg _ _} _ _ _ align _ _ = shared-ok refl (align _)
support-step {i = inv _ _} _ _ _ align _ _ = shared-ok refl (align _)
support-step {i = not _ _} _ _ _ align _ _ = shared-ok refl (align _)
support-step {s} {p} {_} {st} {after} {less-than a b n o} _ _ succeeded align _ _ =
  special-ok (comparison-supported
    {p = p} {s = s} {st = st} {a = a} {b = b} {n = n} {o = o} {after = after} succeeded) (align _)
support-step {i = jubjub-scalar-from-native _ _} _ _ _ align _ _ = shared-ok refl (align _)
support-step {i = public-input _ _ _} _ _ _ _ cells _ = public-ok (WitnessCells.public-cell cells refl)
support-step {i = private-input _ _ _} _ _ _ _ cells _ = private-ok (WitnessCells.private-cell cells refl)
support-step {i = circuit-output _} _ _ _ _ _ _ = output-ok
support-step {i = slice _ _ _ _} _ _ _ align _ _ = shared-ok refl (align _)
support-step {i = nth _ _ _} _ _ _ align _ _ = shared-ok refl (align _)
support-step {i = concat _ _} _ _ _ align _ _ = shared-ok refl (align _)
support-step {i = reverse _ _} _ _ _ align _ _ = shared-ok refl (align false)
support-step {i = load-constant _ _ _} _ _ _ align _ _ = shared-ok refl (align _)
support-step {i = sha512 _ _ _} _ _ _ align _ domain = special-ok (sha-hash domain) (align _)
support-step {i = and _ _} _ _ _ align _ _ = shared-ok refl (align _)
support-step {i = or _ _} _ _ _ align _ _ = shared-ok refl (align _)
support-step {i = xor _ _} _ _ _ align _ _ = shared-ok refl (align _)
support-step {i = to-bytes _ _} _ _ _ align _ _ = shared-ok refl (align _)
support-step {i = from-bytes _ _ _} _ _ _ align _ _ = shared-ok refl (align false)
support-step {i = bytes-into-natives _ _} _ _ _ align _ _ = shared-ok refl (align _)
support-step {i = bytes-from-natives _ _ _} _ _ _ align _ _ = shared-ok refl (align _)
support-step {i = inner-proof _ _} _ _ _ _ _ _ = slot-ok
support-step {s} {p} {_} {st} {after} {prepare-verification g h ops id out} _ _ succeeded _ cells domain =
  prepare-ok
    (successful-prepare-key {p = p} {s = s} {st = st} {g = g} {h = h} {ops = ops}
      {id = id} {out = out} {after = after} domain succeeded)
    (λ flag vs blob key bit vals proof vk → proj₁ (domain flag vs blob key bit vals proof vk)) (WitnessCells.prepared-cell cells refl)
support-step {i = accumulate _ _} _ _ _ _ cells _ = fold-ok (WitnessCells.folded-cell cells refl)
support-step {i = verify-accumulator _} _ _ _ _ _ _ = expose-ok
