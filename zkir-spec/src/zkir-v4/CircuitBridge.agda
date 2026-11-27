{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.CircuitBridge (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Circuit ⋯
open import zkir-v4.Semantics ⋯ using (State; ProofPreimage; step)
open import zkir-v4.Operations ⋯ hiding (write)
open import zkir-v4.Syntax ⋯
open import zkir-v4.Validation ⋯ using (resolve-vk)
open import zkir-v4.Types ⋯
open import zkir-v4.Encoding ⋯ using () renaming (encode to encode-value)

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Nat using (_≤_; _≤?_)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Negation using (contradiction)

guard-pass : ∀ {P A : Set} (d : Dec P) → P → (a : Maybe A) → guardD d a ≡ a
guard-pass (yes _) _ a = refl
guard-pass (no np) p a = contradiction p np

-- Rust permits omitted entries at checked computed writes. If an
-- entry is supplied, an honest witness agrees with the computed value.
Agrees : CircuitWitness → Identifier → IrValue → Set
Agrees w name value = (CircuitWitness.assign w name ≡ nothing) ⊎
                      (CircuitWitness.assign w name ≡ just value)

WriteAgreement : Bool → CircuitWitness → List (Identifier × IrValue) → Set
WriteAgreement false _ _ = ⊤
WriteAgreement true _ [] = ⊤
WriteAgreement true w ((id , v) ∷ writes) = Agrees w id v × WriteAgreement true w writes

check-agreed : ∀ w id v → Agrees w id v → check-assignment w id v ≡ just v
check-agreed w id v (inj₁ absent) rewrite absent = refl
check-agreed w id v (inj₂ present) rewrite present
  | guard-pass (typeof v ≟T typeof v) refl
      (guardD (encode-value v ≟LFr encode-value v) (just v))
  | guard-pass (encode-value v ≟LFr encode-value v) refl (just v) = refl

write-cells-agreed : ∀ checked w m writes
                   → WriteAgreement checked w writes
                   → write-cells checked w m writes ≡ just (apply-writes m writes)
write-cells-agreed checked w m [] _ = refl
write-cells-agreed false w m ((id , v) ∷ writes) _ =
  write-cells-agreed false w (ins id v m) writes tt
write-cells-agreed true w m ((id , v) ∷ writes) (head-ok , tail-ok)
  rewrite check-agreed w id v head-ok =
  write-cells-agreed true w (ins id v m) writes tail-ok

write-agreed : ∀ checked w st writes
               → WriteAgreement checked w writes
               → write checked w st writes
                   ≡ just (record st { mem = apply-writes (CircuitState.mem st) writes })
write-agreed checked w st writes ok
  rewrite write-cells-agreed checked w (CircuitState.mem st) writes ok = refl

shared-forward : ∀ src w st i writes
                 → compute (CircuitState.mem st) i ≡ just writes
                 → WriteAgreement (check-shared-writes i) w writes
                 → stepᶜ src w st (shared i)
                    ≡ just (record st { mem = apply-writes (CircuitState.mem st) writes })
shared-forward src w st i writes computed agreed
  rewrite computed = write-agreed (check-shared-writes i) w st writes agreed

bounded-forward : ∀ src w st i writes bits
                 → bits ≤ FR-BITS
                 → bounded-compute (CircuitState.mem st) i ≡ just writes
                 → WriteAgreement true w writes
                 → stepᶜ src w st (bounded-bits bits i)
                    ≡ just (record st { mem = apply-writes (CircuitState.mem st) writes })
bounded-forward src w st i writes bits within computed agreed
  rewrite computed
        | guard-pass (bits ≤? FR-BITS) within (write true w st writes) =
  write-agreed true w st writes agreed

private
  just-injective : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
  just-injective refl = refl

  bind-success : ∀ {A B : Set} (a : Maybe A) (f : A → Maybe B) {b}
               → (a >>= f) ≡ just b
               → Σ A λ x → (a ≡ just x) × (f x ≡ just b)
  bind-success nothing _ ()
  bind-success (just x) _ ok = x , refl , ok

  guard-success : ∀ {P A : Set} (d : Dec P) (a : Maybe A) {x}
                → guardD d a ≡ just x → P × (a ≡ just x)
  guard-success (yes p) _ ok = p , ok
  guard-success (no _) _ ()

  assignment-value : ∀ w id v cell
                    → check-assignment w id v ≡ just cell → v ≡ cell
  assignment-value w id v cell ok with CircuitWitness.assign w id
  ... | nothing = just-injective ok
  ... | just expected
    with guard-success (typeof v ≟T typeof expected) _ ok
  ...   | _ , typed with guard-success (encode-value v ≟LFr encode-value expected) _ typed
  ...     | _ , stored = just-injective stored

  written-values : ∀ checked w m writes {result}
                   → write-cells checked w m writes ≡ just result
                   → result ≡ apply-writes m writes
  written-values _ _ _ [] refl = refl
  written-values false w m ((id , v) ∷ writes) ok =
    written-values false w (ins id v m) writes ok
  written-values true w m ((id , v) ∷ writes) ok
    with bind-success (check-assignment w id v)
           (λ cell → write-cells true w (ins id cell m) writes) ok
  ... | cell , head-ok , tail-ok
    rewrite assignment-value w id v cell head-ok =
      written-values true w (ins id cell m) writes tail-ok

write-backward : ∀ checked w st writes {result}
                 → write checked w st writes ≡ just result
                 → result ≡ record st { mem = apply-writes (CircuitState.mem st) writes }
write-backward checked w st writes ok
  with bind-success (write-cells checked w (CircuitState.mem st) writes)
         (λ m → just (record st { mem = m })) ok
... | _ , writes-ok , state-ok rewrite written-values checked w (CircuitState.mem st) writes writes-ok =
  sym (just-injective state-ok)

shared-backward : ∀ src w st i {result}
                  → stepᶜ src w st (shared i) ≡ just result
                  → Σ (List (Identifier × IrValue)) λ writes →
                    (compute (CircuitState.mem st) i ≡ just writes)
                    × (result ≡ record st { mem = apply-writes (CircuitState.mem st) writes })
shared-backward src w st i ok
  with bind-success (compute (CircuitState.mem st) i) (write (check-shared-writes i) w st) ok
... | writes , computed , wrote =
  writes , computed , write-backward (check-shared-writes i) w st writes wrote

bounded-backward : ∀ src w st i bits {result}
                   → stepᶜ src w st (bounded-bits bits i) ≡ just result
                   → (bits ≤ FR-BITS) ×
                     Σ (List (Identifier × IrValue)) λ writes →
                       (bounded-compute (CircuitState.mem st) i ≡ just writes)
                       × (result ≡ record st { mem = apply-writes (CircuitState.mem st) writes })
bounded-backward src w st i bits ok
  with guard-success (bits ≤? FR-BITS) _ ok
... | within , step-ok
  with bind-success (bounded-compute (CircuitState.mem st) i) (write true w st) step-ok
...   | writes , computed , wrote =
  within , writes , computed , write-backward true w st writes wrote

-- Assert's circuit gadget accepts every nonzero native value.
assert-forward : ∀ src w st op x
                 → resolveᶠ (CircuitState.mem st) op ≡ just x
                 → ¬ (x ≡ 0ᶠ)
                 → stepᶜ src w st (non-zero op) ≡ just st
assert-forward src w st op x value nz rewrite value with x ≟ᶠ 0ᶠ
... | yes z = contradiction z nz
... | no _ = refl

assert-backward : ∀ src w st op {result}
                  → stepᶜ src w st (non-zero op) ≡ just result
                  → Σ Fr λ x → (resolveᶠ (CircuitState.mem st) op ≡ just x)
                             × ¬ (x ≡ 0ᶠ) × (result ≡ st)
assert-backward src w st op ok with resolveᶠ (CircuitState.mem st) op in value
... | nothing with ok
...   | ()
assert-backward src w st op ok | just x with x ≟ᶠ 0ᶠ
... | yes _ with ok
...   | ()
assert-backward src w st op ok | just x | no nz = x , refl , nz , sym (just-injective ok)

impact-forward : ∀ src w st g ops active values
                 → resolve𝔹 (CircuitState.mem st) g ≡ just active
                 → resolve-all-Fr (CircuitState.mem st) ops ≡ just values
                 → stepᶜ src w st (publish-impact g ops)
                    ≡ just (record st { pis = CircuitState.pis st ++
                           (if active then values else map (λ _ → 0ᶠ) ops) })
impact-forward src w st g ops active values g-ok vals-ok rewrite g-ok | vals-ok = refl

expose-forward : ∀ src w st op acc
                 → resolve-acc (CircuitState.mem st) op ≡ just acc
                 → stepᶜ src w st (publish-acc op)
                    ≡ just (record st { accs = CircuitState.accs st ++ (acc ∷ []) })
expose-forward src w st op acc eq rewrite eq = refl

fold-forward : ∀ src w st ops out a b rest acc
               → resolve-accs (CircuitState.mem st) ops ≡ just (a ∷ b ∷ rest)
               → fold-accumulators (a ∷ b ∷ rest) ≡ just acc
               → Agrees w out (val-accumulator acc)
               → stepᶜ src w st (fold-accs ops out)
                  ≡ just (record st { mem = ins out (val-accumulator acc) (CircuitState.mem st) })
fold-forward src w st ops out a b rest acc values folded agrees
  rewrite values | folded = write-agreed true w st ((out , val-accumulator acc) ∷ []) (agrees , tt)

-- This is the local cryptographic premise used by the prepare gadget.
-- The verifier gadget runs and the fixed key parses for either guard.
prepare-forward : ∀ src w st guard hash ops proof out active instance-values blob key acc
                → resolve𝔹 (CircuitState.mem st) guard ≡ just active
                → resolve-all-Fr (CircuitState.mem st) ops ≡ just instance-values
                → CircuitState.proofs st proof ≡ just blob
                → resolve-vk hash (IrSource.inner-vks src) ≡ just key
                → key-well-formed key ≡ true
                → prepare-circuit key instance-values blob active ≡ just acc
                → Agrees w out (val-accumulator acc)
                → stepᶜ src w st (prepare-proof guard hash ops proof out)
                   ≡ just (record st { mem = ins out (val-accumulator acc) (CircuitState.mem st) })
prepare-forward src w st guard hash ops proof out active instance-values blob key acc
  g-ok inst-ok proof-ok key-ok parse-ok prepared agrees
  rewrite g-ok | inst-ok | proof-ok | key-ok | parse-ok | prepared =
  write-agreed true w st ((out , val-accumulator acc) ∷ []) (agrees , tt)

-- At each point the modes have the same current value and proof
-- stores.  The circuit cursor runs over retained (normalized) slots.
view : State → List (List Byte) → CircuitState
view st retained = mk-state
  (State.mem st)
  (State.proofs st)
  retained
  (State.exposed st)
  (State.pis st)
  (State.outs st)

Agreement : ProofPreimage → IrSource → CircuitWitness → State → List (List Byte)
            → Instruction → State → List (List Byte) → Set
Agreement p src w st before i after remaining =
  (step p src st i ≡ just after) ×
  (stepᶜ src w (view st before) (lower i) ≡ just (view after remaining))

witness-cell-backward : ∀ src w st t id {target}
                       → stepᶜ src w st (witness-cell t id) ≡ just target
                       → Σ IrValue λ v →
                           (CircuitWitness.assign w id ≡ just v)
                         × (typeof v ≡ t)
                         × (target ≡ record st { mem = ins id v (CircuitState.mem st) })
witness-cell-backward src w st t id ok
  with bind-success (CircuitWitness.assign w id >>= assign-value t) (write-one w st id) ok
... | v , assigned-and-typed , wrote
  with bind-success (CircuitWitness.assign w id) (assign-value t) assigned-and-typed
...   | actual , assigned , check-type
  with guard-success (typeof actual ≟T t) (just actual) check-type
...     | typed , refl =
  actual , assigned , typed , write-backward true w st ((id , actual) ∷ []) wrote
