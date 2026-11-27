{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.ProducerStep (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Types ⋯
open import zkir-v4.Syntax ⋯
open import zkir-v4.Semantics ⋯
open import zkir-v4.Producer ⋯
open import zkir-v4.ProducerStore ⋯
open import zkir-v4.Encoding ⋯ using (decode)
open import zkir-v4.EncodingProperties ⋯ using (decode-typed)
open import zkir-v4.CircuitProof ⋯ using (apply)
open import zkir-v4.CircuitEffects ⋯ using (ReadValue)

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; take; drop; length; map)
open import Data.List.Properties using (length-replicate)
import Data.Nat
open import Function using (_∘_)
open import Data.List.Relation.Unary.All using (All)
  renaming ([] to []∀; _∷_ to _∷∀_)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; ∃)
open import Data.Sum using (inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (yes; no)

ComputeTypes : Set
ComputeTypes = ∀ signature Γ m i {bs ws} →
  StoreTyped Γ m → bindings signature Γ i ≡ just bs →
  compute m i ≡ just ws → writes-types ws ≡ bs

record StepWrites (st : State) (i : Instruction) (after : State) (bs : Env) : Set where
  constructor writes-step
  field
    values : List (Identifier × IrValue)
    types : writes-types values ≡ bs
    memory : State.mem after ≡ apply-writes (State.mem st) values
    computed : ∀ ws → compute (State.mem st) i ≡ just ws → ws ≡ values

private
  default-type : ∀ t → typeof (default-val t) ≡ t
  default-type native = refl
  default-type (bytes n) = cong bytes (length-replicate n)
  default-type byte = refl
  default-type bool = refl
  default-type accumulator = refl
  default-type jubjub-point = refl
  default-type jubjub-scalar = refl
  default-type secp256k1-point = refl
  default-type secp256k1-base = refl
  default-type secp256k1-scalar = refl
  default-type secp256r1-point = refl
  default-type secp256r1-base = refl
  default-type secp256r1-scalar = refl
  default-type curve25519-point = refl
  default-type curve25519-base = refl
  default-type curve25519-scalar = refl

read-typed : ∀ active t raw v → ReadValue active t raw v → typeof v ≡ t
read-typed false t raw v refl = default-type t
read-typed true t raw v decoded = decode-typed {t = t} decoded

final-bindings : ∀ {A B : Set} {x : B} {xs : Maybe A} {bs}
  → (xs >> just x) ≡ just bs → x ≡ bs
final-bindings {xs = nothing} ()
final-bindings {xs = just _} eq = just-injective eq

output-binding : ∀ sig Γ xs {bs}
  → bindings sig Γ (circuit-output xs) ≡ just bs → [] ≡ bs
output-binding sig Γ xs ok
  with bind-success (check-list (ty sig Γ) xs) _ ok
... | ts , _ , checked = final-bindings {xs = demand (eq-types ts sig)} checked

prepare-binding : ∀ sig Γ g h ops pr id {bs}
  → bindings sig Γ (prepare-verification g h ops pr id) ≡ just bs
  → (id ⦂ accumulator) ∷ [] ≡ bs
prepare-binding sig Γ g h ops pr id ok =
  final-bindings {xs = expect sig Γ native g >> expect-all sig Γ native ops} ok

fold-binding : ∀ sig Γ ops id {bs}
  → bindings sig Γ (accumulate ops id) ≡ just bs
  → (id ⦂ accumulator) ∷ [] ≡ bs
fold-binding sig Γ ops id ok =
  final-bindings {xs = demand (2 Data.Nat.≤ᵇ length ops) >> expect-all sig Γ accumulator ops} ok

private
  unchanged : ∀ {A : Set} st i after {bs} → (x : Maybe A) (f : A → Maybe State)
    → (∀ a st′ → f a ≡ just st′ → State.mem st′ ≡ State.mem st)
    → (x >>= f) ≡ just after → [] ≡ bs
    → (∀ ws → compute (State.mem st) i ≡ just ws → ws ≡ [])
    → StepWrites st i after bs
  unchanged st i after x f same ok typed absent with bind-success x f ok
  ... | a , _ , applied = writes-step [] typed (same a after applied) absent

  pure-writes : ComputeTypes → ∀ s st i after Γ {bs}
    → StoreTyped Γ (State.mem st) → bindings (IrSource.outputs s) Γ i ≡ just bs
    → (compute (State.mem st) i >>= λ ws → just (apply st ws)) ≡ just after
    → StepWrites st i after bs
  pure-writes typed-operations s st i after Γ typed bs-ok ok
    with bind-success (compute (State.mem st) i) _ ok
  ... | ws , computed , state-ok = writes-step ws
    (typed-operations (IrSource.outputs s) Γ (State.mem st) i typed bs-ok computed)
    (cong State.mem (sym (just-injective state-ok)))
    (λ _ other → just-injective (trans (sym other) computed))

step-writes : ComputeTypes → ∀ p s st i after Γ {bs}
  → StoreTyped Γ (State.mem st) → bindings (IrSource.outputs s) Γ i ≡ just bs
  → step p s st i ≡ just after → StepWrites st i after bs
step-writes _ p s st i@(public-input g t id) after Γ _ bs-ok ok
  with eval-guard (State.mem st) g
... | nothing with () ← ok
step-writes _ p s st i@(public-input g t id) after Γ _ bs-ok ok | just false =
  writes-step ((id , default-val t) ∷ [])
    (trans (cong (λ u → (id ⦂ u) ∷ []) (default-type t))
           (final-bindings {xs = guard-ty (IrSource.outputs s) Γ g} bs-ok))
    (cong State.mem (sym (just-injective ok))) (λ _ ())
step-writes _ p s st i@(public-input g t id) after Γ _ bs-ok ok | just true
  with bind-success (decode t (take (encoded-len t) (State.pto-rem st))) _ ok
... | v , decoded , applied =
  writes-step ((id , v) ∷ [])
    (trans (cong (λ u → (id ⦂ u) ∷ []) (decode-typed {t = t} decoded))
           (final-bindings {xs = guard-ty (IrSource.outputs s) Γ g} bs-ok))
    (cong State.mem (sym (just-injective applied))) (λ _ ())
step-writes _ p s st i@(private-input g t id) after Γ _ bs-ok ok
  with eval-guard (State.mem st) g
... | nothing with () ← ok
step-writes _ p s st i@(private-input g t id) after Γ _ bs-ok ok | just false =
  writes-step ((id , default-val t) ∷ [])
    (trans (cong (λ u → (id ⦂ u) ∷ []) (default-type t))
           (final-bindings {xs = guard-ty (IrSource.outputs s) Γ g} bs-ok))
    (cong State.mem (sym (just-injective ok))) (λ _ ())
step-writes _ p s st i@(private-input g t id) after Γ _ bs-ok ok | just true
  with bind-success (decode t (take (encoded-len t) (State.priv-rem st))) _ ok
... | v , decoded , applied =
  writes-step ((id , v) ∷ [])
    (trans (cong (λ u → (id ⦂ u) ∷ []) (decode-typed {t = t} decoded))
           (final-bindings {xs = guard-ty (IrSource.outputs s) Γ g} bs-ok))
    (cong State.mem (sym (just-injective applied))) (λ _ ())
step-writes _ p s st i@(prepare-verification g h ops pr id) after Γ _ bs-ok ok
  with bind-success (prepare-result s st g h ops pr) _ ok
... | acc , _ , applied =
  writes-step ((id , val-accumulator acc) ∷ [])
    (prepare-binding (IrSource.outputs s) Γ g h ops pr id bs-ok)
    (cong State.mem (sym (just-injective applied))) (λ _ ())
step-writes _ p s st i@(accumulate ops id) after Γ _ bs-ok ok
  with bind-success (fold-result (State.mem st) ops) _ ok
... | acc , _ , applied =
  writes-step ((id , val-accumulator acc) ∷ [])
    (fold-binding (IrSource.outputs s) Γ ops id bs-ok)
    (cong State.mem (sym (just-injective applied))) (λ _ ())
step-writes _ p s st i@(verify-accumulator op) after Γ _ bs-ok ok =
  unchanged st i after (resolve-acc (State.mem st) op) _ (λ _ _ → cong State.mem ∘ sym ∘ just-injective)
    ok (final-bindings {xs = expect (IrSource.outputs s) Γ accumulator op} bs-ok) (λ _ ())
step-writes _ p s st i@(circuit-output ops) after Γ _ bs-ok ok =
  unchanged st i after (collectOutputs (State.mem st) (IrSource.outputs s) ops) _
    (λ _ _ → cong State.mem ∘ sym ∘ just-injective)
    ok (output-binding (IrSource.outputs s) Γ ops bs-ok) (λ _ ())
step-writes _ p s st i@(inner-proof g id) after Γ _ bs-ok ok with State.proof-rem st
... | [] with () ← ok
step-writes _ p s st i@(inner-proof g id) after Γ _ bs-ok ok | _ ∷ _ =
  unchanged st i after (resolve𝔹 (State.mem st) g) _ (λ _ _ → cong State.mem ∘ sym ∘ just-injective)
    ok (final-bindings {xs = expect (IrSource.outputs s) Γ native g} bs-ok) (λ _ ())
step-writes _ p s st i@(impact g ops) after Γ _ bs-ok ok with resolve𝔹 (State.mem st) g
... | nothing with () ← ok
step-writes _ p s st i@(impact g ops) after Γ _ bs-ok ok | just false =
  writes-step [] (final-bindings {xs = expect (IrSource.outputs s) Γ native g >>
    expect-all (IrSource.outputs s) Γ native ops} bs-ok) (cong State.mem (sym (just-injective ok))) (λ _ ())
step-writes _ p s st i@(impact g ops) after Γ _ bs-ok ok | just true
  with resolve-all-Fr (State.mem st) ops
... | nothing with () ← ok
step-writes _ p s st i@(impact g ops) after Γ _ bs-ok ok | just true | just vs
  with take (length ops) (drop (State.pti-idx st) (ProofPreimage.pub-transcript-inputs p)) ≟LFr vs
... | no _ with () ← ok
... | yes _ =
  writes-step [] (final-bindings {xs = expect (IrSource.outputs s) Γ native g >>
    expect-all (IrSource.outputs s) Γ native ops} bs-ok) (cong State.mem (sym (just-injective ok))) (λ _ ())
step-writes types p s st i@(encode _ _) after Γ typed bs-ok ok =
  pure-writes types s st i after Γ typed bs-ok ok
step-writes types p s st i@(assert _) after Γ typed bs-ok ok =
  pure-writes types s st i after Γ typed bs-ok ok
step-writes types p s st i@(cond-select _ _ _ _) after Γ typed bs-ok ok =
  pure-writes types s st i after Γ typed bs-ok ok
step-writes types p s st i@(constrain-bits _ _) after Γ typed bs-ok ok =
  pure-writes types s st i after Γ typed bs-ok ok
step-writes types p s st i@(constrain-eq _ _) after Γ typed bs-ok ok =
  pure-writes types s st i after Γ typed bs-ok ok
step-writes types p s st i@(constrain-to-boolean _) after Γ typed bs-ok ok =
  pure-writes types s st i after Γ typed bs-ok ok
step-writes types p s st i@(copy _ _) after Γ typed bs-ok ok =
  pure-writes types s st i after Γ typed bs-ok ok
step-writes types p s st i@(ec-mul _ _ _) after Γ typed bs-ok ok =
  pure-writes types s st i after Γ typed bs-ok ok
step-writes types p s st i@(ec-mul-generator _ _) after Γ typed bs-ok ok =
  pure-writes types s st i after Γ typed bs-ok ok
step-writes types p s st i@(hash-to-curve _ _) after Γ typed bs-ok ok =
  pure-writes types s st i after Γ typed bs-ok ok
step-writes types p s st i@(into-coordinates _ _) after Γ typed bs-ok ok =
  pure-writes types s st i after Γ typed bs-ok ok
step-writes types p s st i@(from-coordinates _ _) after Γ typed bs-ok ok =
  pure-writes types s st i after Γ typed bs-ok ok
step-writes types p s st i@(into-bytes32 _ _) after Γ typed bs-ok ok =
  pure-writes types s st i after Γ typed bs-ok ok
step-writes types p s st i@(from-bytes32 _ _ _) after Γ typed bs-ok ok =
  pure-writes types s st i after Γ typed bs-ok ok
step-writes types p s st i@(reverse-bytes _ _) after Γ typed bs-ok ok =
  pure-writes types s st i after Γ typed bs-ok ok
step-writes types p s st i@(bytes32-into-low-high _ _) after Γ typed bs-ok ok =
  pure-writes types s st i after Γ typed bs-ok ok
step-writes types p s st i@(bytes32-from-low-high _ _) after Γ typed bs-ok ok =
  pure-writes types s st i after Γ typed bs-ok ok
step-writes types p s st i@(div-mod-power-of-two _ _ _) after Γ typed bs-ok ok =
  pure-writes types s st i after Γ typed bs-ok ok
step-writes types p s st i@(reconstitute-field _ _ _ _) after Γ typed bs-ok ok =
  pure-writes types s st i after Γ typed bs-ok ok
step-writes types p s st i@(transient-hash _ _) after Γ typed bs-ok ok =
  pure-writes types s st i after Γ typed bs-ok ok
step-writes types p s st i@(persistent-hash _ _ _) after Γ typed bs-ok ok =
  pure-writes types s st i after Γ typed bs-ok ok
step-writes types p s st i@(keccak256 _ _ _) after Γ typed bs-ok ok =
  pure-writes types s st i after Γ typed bs-ok ok
step-writes types p s st i@(test-eq _ _ _) after Γ typed bs-ok ok =
  pure-writes types s st i after Γ typed bs-ok ok
step-writes types p s st i@(add _ _ _) after Γ typed bs-ok ok =
  pure-writes types s st i after Γ typed bs-ok ok
step-writes types p s st i@(mul _ _ _) after Γ typed bs-ok ok =
  pure-writes types s st i after Γ typed bs-ok ok
step-writes types p s st i@(neg _ _) after Γ typed bs-ok ok =
  pure-writes types s st i after Γ typed bs-ok ok
step-writes types p s st i@(inv _ _) after Γ typed bs-ok ok =
  pure-writes types s st i after Γ typed bs-ok ok
step-writes types p s st i@(not _ _) after Γ typed bs-ok ok =
  pure-writes types s st i after Γ typed bs-ok ok
step-writes types p s st i@(less-than _ _ _ _) after Γ typed bs-ok ok =
  pure-writes types s st i after Γ typed bs-ok ok
step-writes types p s st i@(jubjub-scalar-from-native _ _) after Γ typed bs-ok ok =
  pure-writes types s st i after Γ typed bs-ok ok
step-writes types p s st i@(slice _ _ _ _) after Γ typed bs-ok ok =
  pure-writes types s st i after Γ typed bs-ok ok
step-writes types p s st i@(nth _ _ _) after Γ typed bs-ok ok =
  pure-writes types s st i after Γ typed bs-ok ok
step-writes types p s st i@(concat _ _) after Γ typed bs-ok ok =
  pure-writes types s st i after Γ typed bs-ok ok
step-writes types p s st i@(reverse _ _) after Γ typed bs-ok ok =
  pure-writes types s st i after Γ typed bs-ok ok
step-writes types p s st i@(load-constant _ _ _) after Γ typed bs-ok ok =
  pure-writes types s st i after Γ typed bs-ok ok
step-writes types p s st i@(sha512 _ _ _) after Γ typed bs-ok ok =
  pure-writes types s st i after Γ typed bs-ok ok
step-writes types p s st i@(and _ _) after Γ typed bs-ok ok =
  pure-writes types s st i after Γ typed bs-ok ok
step-writes types p s st i@(or _ _) after Γ typed bs-ok ok =
  pure-writes types s st i after Γ typed bs-ok ok
step-writes types p s st i@(xor _ _) after Γ typed bs-ok ok =
  pure-writes types s st i after Γ typed bs-ok ok
step-writes types p s st i@(to-bytes _ _) after Γ typed bs-ok ok =
  pure-writes types s st i after Γ typed bs-ok ok
step-writes types p s st i@(from-bytes _ _ _) after Γ typed bs-ok ok =
  pure-writes types s st i after Γ typed bs-ok ok
step-writes types p s st i@(bytes-into-natives _ _) after Γ typed bs-ok ok =
  pure-writes types s st i after Γ typed bs-ok ok
step-writes types p s st i@(bytes-from-natives _ _ _) after Γ typed bs-ok ok =
  pure-writes types s st i after Γ typed bs-ok ok
