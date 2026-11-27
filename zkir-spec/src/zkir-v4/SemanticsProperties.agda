{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.SemanticsProperties (⋯ : _) (open Assumptions ⋯) where

open import zkir-v4.Types ⋯
open import zkir-v4.Syntax ⋯
open import zkir-v4.Encoding ⋯ using (decode; encode-accumulator) renaming (encode to encode-value)
open import zkir-v4.Semantics ⋯
open import zkir-v4.Protocol ⋯ using (exposure; exposures; instance-fields)
open import zkir-v4.Validation ⋯ using (validate)
open import zkir-v4.ProofSlots using (keep)

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_; length; map; take; drop; concatMap)
open import Data.List.Properties using (++-identityʳ; ++-assoc; length-++; concatMap-++)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ; _+_; _≟_)
open import Data.Nat.Properties using (+-identityʳ; +-assoc)
open import Data.Product using (_×_; _,_; ∃)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import Relation.Nullary using (Dec; yes; no)

private
  bind-success : ∀ {A B : Set} (a : Maybe A) (f : A → Maybe B) {b}
                 → (a >>= f) ≡ just b
                 → ∃ λ x → (a ≡ just x) × (f x ≡ just b)
  bind-success nothing _ ()
  bind-success (just x) _ eq = x , refl , eq

  guard-success : ∀ {P A : Set} (d : Dec P) (a : Maybe A) {x}
                  → guardD d a ≡ just x → P × (a ≡ just x)
  guard-success (yes p) _ eq = p , eq
  guard-success (no _) _ ()

-- A trace records the actual intermediate states of an accepted run.
data Trace (P : ProofPreimage) (S : IrSource) : State → List Instruction → State → Set where
  done : ∀ {st} → Trace P S st [] st
  next : ∀ {i is st mid final}
         → step P S st i ≡ just mid
         → Trace P S mid is final
         → Trace P S st (i ∷ is) final

run-trace : ∀ {P S st is final}
            → run P S st is ≡ just final → Trace P S st is final
run-trace {is = []} refl = done
run-trace {P} {S} {st} {i ∷ is} ok
  with bind-success (step P S st i) (λ mid → run P S mid is) ok
... | _ , step-ok , rest-ok = next step-ok (run-trace rest-ok)

trace-run : ∀ {P S st is final}
            → Trace P S st is final → run P S st is ≡ just final
trace-run done = refl
trace-run (next step-ok rest) rewrite step-ok = trace-run rest

step-deterministic : ∀ {P S st i a b}
                     → step P S st i ≡ just a → step P S st i ≡ just b → a ≡ b
step-deterministic a b = just-injective (trans (sym a) b)

run-deterministic : ∀ {P S st is a b}
                    → run P S st is ≡ just a → run P S st is ≡ just b → a ≡ b
run-deterministic a b = just-injective (trans (sym a) b)

record Exhausted (P : ProofPreimage) (st : State) : Set where
  field
    public-inputs-used : State.pti-idx st ≡ length (ProofPreimage.pub-transcript-inputs P)
    public-outputs-used : State.pto-rem st ≡ []
    private-used : State.priv-rem st ≡ []
    proof-slots-used : State.proof-rem st ≡ []

private
  commit-same : ∀ S P st final → check-commit S P st ≡ just final → st ≡ final
  commit-same S P st final eq with IrSource.do-communications-commitment S
  ... | false = just-injective eq
  ... | true with ProofPreimage.comm-commitment P
  ...   | nothing with () ← eq
  commit-same S P st final eq | true | just (c , r)
    with guard-success (c ≟ᶠ transient-commit
           (ProofPreimage.inputs P ++ concatMap encode-value (State.outs st)) r) _ eq
  ... | _ , result = just-injective result

finish-inversion : ∀ S P st final
                   → finish S P st ≡ just final
                   → Exhausted P st × (st ≡ final) × (check-commit S P st ≡ just final)
finish-inversion S P st final eq
  with State.pto-rem st in public-ok
     | State.priv-rem st in private-ok
     | State.proof-rem st in proof-ok
... | [] | [] | []
  with guard-success (State.pti-idx st ≟ length (ProofPreimage.pub-transcript-inputs P))
         (check-commit S P st) eq
...   | used , comm-ok =
  record { public-inputs-used = used
         ; public-outputs-used = public-ok
         ; private-used = private-ok
         ; proof-slots-used = proof-ok } ,
  commit-same S P st final comm-ok , comm-ok
finish-inversion S P st final () | _ ∷ _ | _ | _
finish-inversion S P st final () | [] | _ ∷ _ | _
finish-inversion S P st final () | [] | [] | _ ∷ _

record AcceptedRun (S : IrSource) (P : ProofPreimage) (final : State) : Set where
  field
    source-valid : validate S ≡ true
    initial : State
    initialized : init S P ≡ just initial
    trace : Trace P S initial (IrSource.instructions S) final
    streams-exhausted : Exhausted P final
    commitment-checked : check-commit S P final ≡ just final

preprocess-inversion : ∀ {S P final} → preprocess S P ≡ just final → AcceptedRun S P final
preprocess-inversion {S} {P} {final} ok with validate S in validation
... | false with () ← ok
preprocess-inversion {S} {P} {final} ok | true
  with bind-success (init S P)
         (λ st → run P S st (IrSource.instructions S) >>= finish S P) ok
...   | st , initialized , rest
  with bind-success (run P S st (IrSource.instructions S)) (finish S P) rest
...     | last , ran , finished with finish-inversion S P last final finished
...       | exhausted , refl , comm-ok =
  record { source-valid = validation
         ; initial = st
         ; initialized = initialized
         ; trace = run-trace ran
         ; streams-exhausted = exhausted
         ; commitment-checked = comm-ok }

interprets-deterministically : ∀ {S P a b}
                               → preprocess S P ≡ just a → preprocess S P ≡ just b → a ≡ b
interprets-deterministically a b = just-injective (trans (sym a) b)

infix 4 _≼_
_≼_ : List Fr → List Fr → Set
xs ≼ ys = ∃ λ delta → ys ≡ xs ++ delta

prefix-refl : ∀ {xs} → xs ≼ xs
prefix-refl {xs} = [] , sym (++-identityʳ xs)

prefix-append : ∀ xs ys → xs ≼ (xs ++ ys)
prefix-append xs ys = ys , refl

prefix-trans : ∀ {xs ys zs} → xs ≼ ys → ys ≼ zs → xs ≼ zs
prefix-trans {xs} (a , refl) (b , refl) = (a ++ b) , ++-assoc xs a b

record PublicProgress (st st′ : State) (count : ℕ) : Set where
  field
    statement-prefix : State.pis st ≼ State.pis st′
    accumulator-prefix : State.acc-pis st ≼ State.acc-pis st′
    accumulator-block : State.acc-pis st ≡ concatMap encode-accumulator (State.exposed st)
                        → State.acc-pis st′ ≡ concatMap encode-accumulator (State.exposed st′)
    exposure-count : length (State.exposed st′) ≡ length (State.exposed st) + count

private
  appended : ∀ st st′ vals added
             → State.pis st′ ≡ State.pis st ++ vals
             → State.acc-pis st′ ≡ State.acc-pis st ++ concatMap encode-accumulator added
             → State.exposed st′ ≡ State.exposed st ++ added
             → PublicProgress st st′ (length added)
  appended st st′ vals added pis-eq block-eq exposed-eq =
    record { statement-prefix = vals , pis-eq
           ; accumulator-prefix = concatMap encode-accumulator added , block-eq
           ; accumulator-block = λ previous →
               trans block-eq
                 (trans (cong (_++ concatMap encode-accumulator added) previous)
                   (trans (sym (concatMap-++ encode-accumulator (State.exposed st) added))
                     (cong (concatMap encode-accumulator) (sym exposed-eq))))
           ; exposure-count =
               trans (cong length exposed-eq) (length-++ (State.exposed st)) }

  impact-progress : ∀ st st′ vals
                    → State.pis st′ ≡ State.pis st ++ vals
                    → State.acc-pis st′ ≡ State.acc-pis st
                    → State.exposed st′ ≡ State.exposed st
                    → PublicProgress st st′ 0
  impact-progress st st′ vals pis-eq acc-eq exposed-eq =
    appended st st′ vals [] pis-eq
      (trans acc-eq (sym (++-identityʳ (State.acc-pis st))))
      (trans exposed-eq (sym (++-identityʳ (State.exposed st))))

  unchanged : ∀ {st st′}
              → State.pis st′ ≡ State.pis st
              → State.acc-pis st′ ≡ State.acc-pis st
              → State.exposed st′ ≡ State.exposed st
              → PublicProgress st st′ 0
  unchanged {st} {st′} pis-eq =
    impact-progress st st′ [] (trans pis-eq (sym (++-identityʳ (State.pis st))))

  same-after-bind : ∀ {A : Set} {st st′} (m : Maybe A) (f : A → State)
                    → (∀ x → State.pis (f x) ≡ State.pis st)
                    → (∀ x → State.acc-pis (f x) ≡ State.acc-pis st)
                    → (∀ x → State.exposed (f x) ≡ State.exposed st)
                    → (m >>= λ x → just (f x)) ≡ just st′
                    → PublicProgress st st′ 0
  same-after-bind m f same-pis same-acc same-exposed ok
    with bind-success m (λ x → just (f x)) ok
  ... | x , _ , ok′ rewrite sym (just-injective ok′) =
    unchanged (same-pis x) (same-acc x) (same-exposed x)

  stable-write : ∀ {st st′} (m : Maybe (List (Identifier × IrValue)))
                  → (m >>= λ ws → just (record st { mem = apply-writes (State.mem st) ws }))
                    ≡ just st′
                  → PublicProgress st st′ 0
  stable-write m = same-after-bind m _ (λ _ → refl) (λ _ → refl) (λ _ → refl)

  exposure-progress : ∀ st st′ a
      → State.pis st′ ≡ State.pis st
      → State.acc-pis st′ ≡ State.acc-pis st ++ encode-accumulator a
      → State.exposed st′ ≡ State.exposed st ++ (a ∷ [])
      → PublicProgress st st′ 1
  exposure-progress st st′ a pis-eq block-eq =
    appended st st′ [] (a ∷ [])
      (trans pis-eq (sym (++-identityʳ (State.pis st))))
      (trans block-eq (cong (State.acc-pis st ++_) (sym (++-identityʳ (encode-accumulator a)))))

step-public-progress : ∀ {P S st i st′}
                       → step P S st i ≡ just st′
                       → PublicProgress st st′ (exposure i)
step-public-progress {P} {S} {st} {impact guard inputs} ok
  with resolve𝔹 (State.mem st) guard
... | nothing with () ← ok
step-public-progress {P} {S} {st} {impact guard inputs} ok | just false
  with refl ← just-injective ok =
    impact-progress st _ (map (λ _ → 0ᶠ) inputs) refl refl refl
step-public-progress {P} {S} {st} {impact guard inputs} ok | just true
  with resolve-all-Fr (State.mem st) inputs
... | nothing with () ← ok
step-public-progress {P} {S} {st} {impact guard inputs} ok | just true | just vals
  with take (length inputs) (drop (State.pti-idx st) (ProofPreimage.pub-transcript-inputs P))
         ≟LFr vals
... | no _ with () ← ok
step-public-progress {P} {S} {st} {impact guard inputs} ok | just true | just vals | yes _
  with refl ← just-injective ok = impact-progress st _ vals refl refl refl
step-public-progress {P} {S} {st} {public-input guard t id} ok
  with eval-guard (State.mem st) guard
... | nothing with () ← ok
step-public-progress {P} {S} {st} {public-input guard t id} ok | just false
  with refl ← just-injective ok = unchanged refl refl refl
step-public-progress {P} {S} {st} {public-input guard t id} ok | just true =
  same-after-bind (decode t (take (encoded-len t) (State.pto-rem st))) _
    (λ _ → refl) (λ _ → refl) (λ _ → refl) ok
step-public-progress {P} {S} {st} {private-input guard t id} ok
  with eval-guard (State.mem st) guard
... | nothing with () ← ok
step-public-progress {P} {S} {st} {private-input guard t id} ok | just false
  with refl ← just-injective ok = unchanged refl refl refl
step-public-progress {P} {S} {st} {private-input guard t id} ok | just true =
  same-after-bind (decode t (take (encoded-len t) (State.priv-rem st))) _
    (λ _ → refl) (λ _ → refl) (λ _ → refl) ok
step-public-progress {P} {S} {st} {inner-proof guard id} ok with State.proof-rem st
... | [] with () ← ok
step-public-progress {P} {S} {st} {inner-proof guard id} ok | _ ∷ _ =
  same-after-bind (resolve𝔹 (State.mem st) guard) _
    (λ _ → refl) (λ _ → refl) (λ _ → refl) ok
step-public-progress {P} {S} {st} {prepare-verification g h ops proof id} ok =
  same-after-bind (prepare-result S st g h ops proof) _
    (λ _ → refl) (λ _ → refl) (λ _ → refl) ok
step-public-progress {P} {S} {st} {accumulate ops id} ok =
  same-after-bind (fold-result (State.mem st) ops) _
    (λ _ → refl) (λ _ → refl) (λ _ → refl) ok
step-public-progress {P} {S} {st} {verify-accumulator input} ok
  with bind-success (resolve-acc (State.mem st) input) _ ok
... | a , _ , exposed-ok with refl ← just-injective exposed-ok = exposure-progress st _ a refl refl refl
step-public-progress {P} {S} {st} {circuit-output ops} ok =
  same-after-bind (collectOutputs (State.mem st) (IrSource.outputs S) ops) _
    (λ _ → refl) (λ _ → refl) (λ _ → refl) ok
step-public-progress {st = st} {i = i@(encode _ _)} ok = stable-write (compute (State.mem st) i) ok
step-public-progress {st = st} {i = i@(assert _)} ok = stable-write (compute (State.mem st) i) ok
step-public-progress {st = st} {i = i@(cond-select _ _ _ _)} ok = stable-write (compute (State.mem st) i) ok
step-public-progress {st = st} {i = i@(constrain-bits _ _)} ok = stable-write (compute (State.mem st) i) ok
step-public-progress {st = st} {i = i@(constrain-eq _ _)} ok = stable-write (compute (State.mem st) i) ok
step-public-progress {st = st} {i = i@(constrain-to-boolean _)} ok = stable-write (compute (State.mem st) i) ok
step-public-progress {st = st} {i = i@(copy _ _)} ok = stable-write (compute (State.mem st) i) ok
step-public-progress {st = st} {i = i@(ec-mul _ _ _)} ok = stable-write (compute (State.mem st) i) ok
step-public-progress {st = st} {i = i@(ec-mul-generator _ _)} ok = stable-write (compute (State.mem st) i) ok
step-public-progress {st = st} {i = i@(hash-to-curve _ _)} ok = stable-write (compute (State.mem st) i) ok
step-public-progress {st = st} {i = i@(into-coordinates _ _)} ok = stable-write (compute (State.mem st) i) ok
step-public-progress {st = st} {i = i@(from-coordinates _ _)} ok = stable-write (compute (State.mem st) i) ok
step-public-progress {st = st} {i = i@(into-bytes32 _ _)} ok = stable-write (compute (State.mem st) i) ok
step-public-progress {st = st} {i = i@(from-bytes32 _ _ _)} ok = stable-write (compute (State.mem st) i) ok
step-public-progress {st = st} {i = i@(reverse-bytes _ _)} ok = stable-write (compute (State.mem st) i) ok
step-public-progress {st = st} {i = i@(bytes32-into-low-high _ _)} ok = stable-write (compute (State.mem st) i) ok
step-public-progress {st = st} {i = i@(bytes32-from-low-high _ _)} ok = stable-write (compute (State.mem st) i) ok
step-public-progress {st = st} {i = i@(div-mod-power-of-two _ _ _)} ok = stable-write (compute (State.mem st) i) ok
step-public-progress {st = st} {i = i@(reconstitute-field _ _ _ _)} ok = stable-write (compute (State.mem st) i) ok
step-public-progress {st = st} {i = i@(transient-hash _ _)} ok = stable-write (compute (State.mem st) i) ok
step-public-progress {st = st} {i = i@(persistent-hash _ _ _)} ok = stable-write (compute (State.mem st) i) ok
step-public-progress {st = st} {i = i@(keccak256 _ _ _)} ok = stable-write (compute (State.mem st) i) ok
step-public-progress {st = st} {i = i@(test-eq _ _ _)} ok = stable-write (compute (State.mem st) i) ok
step-public-progress {st = st} {i = i@(add _ _ _)} ok = stable-write (compute (State.mem st) i) ok
step-public-progress {st = st} {i = i@(mul _ _ _)} ok = stable-write (compute (State.mem st) i) ok
step-public-progress {st = st} {i = i@(neg _ _)} ok = stable-write (compute (State.mem st) i) ok
step-public-progress {st = st} {i = i@(inv _ _)} ok = stable-write (compute (State.mem st) i) ok
step-public-progress {st = st} {i = i@(not _ _)} ok = stable-write (compute (State.mem st) i) ok
step-public-progress {st = st} {i = i@(less-than _ _ _ _)} ok = stable-write (compute (State.mem st) i) ok
step-public-progress {st = st} {i = i@(jubjub-scalar-from-native _ _)} ok = stable-write (compute (State.mem st) i) ok
step-public-progress {st = st} {i = i@(slice _ _ _ _)} ok = stable-write (compute (State.mem st) i) ok
step-public-progress {st = st} {i = i@(nth _ _ _)} ok = stable-write (compute (State.mem st) i) ok
step-public-progress {st = st} {i = i@(concat _ _)} ok = stable-write (compute (State.mem st) i) ok
step-public-progress {st = st} {i = i@(reverse _ _)} ok = stable-write (compute (State.mem st) i) ok
step-public-progress {st = st} {i = i@(load-constant _ _ _)} ok = stable-write (compute (State.mem st) i) ok
step-public-progress {st = st} {i = i@(sha512 _ _ _)} ok = stable-write (compute (State.mem st) i) ok
step-public-progress {st = st} {i = i@(and _ _)} ok = stable-write (compute (State.mem st) i) ok
step-public-progress {st = st} {i = i@(or _ _)} ok = stable-write (compute (State.mem st) i) ok
step-public-progress {st = st} {i = i@(xor _ _)} ok = stable-write (compute (State.mem st) i) ok
step-public-progress {st = st} {i = i@(to-bytes _ _)} ok = stable-write (compute (State.mem st) i) ok
step-public-progress {st = st} {i = i@(from-bytes _ _ _)} ok = stable-write (compute (State.mem st) i) ok
step-public-progress {st = st} {i = i@(bytes-into-natives _ _)} ok = stable-write (compute (State.mem st) i) ok
step-public-progress {st = st} {i = i@(bytes-from-natives _ _ _)} ok = stable-write (compute (State.mem st) i) ok

step-pis-prefix : ∀ {P S st i st′}
                  → step P S st i ≡ just st′ → State.pis st ≼ State.pis st′
step-pis-prefix {P} {S} {st} {i} ok =
  PublicProgress.statement-prefix (step-public-progress {P} {S} {st} {i} ok)

step-acc-pis-prefix : ∀ {P S st i st′}
                      → step P S st i ≡ just st′ → State.acc-pis st ≼ State.acc-pis st′
step-acc-pis-prefix {P} {S} {st} {i} ok =
  PublicProgress.accumulator-prefix (step-public-progress {P} {S} {st} {i} ok)

trace-public-progress : ∀ {P S st is final}
                         → Trace P S st is final
                         → PublicProgress st final (exposures is)
trace-public-progress {st = st} done = unchanged {st} {st} refl refl refl
trace-public-progress {P} {S} {st} (next {i} {is} {mid = mid} step-ok rest) =
  let first = step-public-progress {P} {S} {st} {i} step-ok
      tail = trace-public-progress rest in
  record { statement-prefix = prefix-trans
             (PublicProgress.statement-prefix first) (PublicProgress.statement-prefix tail)
         ; accumulator-prefix = prefix-trans
             (PublicProgress.accumulator-prefix first) (PublicProgress.accumulator-prefix tail)
         ; accumulator-block = λ initial →
             PublicProgress.accumulator-block tail (PublicProgress.accumulator-block first initial)
         ; exposure-count =
             trans (PublicProgress.exposure-count tail)
               (trans (cong (_+ exposures is) (PublicProgress.exposure-count first))
                 (+-assoc (length (State.exposed st)) (exposure i) (exposures is))) }

run-prefixes : ∀ {P S st is final}
             → run P S st is ≡ just final
             → (State.pis st ≼ State.pis final) × (State.acc-pis st ≼ State.acc-pis final)
run-prefixes {P} {S} {st} {is} ran =
  let progress = trace-public-progress (run-trace {P} {S} {st} {is} ran) in
  PublicProgress.statement-prefix progress , PublicProgress.accumulator-prefix progress

preprocess-exhausts : ∀ {S P final}
                      → preprocess S P ≡ just final → Exhausted P final
preprocess-exhausts {S} {P} ok = AcceptedRun.streams-exhausted (preprocess-inversion {S} {P} ok)

private
  init-carried-empty : ∀ S P st → init S P ≡ just st
                     → (State.acc-pis st ≡ []) × (State.exposed st ≡ [])
  init-carried-empty S P st ok with decode-inputs (IrSource.inputs S) (ProofPreimage.inputs P)
  ... | nothing with () ← ok
  init-carried-empty S P st ok | just _ with IrSource.do-communications-commitment S
  ... | false with refl ← just-injective ok = refl , refl
  init-carried-empty S P st ok | just _ | true with ProofPreimage.comm-commitment P
  ... | nothing with () ← ok
  init-carried-empty S P st ok | just _ | true | just (_ , _)
    with refl ← just-injective ok = refl , refl

-- These equalities connect the accepted VM run to the protocol's key-bound
-- exposure count and to the instance vector reconstructed by the verifier.
preprocess-exposure : ∀ {S P final}
                      → preprocess S P ≡ just final
                      → (State.acc-pis final ≡ concatMap encode-accumulator (State.exposed final))
                        × (length (State.exposed final) ≡ exposures (IrSource.instructions S))
preprocess-exposure {S} {P} ok with preprocess-inversion {S} {P} ok
... | accepted with init-carried-empty S P (AcceptedRun.initial accepted)
                      (AcceptedRun.initialized accepted)
...   | empty-fields , empty-exposed =
  let progress = trace-public-progress (AcceptedRun.trace accepted) in
  PublicProgress.accumulator-block progress
    (trans empty-fields (cong (concatMap encode-accumulator) (sym empty-exposed))) ,
  trans (PublicProgress.exposure-count progress)
    (cong (λ as → length as + exposures (IrSource.instructions S)) empty-exposed)

preprocess-full-inputs : ∀ {S P final}
                        → preprocess S P ≡ just final
                        → full-public-inputs final ≡ instance-fields (State.exposed final) (State.pis final)
preprocess-full-inputs {S} {P} {final} ok with preprocess-exposure {S} {P} ok
... | fields , _ = cong (_++ State.pis final) fields
