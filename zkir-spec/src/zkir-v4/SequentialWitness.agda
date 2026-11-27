{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.SequentialWitness (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Circuit ⋯
open import zkir-v4.CircuitBridge ⋯ using
  (guard-pass; shared-forward; prepare-forward; fold-forward)
open import zkir-v4.CircuitProperties ⋯ using (Trace; next; end; trace→run)
open import zkir-v4.Operations ⋯ using (Mem; ∅; ins; _≟LFr_; insert-proof)
open import zkir-v4.Protocol ⋯ using (instance-fields)
open import zkir-v4.SequentialAccumulator ⋯ using
  (carried-fields; carry-writes; encoded-state; encode-computes)
open import zkir-v4.SequentialSource ⋯
open import zkir-v4.Syntax ⋯
open import zkir-v4.Types ⋯
open import zkir-v4.Validation ⋯ using (validate)

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃; _×_; _,_)
open import Data.Sum using (inj₁)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

private
  witness : Mem → List Accumulator → List Fr → List (List Byte) → CircuitWitness
  witness inputs accs statement raw = mk-witness inputs (instance-fields accs statement) 0ᶠ nothing raw

  no-commitment : ∀ keys n → IrSource.do-communications-commitment (source keys n) ≡ false
  no-commitment keys zero = refl
  no-commitment keys (suc zero) = refl
  no-commitment keys (suc (suc n)) = refl

  assemble : ∀ keys n w first final →
    validate (source keys n) ≡ true →
    initᶜ (source keys n) w ≡ just first →
    runᶜ (source keys n) w first (map lower (IrSource.instructions (source keys n))) ≡ just final →
    full-public-inputsᶜ final ≡ CircuitWitness.full-pis w →
    satisfies (source keys n) w final
  assemble keys n w first final valid initialized ran public-ok
    rewrite valid | initialized | ran | no-commitment keys n =
    guard-pass (full-public-inputsᶜ final ≟LFr CircuitWitness.full-pis w) public-ok (just final)

  add-step : ∀ src w m c s p → CircuitWitness.assign w finish ≡ nothing →
    stepᶜ src w (initial-state w (install-native m c s p)) (lower advance) ≡ just (after-add w m c s p)
  add-step src w m c s p absent = shared-forward src w _ advance
    ((finish , val-native (p +ᶠ 1ᶠ)) ∷ []) refl (inj₁ absent , tt)

  bound-proof : CircuitState → List Byte → CircuitState
  bound-proof st raw = record st
    { proofs = insert-proof "%proof" raw (CircuitState.proofs st) ; proof-rem = [] }

  expose : CircuitState → Accumulator → CircuitState
  expose st a = record st { accs = a ∷ [] }

  base-witness : ∀ keys c →
    validate (source keys zero) ≡ true →
    ∃ λ w → ∃ λ final → satisfies (source keys zero) w final × CircuitWitness.full-pis w ≡ fields zero c c c
  base-witness keys c valid = w , final , assemble keys zero w first final valid refl ran refl , refl
    where
    inputs = ins ctx (val-native c) ∅
    w = witness inputs [] (fields zero c c c) []
    first = initial-state w inputs
    final = record first { pis = fields zero c c c }
    ran : runᶜ (source keys zero) w first (map lower (IrSource.instructions (source keys zero))) ≡ just final
    ran rewrite active = refl

  first-witness : ∀ keys c s p raw a →
    validate (source keys 1) ≡ true →
    key-well-formed (keys zero) ≡ true →
    prepare-circuit (keys zero) (fields zero c s p) raw true ≡ just a →
    ∃ λ w → ∃ λ final → satisfies (source keys 1) w final ×
      CircuitWitness.full-pis w ≡ instance-fields (a ∷ []) (fields 1 c s (p +ᶠ 1ᶠ))
  first-witness keys c s p raw a valid parsed prepared =
    w , final , assemble keys 1 w first final valid refl (trace→run path) refl , refl
    where
    src = source keys 1
    inputs = install-native ∅ c s p
    w = witness inputs (a ∷ []) (fields 1 c s (p +ᶠ 1ᶠ)) (raw ∷ [])
    first = initial-state w inputs
    published = after-publish zero w ∅ c s p
    bound = bound-proof published raw
    opened = install bound opening (val-accumulator a)
    final = expose opened a

    path : Trace src w first (map lower (IrSource.instructions src)) final
    path = next (add-step src w ∅ c s p refl)
      (next (publish-step src zero w ∅ c s p)
        (next refl
          (next (prepare-forward src w bound (imm 1ᶠ) (key-digest (keys zero))
            (child-operands zero) "%proof" opening true (fields zero c s p) raw (keys zero) a
            active refl refl (pinned-key (keys zero)) parsed prepared (inj₁ refl))
          (next refl end))))

  later-witness : ∀ keys n c s p raw a b f →
    validate (source keys (suc (suc n))) ≡ true →
    key-well-formed (keys (suc n)) ≡ true →
    prepare-circuit (keys (suc n)) (instance-fields (b ∷ []) (fields (suc n) c s p)) raw true ≡ just a →
    fold-accumulators (a ∷ b ∷ []) ≡ just f →
    ∃ λ w → ∃ λ final → satisfies (source keys (suc (suc n))) w final ×
      CircuitWitness.full-pis w ≡ instance-fields (f ∷ []) (fields (suc (suc n)) c s (p +ᶠ 1ᶠ))
  later-witness keys n c s p raw a b f valid parsed prepared folded-ok =
    w , final , assemble keys (suc (suc n)) w first final valid refl (trace→run path) refl , refl
    where
    src = source keys (suc (suc n))
    carried-input = ins carried (val-accumulator b) ∅
    inputs = install-native carried-input c s p
    w = witness inputs (f ∷ []) (fields (suc (suc n)) c s (p +ᶠ 1ᶠ)) (raw ∷ [])
    first = initial-state w inputs
    published = after-publish (suc n) w carried-input c s p
    encoded = encoded-state published b
    bound = bound-proof encoded raw
    opened = install bound opening (val-accumulator a)
    combined = install opened folded (val-accumulator f)
    final = expose combined f

    ops = map var carried-fields ++ child-operands (suc n)
    predecessor = instance-fields (b ∷ []) (fields (suc n) c s p)

    encoded-step : stepᶜ src w published (lower (encode (var carried) carried-fields)) ≡ just encoded
    encoded-step =
      shared-forward src w published (encode (var carried) carried-fields) (carry-writes b)
        (encode-computes published b refl)
        (inj₁ refl , inj₁ refl , inj₁ refl , inj₁ refl , inj₁ refl , inj₁ refl ,
         inj₁ refl , inj₁ refl , inj₁ refl , inj₁ refl , inj₁ refl , inj₁ refl , tt)

    prepare-step : stepᶜ src w bound (lower (prepare (keys (suc n)) ops)) ≡ just opened
    prepare-step = prepare-forward src w bound (imm 1ᶠ) (key-digest (keys (suc n)))
      ops "%proof" opening true predecessor raw (keys (suc n)) a
      active
      (resolve-predecessor n w c s p b)
      refl (pinned-key (keys (suc n))) parsed prepared (inj₁ refl)

    path : Trace src w first (map lower (IrSource.instructions src)) final
    path = next (add-step src w carried-input c s p refl)
      (next (publish-step src (suc n) w carried-input c s p)
        (next encoded-step
          (next refl
            (next prepare-step
              (next (fold-forward src w opened (var opening ∷ var carried ∷ []) folded a b [] f
                refl folded-ok (inj₁ refl))
              (next refl end))))))

-- The only supplied assignments are the declared inputs. A successor's
-- proof slot is filled by the raw predecessor proof used by its observation.
build : ∀ keys n {statement carried} →
  validate (source keys n) ≡ true →
  (∀ {m} → n ≡ suc m → key-well-formed (keys m) ≡ true) →
  Observation keys 0ᶠ n statement carried →
  ∃ λ w → ∃ λ final → satisfies (source keys n) w final ×
    CircuitWitness.full-pis w ≡ instance-fields carried statement
build keys zero valid parsed (initial c) = base-witness keys c valid
build keys (suc zero) valid parsed (advanced c s p raw a _ prepared single) =
  first-witness keys c s p raw a valid (parsed refl) prepared
build keys (suc zero) valid parsed (advanced c s p raw a () prepared (batch _))
build keys (suc (suc n)) valid parsed (advanced c s p raw a () prepared single)
build keys (suc (suc n)) valid parsed (advanced c s p raw a _ prepared (batch {b = b} {f = f} folded-ok)) =
  later-witness keys n c s p raw a b f valid (parsed refl) prepared folded-ok
