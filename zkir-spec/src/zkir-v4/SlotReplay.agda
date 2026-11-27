{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.SlotReplay (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Semantics ⋯
open import zkir-v4.SemanticsProperties ⋯ using (Trace; done; next; AcceptedRun; Exhausted; preprocess-inversion)
open import zkir-v4.Syntax ⋯
open import zkir-v4.Types ⋯ using (encoded-len)
open import zkir-v4.Encoding ⋯ using (decode)
open import zkir-v4.ProofSlots using (keep)
open import zkir-v4.Validation ⋯ using (validate)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; length; take; drop)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Maybe using (Maybe; nothing; just; _>>=_)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (_≟_)
open import Data.Product using (_×_; _,_; ∃; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; trans; subst)
open import Relation.Nullary using (yes; no)

Slots = List (List Byte)

set-slots : State → Slots → State
set-slots st xs = record st { proof-rem = xs }

with-slots : ProofPreimage → Slots → ProofPreimage
with-slots p xs = record p { inner-proofs = xs }

private
  -- Canonical input for one instruction, read from its actual pre-step state.
  slot : State → Instruction → Slots
  slot st (inner-proof g id) with State.proof-rem st | resolve𝔹 (State.mem st) g
  ... | b ∷ _ | just active = keep active b ∷ []
  ... | _ | _ = []
  slot _ _ = []

  -- The replay changes only the unconsumed proof stream.  The normalized
  -- proof bytes passed to subsequent preparations stay identical.
  pure-step : ∀ st i final tail
            → (compute (State.mem st) i >>= λ ws → just (record st { mem = apply-writes (State.mem st) ws })) ≡ just final
            → (compute (State.mem st) i >>= λ ws → just (record (set-slots st tail) { mem = apply-writes (State.mem st) ws }))
                ≡ just (set-slots final tail)
              × State.inner-witnesses final ≡ State.inner-witnesses st ++ []
  pure-step st i final tail eq with compute (State.mem st) i
  ... | nothing with () ← eq
  ... | just ws with refl ← just-injective eq = refl , sym (++-identityʳ _)

  step-replay : ∀ p s st i final tail → step p s st i ≡ just final
              → step p s (set-slots st (slot st i ++ tail)) i ≡ just (set-slots final tail)
                × State.inner-witnesses final ≡ State.inner-witnesses st ++ slot st i

  step-replay p s st (impact g ops) final tail ok with resolve𝔹 (State.mem st) g
  ... | nothing with () ← ok
  ... | just false with refl ← just-injective ok = refl , sym (++-identityʳ _)
  ... | just true with resolve-all-Fr (State.mem st) ops
  ...   | nothing with () ← ok
  ...   | just vals with take (length ops) (drop (State.pti-idx st) (ProofPreimage.pub-transcript-inputs p)) ≟LFr vals
  ...     | no _ with () ← ok
  ...     | yes _ with refl ← just-injective ok = refl , sym (++-identityʳ _)
  step-replay p s st (public-input g t o) final tail ok with eval-guard (State.mem st) g
  ... | nothing with () ← ok
  ... | just false with refl ← just-injective ok = refl , sym (++-identityʳ _)
  ... | just true with decode t (take (encoded-len t) (State.pto-rem st))
  ...   | nothing with () ← ok
  ...   | just v with refl ← just-injective ok = refl , sym (++-identityʳ _)
  step-replay p s st (private-input g t o) final tail ok with eval-guard (State.mem st) g
  ... | nothing with () ← ok
  ... | just false with refl ← just-injective ok = refl , sym (++-identityʳ _)
  ... | just true with decode t (take (encoded-len t) (State.priv-rem st))
  ...   | nothing with () ← ok
  ...   | just v with refl ← just-injective ok = refl , sym (++-identityʳ _)

  step-replay p s st (inner-proof g o) final tail ok with State.proof-rem st
  ... | [] with () ← ok
  ... | raw ∷ rest with resolve𝔹 (State.mem st) g in guard-ok
  ...   | nothing with () ← ok
  ...   | just true with refl ← just-injective ok rewrite guard-ok = refl , refl
  ...   | just false with refl ← just-injective ok rewrite guard-ok = refl , refl
  step-replay p s st (prepare-verification g h ops proof o) final tail ok with prepare-result s st g h ops proof
  ... | nothing with () ← ok
  step-replay p s st (prepare-verification g h ops proof o) final tail ok | just v with refl ← just-injective ok = refl , sym (++-identityʳ _)
  step-replay p s st (accumulate ops o) final tail ok with fold-result (State.mem st) ops
  ... | nothing with () ← ok
  step-replay p s st (accumulate ops o) final tail ok | just v with refl ← just-injective ok = refl , sym (++-identityʳ _)
  step-replay p s st (verify-accumulator op) final tail ok with resolve-acc (State.mem st) op
  ... | nothing with () ← ok
  step-replay p s st (verify-accumulator op) final tail ok | just v with refl ← just-injective ok = refl , sym (++-identityʳ _)
  step-replay p s st (circuit-output ops) final tail ok with collectOutputs (State.mem st) (IrSource.outputs s) ops
  ... | nothing with () ← ok
  step-replay p s st (circuit-output ops) final tail ok | just v with refl ← just-injective ok = refl , sym (++-identityʳ _)
  step-replay p s st i@(encode _ _) final tail = pure-step st i final tail
  step-replay p s st i@(assert _) final tail = pure-step st i final tail
  step-replay p s st i@(cond-select _ _ _ _) final tail = pure-step st i final tail
  step-replay p s st i@(constrain-bits _ _) final tail = pure-step st i final tail
  step-replay p s st i@(constrain-eq _ _) final tail = pure-step st i final tail
  step-replay p s st i@(constrain-to-boolean _) final tail = pure-step st i final tail
  step-replay p s st i@(copy _ _) final tail = pure-step st i final tail
  step-replay p s st i@(ec-mul _ _ _) final tail = pure-step st i final tail
  step-replay p s st i@(ec-mul-generator _ _) final tail = pure-step st i final tail
  step-replay p s st i@(hash-to-curve _ _) final tail = pure-step st i final tail
  step-replay p s st i@(into-coordinates _ _) final tail = pure-step st i final tail
  step-replay p s st i@(from-coordinates _ _) final tail = pure-step st i final tail
  step-replay p s st i@(into-bytes32 _ _) final tail = pure-step st i final tail
  step-replay p s st i@(from-bytes32 _ _ _) final tail = pure-step st i final tail
  step-replay p s st i@(reverse-bytes _ _) final tail = pure-step st i final tail
  step-replay p s st i@(bytes32-into-low-high _ _) final tail = pure-step st i final tail
  step-replay p s st i@(bytes32-from-low-high _ _) final tail = pure-step st i final tail
  step-replay p s st i@(div-mod-power-of-two _ _ _) final tail = pure-step st i final tail
  step-replay p s st i@(reconstitute-field _ _ _ _) final tail = pure-step st i final tail
  step-replay p s st i@(transient-hash _ _) final tail = pure-step st i final tail
  step-replay p s st i@(persistent-hash _ _ _) final tail = pure-step st i final tail
  step-replay p s st i@(keccak256 _ _ _) final tail = pure-step st i final tail
  step-replay p s st i@(test-eq _ _ _) final tail = pure-step st i final tail
  step-replay p s st i@(add _ _ _) final tail = pure-step st i final tail
  step-replay p s st i@(mul _ _ _) final tail = pure-step st i final tail
  step-replay p s st i@(neg _ _) final tail = pure-step st i final tail
  step-replay p s st i@(inv _ _) final tail = pure-step st i final tail
  step-replay p s st i@(not _ _) final tail = pure-step st i final tail
  step-replay p s st i@(less-than _ _ _ _) final tail = pure-step st i final tail
  step-replay p s st i@(jubjub-scalar-from-native _ _) final tail = pure-step st i final tail
  step-replay p s st i@(slice _ _ _ _) final tail = pure-step st i final tail
  step-replay p s st i@(nth _ _ _) final tail = pure-step st i final tail
  step-replay p s st i@(concat _ _) final tail = pure-step st i final tail
  step-replay p s st i@(reverse _ _) final tail = pure-step st i final tail
  step-replay p s st i@(load-constant _ _ _) final tail = pure-step st i final tail
  step-replay p s st i@(sha512 _ _ _) final tail = pure-step st i final tail
  step-replay p s st i@(and _ _) final tail = pure-step st i final tail
  step-replay p s st i@(or _ _) final tail = pure-step st i final tail
  step-replay p s st i@(xor _ _) final tail = pure-step st i final tail
  step-replay p s st i@(to-bytes _ _) final tail = pure-step st i final tail
  step-replay p s st i@(from-bytes _ _ _) final tail = pure-step st i final tail
  step-replay p s st i@(bytes-into-natives _ _) final tail = pure-step st i final tail
  step-replay p s st i@(bytes-from-natives _ _ _) final tail = pure-step st i final tail

  recover : ∀ {p s st is final} → Trace p s st is final → Slots
  recover done = []
  recover (next {i} {st = st} _ rest) = slot st i ++ recover rest

  witnesses : ∀ {p s st is final} (tr : Trace p s st is final)
            → State.inner-witnesses final ≡ State.inner-witnesses st ++ recover tr
  witnesses {st = st} done = sym (++-identityʳ (State.inner-witnesses st))
  witnesses {p} {s} (next {i} {st = st} {mid} ok rest) =
    trans (witnesses rest)
      (trans (cong (_++ recover rest) (proj₂ (step-replay p s st i mid [] ok)))
             (++-assoc (State.inner-witnesses st) (slot st i) (recover rest)))

  replay : ∀ {p s st is final} (tr : Trace p s st is final) xs tail
         → run (with-slots p xs) s (set-slots st (recover tr ++ tail)) is
             ≡ just (set-slots final tail)
  replay done _ _ = refl
  replay {p} {s} (next {i} {st = st} {mid} ok rest) xs tail
    rewrite ++-assoc (slot st i) (recover rest) tail
          | proj₁ (step-replay p s st i mid (recover rest ++ tail) ok) = replay rest xs tail

  init-replay : ∀ s p st xs → init s p ≡ just st
              → init s (with-slots p xs) ≡ just (set-slots st xs) × State.inner-witnesses st ≡ []
  init-replay s p st xs ok with decode-inputs (IrSource.inputs s) (ProofPreimage.inputs p)
  ... | nothing with () ← ok
  ... | just m with IrSource.do-communications-commitment s
  ...   | false with refl ← just-injective ok = refl , refl
  ...   | true with ProofPreimage.comm-commitment p
  ...     | nothing with () ← ok
  ...     | just (_ , _) with refl ← just-injective ok = refl , refl

  finish-replay : ∀ s p final xs → Exhausted p final → check-commit s p final ≡ just final
                → finish s (with-slots p xs) final ≡ just final
  finish-replay s p final xs ex ok
    rewrite Exhausted.public-outputs-used ex | Exhausted.private-used ex | Exhausted.proof-slots-used ex
    with State.pti-idx final ≟ length (ProofPreimage.pub-transcript-inputs p)
  ... | no ne with () ← ne (Exhausted.public-inputs-used ex)
  ... | yes _ with IrSource.do-communications-commitment s
  ...   | false = ok
  ...   | true = ok

-- Replacing every inactive input proof with the empty byte string reproduces
-- the complete final state, including the statement, skips and carried points.
preprocess-normalized : ∀ s p final → preprocess s p ≡ just final
                      → preprocess s (with-slots p (State.inner-witnesses final)) ≡ just final

preprocess-normalized s p final ok = normalized (preprocess-inversion {s} {p} ok)
  where
  normalized : AcceptedRun s p final
             → preprocess s (with-slots p (State.inner-witnesses final)) ≡ just final
  normalized a = build (AcceptedRun.source-valid a) ini ran
    where
    xs = State.inner-witnesses final
    st = AcceptedRun.initial a
    tr = AcceptedRun.trace a
    ex = AcceptedRun.streams-exhausted a
    initialized = init-replay s p st xs (AcceptedRun.initialized a)
    ini = proj₁ initialized
    recovered : xs ≡ recover tr ++ []
    recovered = trans (witnesses tr) (trans (cong (_++ recover tr) (proj₂ initialized)) (sym (++-identityʳ (recover tr))))
    ran : run (with-slots p xs) s (set-slots st xs) (IrSource.instructions s) ≡ just final
    ran = trans (cong (λ slots → run (with-slots p xs) s (set-slots st slots) (IrSource.instructions s)) recovered)
            (trans (replay tr xs [])
              (cong (λ slots → just (set-slots final slots)) (sym (Exhausted.proof-slots-used ex))))

    build : validate s ≡ true → init s (with-slots p xs) ≡ just (set-slots st xs)
          → run (with-slots p xs) s (set-slots st xs) (IrSource.instructions s) ≡ just final
          → preprocess s (with-slots p xs) ≡ just final
    build valid init-ok run-ok rewrite valid | init-ok | run-ok =
      finish-replay s p final xs ex (AcceptedRun.commitment-checked a)

-- The proof stream reconstructed from an accepted trace is the list
-- supplied to synthesis by the honest preprocessor.
step-slots = slot
trace-slots = recover

accepted-slots : ∀ s p final (ok : preprocess s p ≡ just final)
               → State.inner-witnesses final ≡ trace-slots (AcceptedRun.trace (preprocess-inversion {s} {p} ok))
accepted-slots s p final ok with preprocess-inversion {s} {p} ok
... | a = trans (witnesses (AcceptedRun.trace a))
              (cong (_++ trace-slots (AcceptedRun.trace a))
                (proj₂ (init-replay s p (AcceptedRun.initial a) [] (AcceptedRun.initialized a))))

initial-history : ∀ s p st → init s p ≡ just st → State.inner-witnesses st ≡ []
initial-history s p st ok = proj₂ (init-replay s p st [] ok)
