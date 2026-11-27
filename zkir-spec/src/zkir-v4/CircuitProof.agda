{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.CircuitProof (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Syntax ⋯
open import zkir-v4.Types ⋯ using (IrValue)
open import zkir-v4.Semantics ⋯
open import zkir-v4.Circuit ⋯
open import zkir-v4.CircuitBridge ⋯

open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Product using (_×_; _,_; Σ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

honest-witness : ProofPreimage → State → CircuitWitness
honest-witness p st = mk-witness
  (State.mem st)
  (full-public-inputs st)
  (ProofPreimage.binding-input p)
  (ProofPreimage.comm-commitment p)
  (State.inner-witnesses st)

-- This fragment consists of the instructions that share the same
-- functional primitive and perform no transcript or PI action.
-- The remaining instructions have separate synthesis contracts.
Common : Instruction → Set
Common i = lower i ≡ shared i

apply : State → List (Identifier × IrValue) → State
apply st writes = record st { mem = apply-writes (State.mem st) writes }

core-step : ∀ p src st i → Common i
            → step p src st i ≡ ((compute (State.mem st) i) >>= λ writes → just (apply st writes))

core-step _ _ _ (encode _ _) _ = refl
core-step _ _ _ (assert _) ()
core-step _ _ _ (cond-select _ _ _ _) ()
core-step _ _ _ (constrain-bits _ _) ()
core-step _ _ _ (constrain-eq _ _) ()
core-step _ _ _ (constrain-to-boolean _) _ = refl
core-step _ _ _ (copy _ _) _ = refl
core-step _ _ _ (impact _ _) ()
core-step _ _ _ (ec-mul _ _ _) _ = refl
core-step _ _ _ (ec-mul-generator _ _) _ = refl
core-step _ _ _ (hash-to-curve _ _) _ = refl
core-step _ _ _ (into-coordinates _ _) _ = refl
core-step _ _ _ (from-coordinates _ _) _ = refl
core-step _ _ _ (into-bytes32 _ _) _ = refl
core-step _ _ _ (from-bytes32 _ _ _) _ = refl
core-step _ _ _ (reverse-bytes _ _) _ = refl
core-step _ _ _ (bytes32-into-low-high _ _) _ = refl
core-step _ _ _ (bytes32-from-low-high (_ , _) _) ()
core-step _ _ _ (div-mod-power-of-two _ _ _) ()
core-step _ _ _ (reconstitute-field _ _ _ _) ()
core-step _ _ _ (transient-hash _ _) _ = refl
core-step _ _ _ (persistent-hash _ _ _) ()
core-step _ _ _ (keccak256 _ _ _) ()
core-step _ _ _ (test-eq _ _ _) ()
core-step _ _ _ (add _ _ _) _ = refl
core-step _ _ _ (mul _ _ _) _ = refl
core-step _ _ _ (neg _ _) _ = refl
core-step _ _ _ (inv _ _) _ = refl
core-step _ _ _ (not _ _) _ = refl
core-step _ _ _ (less-than _ _ _ _) ()
core-step _ _ _ (jubjub-scalar-from-native _ _) _ = refl
core-step _ _ _ (slice _ _ _ _) _ = refl
core-step _ _ _ (nth _ _ _) _ = refl
core-step _ _ _ (concat _ _) _ = refl
core-step _ _ _ (reverse _ _) _ = refl
core-step _ _ _ (load-constant _ _ _) _ = refl
core-step _ _ _ (sha512 _ _ _) ()
core-step _ _ _ (and _ _) _ = refl
core-step _ _ _ (or _ _) _ = refl
core-step _ _ _ (xor _ _) _ = refl
core-step _ _ _ (to-bytes _ _) _ = refl
core-step _ _ _ (from-bytes _ _ _) _ = refl
core-step _ _ _ (bytes-into-natives _ _) _ = refl
core-step _ _ _ (bytes-from-natives _ _ _) _ = refl
core-step _ _ _ (public-input _ _ _) ()
core-step _ _ _ (private-input _ _ _) ()
core-step _ _ _ (circuit-output _) ()
core-step _ _ _ (inner-proof _ _) ()
core-step _ _ _ (prepare-verification _ _ _ _ _) ()
core-step _ _ _ (accumulate _ _) ()
core-step _ _ _ (verify-accumulator _) ()

-- Per-step computed values may appear in the supplied final witness.
-- When they do, the Rust alignment check demands their agreement.
data CommonRun (w : CircuitWitness) : State → List Instruction → State → Set where
  end : ∀ {st} → CommonRun w st [] st
  next : ∀ {st i is writes final}
         → Common i
         → compute (State.mem st) i ≡ just writes
         → WriteAgreement (check-shared-writes i) w writes
         → CommonRun w (apply st writes) is final
         → CommonRun w st (i ∷ is) final

common-preprocess-run : ∀ {p src w start is final}
                        → CommonRun w start is final → run p src start is ≡ just final
common-preprocess-run end = refl
common-preprocess-run {p} {src} {start = start} (next {i = i} common computed _ rest)
  rewrite core-step p src start i common | computed = common-preprocess-run rest

common-circuit-run : ∀ {src w st is final} retained
                     → CommonRun w st is final
                     → runᶜ src w (view st retained) (map lower is) ≡ just (view final retained)
common-circuit-run retained end = refl
common-circuit-run {src} {w} {st} retained (next {i = i} {writes = writes} common computed agrees rest)
  rewrite common
        | shared-forward src w (view st retained) i writes computed agrees =
  common-circuit-run retained rest

data CommonProgram : List Instruction → Set where
  end : CommonProgram []
  next : ∀ {i is} → Common i → CommonProgram is → CommonProgram (i ∷ is)

private
  just-injective : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
  just-injective refl = refl

  bind-success : ∀ {A B : Set} (a : Maybe A) (f : A → Maybe B) {b}
               → (a >>= f) ≡ just b
               → Σ A λ x → (a ≡ just x) × (f x ≡ just b)
  bind-success nothing _ ()
  bind-success (just x) _ ok = x , refl , ok

-- Reverse simulation for the shared fragment.  It needs no computed
-- write agreement: successful synthesis already checked the writes.
common-circuit-backward : ∀ p src w st is retained final
                          → CommonProgram is
                          → runᶜ src w (view st retained) (map lower is) ≡ just final
                          → Σ State λ next-st → (run p src st is ≡ just next-st)
                                            × (final ≡ view next-st retained)
common-circuit-backward p src w st [] retained final end ok =
  st , refl , sym (just-injective ok)
common-circuit-backward p src w st (i ∷ is) retained final (next common rest) ok
  rewrite common | core-step p src st i common
  with bind-success (stepᶜ src w (view st retained) (shared i))
         (λ after → runᶜ src w after (map lower is)) ok
... | _ , step-ok , run-ok with shared-backward src w (view st retained) i step-ok
...   | writes , computed , refl rewrite computed =
  common-circuit-backward p src w (apply st writes) is retained final rest run-ok
