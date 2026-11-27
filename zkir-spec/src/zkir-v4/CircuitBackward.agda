{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.CircuitBackward (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Types ⋯ using (IrValue)
open import zkir-v4.Syntax ⋯
open import zkir-v4.Semantics ⋯ hiding (write; writes)
open import zkir-v4.Circuit ⋯
open import zkir-v4.CircuitBridge ⋯ using (view; shared-backward; bounded-backward)
open import zkir-v4.CircuitProof ⋯ using (Common; apply; core-step)
open import zkir-v4.CircuitPure ⋯ using (Special; special-off; special-backward)

open import Data.Bool using (true)
open import Data.List using (List)
open import Data.Maybe using (just; nothing; _>>=_)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; ∃)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

-- Admissibility is independent of circuit satisfaction.  The common and
-- bounded arms identify the applicable contract.  The other pure arms
-- require the operand-side conditions recorded by Special.
data PureAdmissible (m : Mem) : Instruction → Set where
  common-op : ∀ {i} → Common i → PureAdmissible m i
  bit-constraint-op : ∀ {val bits}
                    → preprocess-bit-bounds (constrain-bits val bits) ≡ true
                    → PureAdmissible m (constrain-bits val bits)
  division-op : ∀ {val bits ids}
              → preprocess-bit-bounds (div-mod-power-of-two val bits ids) ≡ true
              → PureAdmissible m (div-mod-power-of-two val bits ids)
  reconstitution-op : ∀ {divisor modulus bits id}
                    → preprocess-bit-bounds (reconstitute-field divisor modulus bits id) ≡ true
                    → PureAdmissible m (reconstitute-field divisor modulus bits id)
  special-op : ∀ {i} → Special m i → PureAdmissible m i

pure-compute : ∀ p src st i → PureAdmissible (State.mem st) i
                → step p src st i ≡
                  (compute (State.mem st) i >>= λ ws → just (apply st ws))
pure-compute p src st i (common-op lowering) = core-step p src st i lowering
pure-compute _ _ _ _ (bit-constraint-op _) = refl
pure-compute _ _ _ _ (division-op _) = refl
pure-compute _ _ _ _ (reconstitution-op _) = refl
pure-compute p src st i (special-op operands) = special-off p src st i operands

record PureFrame (before after : State) : Set where
  field
    pti-idx-same : State.pti-idx after ≡ State.pti-idx before
    pto-rem-same : State.pto-rem after ≡ State.pto-rem before
    priv-rem-same : State.priv-rem after ≡ State.priv-rem before
    proof-rem-same : State.proof-rem after ≡ State.proof-rem before
    pis-same : State.pis after ≡ State.pis before
    acc-pis-same : State.acc-pis after ≡ State.acc-pis before
    exposed-same : State.exposed after ≡ State.exposed before
    pi-skips-same : State.pi-skips after ≡ State.pi-skips before
    proofs-same : State.proofs after ≡ State.proofs before
    inner-witnesses-same : State.inner-witnesses after ≡ State.inner-witnesses before
    outs-same : State.outs after ≡ State.outs before

pure-frame : ∀ p src st i after
             → PureAdmissible (State.mem st) i
             → step p src st i ≡ just after
             → PureFrame st after
pure-frame p src st i after admissible ok
  rewrite pure-compute p src st i admissible with compute (State.mem st) i
... | nothing with () ← ok
pure-frame p src st i after admissible ok | just _
  with refl ← just-injective ok =
  record { pti-idx-same = refl
         ; pto-rem-same = refl
         ; priv-rem-same = refl
         ; proof-rem-same = refl
         ; pis-same = refl
         ; acc-pis-same = refl
         ; exposed-same = refl
         ; pi-skips-same = refl
         ; proofs-same = refl
         ; inner-witnesses-same = refl
         ; outs-same = refl }

private
  preprocess-result : ∀ m i {ws} → preprocess-bit-bounds i ≡ true
                    → bounded-compute m i ≡ just ws → preprocess-bounded m i ≡ just ws
  preprocess-result m i within computed rewrite within = computed

  from-writes : ∀ p src st retained i final
                → step p src st i ≡
                    (compute (State.mem st) i >>= λ ws → just (apply st ws))
                → (∃ λ (ws : List (Identifier × IrValue)) →
                     (compute (State.mem st) i ≡ just ws) ×
                     (final ≡ record (view st retained) { mem = apply-writes (State.mem st) ws }))
                → ∃ λ after → (step p src st i ≡ just after) × final ≡ view after retained
  from-writes p src st retained i final off (ws , calculated , circuit-state)
    rewrite off | calculated = apply st ws , refl , circuit-state

-- A satisfying circuit step on an admissible pure instruction identifies
-- the same state as preprocessing.  Successful witness-cell checks are
-- extracted from the circuit step itself.
pure-preprocess-step : ∀ p src w st retained i final
                      → PureAdmissible (State.mem st) i
                      → stepᶜ src w (view st retained) (lower i) ≡ just final
                      → ∃ λ after → (step p src st i ≡ just after) × final ≡ view after retained
pure-preprocess-step p src w st retained i final (common-op lowering) accepted =
  from-writes p src st retained i final (core-step p src st i lowering)
    (shared-backward src w (view st retained) i
      (trans (cong (stepᶜ src w (view st retained)) (sym lowering)) accepted))
pure-preprocess-step p src w st retained i@(constrain-bits _ bits) final
  (bit-constraint-op within) accepted
  with bounded-backward src w (view st retained) i bits accepted
... | _ , ws , computed , circuit-state =
  from-writes p src st retained i final refl
    (ws , preprocess-result (State.mem st) i within computed , circuit-state)
pure-preprocess-step p src w st retained i@(div-mod-power-of-two _ bits _) final
  (division-op within) accepted
  with bounded-backward src w (view st retained) i bits accepted
... | _ , ws , computed , circuit-state =
  from-writes p src st retained i final refl
    (ws , preprocess-result (State.mem st) i within computed , circuit-state)
pure-preprocess-step p src w st retained i@(reconstitute-field _ _ bits _) final
  (reconstitution-op within) accepted
  with bounded-backward src w (view st retained) i bits accepted
... | _ , ws , computed , circuit-state =
  from-writes p src st retained i final refl
    (ws , preprocess-result (State.mem st) i within computed , circuit-state)
pure-preprocess-step p src w st retained i final (special-op operands) accepted =
  from-writes p src st retained i final (special-off p src st i operands)
    (special-backward src w (view st retained) i operands accepted)
