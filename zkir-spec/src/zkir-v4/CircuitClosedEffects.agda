{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.CircuitClosedEffects (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Types ⋯
open import zkir-v4.Syntax ⋯
open import zkir-v4.Semantics ⋯ hiding (write)
open import zkir-v4.Circuit ⋯
open import zkir-v4.CircuitBridge ⋯ using (view; write-backward)
open import zkir-v4.CircuitEffects ⋯ using (PreparationLaws; PreparationBackward; preparation-backward; collect-agrees; exposure-result)
open import zkir-v4.Validation ⋯ using (resolve-vk)

open import Data.Bool using (true; false; if_then_else_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (just; nothing; _>>=_)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; ∃)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

-- These effects use the current memory and fixed key table.  They consume
-- no stream entries and need no extra data from circuit extraction.
data ClosedEffect : Instruction → Set where
  prepare-effect : ∀ {g h ops proof out}
                  → ClosedEffect (prepare-verification g h ops proof out)
  fold-effect : ∀ {ops out} → ClosedEffect (accumulate ops out)
  expose-effect : ∀ {op} → ClosedEffect (verify-accumulator op)
  output-effect : ∀ {ops} → ClosedEffect (circuit-output ops)

record ClosedEffectFrame (before after : State) : Set where
  field
    pti-idx-same : State.pti-idx after ≡ State.pti-idx before
    pto-rem-same : State.pto-rem after ≡ State.pto-rem before
    priv-rem-same : State.priv-rem after ≡ State.priv-rem before
    proof-rem-same : State.proof-rem after ≡ State.proof-rem before

private
  preserve-streams : ∀ {st st′}
                   → State.pti-idx st′ ≡ State.pti-idx st
                   → State.pto-rem st′ ≡ State.pto-rem st
                   → State.priv-rem st′ ≡ State.priv-rem st
                   → State.proof-rem st′ ≡ State.proof-rem st
                   → ClosedEffectFrame st st′
  preserve-streams pi pub priv proofs = record
    { pti-idx-same = pi ; pto-rem-same = pub ; priv-rem-same = priv ; proof-rem-same = proofs }

  prepared-off : ∀ (laws : PreparationBackward) active vals blob key acc
                 → key-well-formed key ≡ true
                 → prepare-circuit key vals blob active ≡ just acc
                 → (if active then prepare-active key vals blob else just trivial-accumulator)
                   ≡ just acc
  prepared-off laws active vals blob key acc =
    laws key vals blob active acc

closed-effect-backward-using : ∀ (laws : PreparationBackward) p src w st retained i final
                         → ClosedEffect i
                         → stepᶜ src w (view st retained) (lower i) ≡ just final
                         → ∃ λ after → (step p src st i ≡ just after)
                                     × (final ≡ view after retained)
                                     × ClosedEffectFrame st after
closed-effect-backward-using laws p src w st retained (prepare-verification g h ops proof out) final
  prepare-effect accepted with resolve𝔹 (State.mem st) g
... | nothing = case accepted of λ ()
... | just active with resolve-all-Fr (State.mem st) ops
...   | nothing = case accepted of λ ()
...   | just vals with State.proofs st proof
...     | nothing = case accepted of λ ()
...     | just blob with resolve-vk h (IrSource.inner-vks src)
...       | nothing = case accepted of λ ()
...       | just key with key-well-formed key in parses
...         | false = case accepted of λ ()
...         | true with prepare-circuit key vals blob active in prepared
...           | nothing = case accepted of λ ()
...           | just acc =
  out1 st out (val-accumulator acc) ,
  cong (_>>= λ a → just (out1 st out (val-accumulator a)))
    (prepared-off laws active vals blob key acc parses prepared) ,
  write-backward true w (view st retained) ((out , val-accumulator acc) ∷ []) accepted ,
  preserve-streams refl refl refl refl
closed-effect-backward-using laws p src w st retained (accumulate ops out) final fold-effect accepted
  with resolve-accs (State.mem st) ops
... | nothing = case accepted of λ ()
... | just [] = case accepted of λ ()
... | just (_ ∷ []) = case accepted of λ ()
... | just (a ∷ b ∷ rest) with fold-accumulators (a ∷ b ∷ rest)
...   | nothing = case accepted of λ ()
...   | just acc =
  out1 st out (val-accumulator acc) ,
  refl ,
  write-backward true w (view st retained) ((out , val-accumulator acc) ∷ []) accepted ,
  preserve-streams refl refl refl refl
closed-effect-backward-using laws p src w st retained (verify-accumulator op) final expose-effect accepted
  with resolve-acc (State.mem st) op
... | nothing = case accepted of λ ()
... | just acc = exposure-result st acc , refl , sym (just-injective accepted) ,
                 preserve-streams refl refl refl refl
closed-effect-backward-using laws p src w st retained (circuit-output ops) final output-effect accepted
  with collect-outputs (State.mem st) (IrSource.outputs src) ops in collected
... | nothing = case accepted of λ ()
... | just vals =
  record st { outs = State.outs st ++ vals } ,
  cong (_>>= λ vs → just (record st { outs = State.outs st ++ vs }))
    (trans (collect-agrees (State.mem st) (IrSource.outputs src) ops) collected) ,
  sym (just-injective accepted) ,
  preserve-streams refl refl refl refl

closed-effect-backward : ∀ (laws : PreparationLaws) p src w st retained i final
                         → ClosedEffect i
                         → stepᶜ src w (view st retained) (lower i) ≡ just final
                         → ∃ λ after → (step p src st i ≡ just after)
                                     × (final ≡ view after retained)
                                     × ClosedEffectFrame st after
closed-effect-backward laws = closed-effect-backward-using (preparation-backward laws)
