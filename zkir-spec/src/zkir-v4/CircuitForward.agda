{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.CircuitForward (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Syntax ⋯
open import zkir-v4.Semantics ⋯
open import zkir-v4.SemanticsProperties ⋯ using (AcceptedRun; preprocess-inversion; preprocess-full-inputs)
open import zkir-v4.Circuit ⋯
open import zkir-v4.CircuitBridge ⋯
open import zkir-v4.CircuitProof ⋯ using (honest-witness; apply; core-step)
open import zkir-v4.CircuitEffects ⋯
open import zkir-v4.CircuitPure ⋯
open import zkir-v4.CircuitInputs ⋯ using (InitialInputsAgree; init-forward)
open import zkir-v4.CommitmentInputs ⋯ using (honest-terminal-inputs)
open import zkir-v4.EncodingProperties ⋯ using (EncodingLaws)
open import zkir-v4.Validation ⋯ using (validate)

open import Data.Bool using (true; false)
open import Data.List using ([]; _++_; map)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Product using (_×_; _,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
import Relation.Nullary

open import zkir-v4.RunShape ⋯ public

private
  successful-bound : ∀ m i {writes} → preprocess-bounded m i ≡ just writes
                   → bounded-compute m i ≡ just writes
  successful-bound m i ok with preprocess-bit-bounds i
  ... | true = ok
  ... | false with () ← ok

agrees-step-using : ∀ {p src w st retained i after rest}
             → PreparationForward
             → ReadyStep p src w st retained i after rest
             → Agreement p src w st retained i after rest
agrees-step-using {p} {src} {w} {st} {retained} {i} _ (common {writes = writes} lowering computed agreed) =
  off , on
  where
  off : step p src st i ≡ just (apply st writes)
  off = trans (core-step p src st i lowering) (cong (λ result → result >>= λ ws → just (apply st ws)) computed)
  on : stepᶜ src w (view st retained) (lower i) ≡ just (view (apply st writes) retained)
  on rewrite lowering = shared-forward src w (view st retained) i writes computed agreed
agrees-step-using {p} {src} {w} {st} {retained} {i = i@(constrain-bits _ bits)}
  _ (bit-constraint {writes = writes} within computed agreed) =
  off , bounded-forward src w (view st retained) i writes bits within
        (successful-bound (State.mem st) i computed) agreed
  where
  off : step p src st i ≡ just (apply st writes)
  off rewrite computed = refl
agrees-step-using {p} {src} {w} {st} {retained} {i = i@(div-mod-power-of-two _ bits _)}
  _ (division {writes = writes} within computed agreed) =
  off , bounded-forward src w (view st retained) i writes bits within
        (successful-bound (State.mem st) i computed) agreed
  where
  off : step p src st i ≡ just (apply st writes)
  off rewrite computed = refl
agrees-step-using {p} {src} {w} {st} {retained} {i = i@(reconstitute-field _ _ bits _)}
  _ (reconstitution {writes = writes} within computed agreed) =
  off , bounded-forward src w (view st retained) i writes bits within
        (successful-bound (State.mem st) i computed) agreed
  where
  off : step p src st i ≡ just (apply st writes)
  off rewrite computed = refl
agrees-step-using {p} {src} {w} {st} {retained} {i} _ (special {writes = writes} support computed agreed) =
  off , special-forward src w (view st retained) i writes support computed agreed
  where
  off : step p src st i ≡ just (apply st writes)
  off = trans (special-off p src st i support) (cong (λ result → result >>= λ ws → just (apply st ws)) computed)
agrees-step-using {p} {src} {w} {st} {retained} _
  (public-read {g = g} {t} {id} {active} {v} bit read assigned typed) =
  public-read-agrees p src w st retained g t id active v bit read assigned typed
agrees-step-using {p} {src} {w} {st} {retained} _
  (private-read {g = g} {t} {id} {active} {v} bit read assigned typed) =
  private-read-agrees p src w st retained g t id active v bit read assigned typed
agrees-step-using {p} {src} {w} {st} {retained} _
  (impact-step {g = g} {ops} {active} {values} bit resolved received) =
  impact-agrees p src w st retained g ops active values bit resolved received
agrees-step-using {p} {src} {w} {st} _
  (proof-slot {retained} {g} {id} {raw} {rest} {active} slots bit) =
  proof-slot-agrees p src w st g id retained raw rest active slots bit
agrees-step-using {p} {src} {w} {st} {retained} laws
  (prepare-step {g = g} {hash} {ops} {proof} {out} {active} {values} {blob} {key} {acc}
    bit vals slot key-found parsed prepared agreed) =
  prepare-agrees-using laws p src w st retained g hash ops proof out active values blob key acc
    bit vals slot key-found parsed prepared agreed
agrees-step-using {p} {src} {w} {st} {retained} _
  (fold-step {ops = ops} {out} {a} {b} {rest} {acc} vals collapsed agreed) =
  fold-agrees p src w st retained ops out a b rest acc vals collapsed agreed
agrees-step-using {p} {src} {w} {st} {retained} _ (expose-step {op = op} {acc} resolved) =
  expose-agrees p src w st retained op acc resolved
agrees-step-using {p} {src} {w} {st} {retained} _ (output-step {ops = ops} {values} collected) =
  output-agrees p src w st retained ops values collected

agrees-run-using : ∀ {p src w st retained is final rest}
            → PreparationForward
            → ReadyRun p src w st retained is final rest
            → (run p src st is ≡ just final)
              × (runᶜ src w (view st retained) (map lower is) ≡ just (view final rest))
agrees-run-using laws empty = refl , refl
agrees-run-using laws (instr ready rest) with agrees-step-using laws ready | agrees-run-using laws rest
... | off , on | off-rest , on-rest rewrite off | on = off-rest , on-rest

agrees-step : ∀ {p src w st retained i after rest}
             → PreparationLaws
             → ReadyStep p src w st retained i after rest
             → Agreement p src w st retained i after rest
agrees-step laws = agrees-step-using (preparation-forward laws)

agrees-run : ∀ {p src w st retained is final rest}
            → PreparationLaws
            → ReadyRun p src w st retained is final rest
            → (run p src st is ≡ just final)
              × (runᶜ src w (view st retained) (map lower is) ≡ just (view final rest))
agrees-run laws = agrees-run-using (preparation-forward laws)

private
  finish-honest : ∀ src p final
                → check-commit src p final ≡ just final
                → (IrSource.do-communications-commitment src ≡ true →
                    encode-inputs (State.mem final) (IrSource.inputs src) ≡ ProofPreimage.inputs p)
                → finish-commitment src (honest-witness p final) (view final []) ≡ just (view final [])
  finish-honest src p final checked raw with IrSource.do-communications-commitment src in flag
  ... | false = refl
  ... | true with ProofPreimage.comm-commitment p
  ...   | nothing with () ← checked
  finish-honest src p final checked raw | true | just (commitment , randomness)
    rewrite raw refl with commitment ≟ᶠ transient-commit
      (ProofPreimage.inputs p ++ encode-outputs (view final [])) randomness
  ... | Relation.Nullary.yes _ = refl
  ... | Relation.Nullary.no _ with () ← checked

private
  conclude : ∀ src w start target
           → validate src ≡ true
           → initᶜ src w ≡ just start
           → runᶜ src w start (map lower (IrSource.instructions src)) ≡ just target
           → finishᶜ src w target ≡ just target
           → satisfies src w target
  conclude src w start target valid initialized ran terminal
    rewrite valid | initialized | ran = terminal

-- The public statement is the trailing block of the same instance
-- vector. The terminal commitment check needs the re-encoding of the
-- declared inputs to match the original stream.
forward-using : ∀ src p final
          → PreparationForward
          → (accepted : preprocess src p ≡ just final)
          → InitialInputsAgree src p (honest-witness p final)
          → initᶜ src (honest-witness p final)
              ≡ just (view (AcceptedRun.initial (preprocess-inversion {src} {p} accepted))
                            (State.inner-witnesses final))
          → ReadyRun p src (honest-witness p final)
              (AcceptedRun.initial (preprocess-inversion {src} {p} accepted))
              (State.inner-witnesses final) (IrSource.instructions src) final []
          → satisfies src (honest-witness p final) (view final [])
forward-using src p final laws accepted inputs-agree initialized ready
  = conclude src (honest-witness p final) (view (AcceptedRun.initial run-info) (State.inner-witnesses final))
      (view final []) (AcceptedRun.source-valid run-info)
      initialized (proj₂ (agrees-run-using laws ready))
      (trans
        (guard-pass
          (full-public-inputsᶜ (view final []) ≟LFr full-public-inputs final)
          (sym (preprocess-full-inputs {src} {p} accepted))
          (finish-commitment src (honest-witness p final) (view final [])))
        (finish-honest src p final (AcceptedRun.commitment-checked run-info) (λ _ → raw)))
  where
  run-info = preprocess-inversion {src} {p} accepted
  raw = honest-terminal-inputs src p (AcceptedRun.initial run-info) final
          (State.inner-witnesses final) [] inputs-agree (AcceptedRun.initialized run-info) ready

forward : ∀ src p final
          → EncodingLaws
          → PreparationLaws
          → (accepted : preprocess src p ≡ just final)
          → InitialInputsAgree src p (honest-witness p final)
          → ReadyRun p src (honest-witness p final)
              (AcceptedRun.initial (preprocess-inversion {src} {p} accepted))
              (State.inner-witnesses final) (IrSource.instructions src) final []
          → satisfies src (honest-witness p final) (view final [])
forward src p final encoding laws accepted inputs-agree ready =
  forward-using src p final (preparation-forward laws) accepted inputs-agree
    (init-forward encoding src p (honest-witness p final) inputs-agree refl refl
      (AcceptedRun.initialized (preprocess-inversion {src} {p} accepted)))
    ready
