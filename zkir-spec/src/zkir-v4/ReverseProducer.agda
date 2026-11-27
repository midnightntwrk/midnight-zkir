{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.ReverseProducer (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Syntax ⋯
open import zkir-v4.Circuit ⋯
open import zkir-v4.CircuitBridge ⋯ using (view)
open import zkir-v4.CircuitEffects ⋯ using (PreparationBackward)
open import zkir-v4.CircuitExtraction ⋯ using (extract)
open import zkir-v4.CircuitInputs ⋯ using (ValidDeclarations)
open import zkir-v4.CircuitProperties ⋯ using (SatisfiedRun; satisfying-run)
open import zkir-v4.CircuitReplay ⋯ using (PrefixReplay; replay-prefix; extraction-complete-using)
open import zkir-v4.CommitmentInputs ⋯ using (encode-inputs-frame)
open import zkir-v4.EncodingProperties ⋯ using (EncodingLaws)
open import zkir-v4.Producer ⋯
open import zkir-v4.ProducerMemory ⋯ using (ComputeTypes; trace-store; trace-extends; initial-input-frame)
open import zkir-v4.ProducerStore ⋯ using
  (infer-success; fold-cons; fresh-success; initial-store; InitialStore; WriteFrame)
open import zkir-v4.ReverseShape ⋯
open import zkir-v4.Semantics ⋯ using (ProofPreimage; State; preprocess)
open import zkir-v4.SemanticsProperties ⋯ using (run-trace)
open import zkir-v4.StatementSoundness ⋯ using (WitnessShape)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using () renaming ([] to []∀; _∷_ to _∷∀_)
open import Data.Maybe using (just)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; sym; trans)

private
  declarations-checked : ∀ Γ ds {after}
                       → fold-check fresh Γ ds ≡ just after → ValidDeclarations ds
  declarations-checked Γ [] _ = []∀
  declarations-checked Γ ((id ⦂ t) ∷ ds) ok with fold-cons fresh Γ (id ⦂ t) ds ok
  ... | next , added , tail with fresh-success Γ id t added
  ...   | _ , _ , valid = valid ∷∀ declarations-checked next ds tail

producer-declarations : ∀ src → Producer src → ValidDeclarations (IrSource.inputs src)
producer-declarations src producer with infer-success src producer
... | _ , _ , checked , _ = declarations-checked [] (IrSource.inputs src) checked

private
  replay-stable : ComputeTypes → ∀ src w start target {p}
                → Producer src → PrefixReplay src w start target p → StableInputs src start target
  replay-stable types src w start target {p} producer replayed _ with infer-success src producer
  ... | Γ , _ , declared , checked =
    trans (cong encode-declared (sym final-view))
      (trans (encode-inputs-frame (IrSource.inputs src) (State.mem off-start) (State.mem off-final) frame)
             (cong encode-declared start-view))
    where
    open PrefixReplay replayed
    encode-declared = λ st → encode-inputs (CircuitState.mem st) (IrSource.inputs src)
    initial = initial-store src p {st = off-start} off-initialized declared
    trace = trace-store types (run-trace {P = p} {S = src} {st = off-start}
      {is = IrSource.instructions src} {final = off-final} off-ran)
      Γ (WriteFrame.typed-after (InitialStore.frame initial)) checked
    frame = initial-input-frame src p off-start off-final Γ initial (trace-extends trace)

-- Producer single assignment preserves the declared input cells during
-- replay, so the commitment compares the same inputs in both executions.
producer-shape : EncodingLaws → PreparationBackward → ComputeTypes
               → ∀ src w target → Producer src → (checked : SatisfiedRun src w target)
               → Along w (IrSource.instructions src) (SatisfiedRun.path checked)
               → WitnessShape src w target
producer-shape encoding prepare types src w target producer checked local
  with reconstruct-trace src w (SatisfiedRun.start checked) _ target (SatisfiedRun.path checked) local
... | streams , trace = record
  { start = SatisfiedRun.start checked
  ; streams = streams
  ; initialized = SatisfiedRun.initialized checked
  ; path = trace
  ; input-stability = replay-stable types src w _ target producer
      (replay-prefix encoding prepare src w _ target streams (producer-declarations src producer)
        (SatisfiedRun.initialized checked) trace)
  }

producer-reverse : EncodingLaws → PreparationBackward → ComputeTypes
                 → ∀ src w target → Producer src → (accepted : satisfies src w target)
                 → let checked = satisfying-run src w target accepted in
                   Along w (IrSource.instructions src) (SatisfiedRun.path checked)
                   → Σ ProofPreimage λ p → Σ State λ final →
                       (extract src w ≡ just p) × (preprocess src p ≡ just final)
                       × (view final (CircuitState.proof-rem target) ≡ target)
producer-reverse encoding prepare types src w target producer accepted local =
  extraction-complete-using encoding prepare src w _ target _ (SatisfiedRun.validated checked)
    (producer-declarations src producer) (WitnessShape.initialized shape) accepted
    (WitnessShape.path shape) (WitnessShape.input-stability shape)
  where
  checked = satisfying-run src w target accepted
  shape = producer-shape encoding prepare types src w target producer checked local
