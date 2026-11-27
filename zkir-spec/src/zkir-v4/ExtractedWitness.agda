{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.ExtractedWitness (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Circuit ⋯
open import zkir-v4.CircuitBridge ⋯ using (view)
open import zkir-v4.CircuitEffects ⋯ using (PreparationLaws)
open import zkir-v4.CircuitExtraction ⋯ using (extract)
open import zkir-v4.CircuitForward ⋯ using (forward)
open import zkir-v4.CircuitInputs ⋯ using (InitialInputsAgree; ValidDeclarations)
open import zkir-v4.CircuitProof ⋯ using (honest-witness)
open import zkir-v4.CircuitProperties ⋯ using (satisfying-public-inputs)
open import zkir-v4.CircuitReplay ⋯ using (ReplayTrace; extraction-complete)
open import zkir-v4.EncodingProperties ⋯ using (EncodingLaws)
open import zkir-v4.ForwardShape ⋯ using (Along; ready-from-preprocess)
open import zkir-v4.Semantics ⋯ using (ProofPreimage; State; preprocess; full-public-inputs)
open import zkir-v4.SemanticsProperties ⋯ using (AcceptedRun; preprocess-inversion; preprocess-full-inputs)
open import zkir-v4.Syntax ⋯ using (IrSource)
open import zkir-v4.Validation ⋯ using (validate)

open import Data.Bool using (true)
open import Data.List using ([])
open import Data.Maybe using (just)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; trans; cong)

-- Local source, assignment and operation conditions for the extracted
-- preimage's own honest witness. Along applies them at the intermediate
-- states of the accepted run, which the theorem obtains by inversion.
record RebuiltShape (src : IrSource) (p : ProofPreimage) (final : State)
                    (accepted : preprocess src p ≡ just final) : Set where
  field
    initial-inputs : InitialInputsAgree src p (honest-witness p final)
    local-shape : Along (honest-witness p final)
      (AcceptedRun.trace (preprocess-inversion {src} {p} accepted))

rebuilt-satisfies : EncodingLaws → PreparationLaws → ∀ src p final
  → (accepted : preprocess src p ≡ just final)
  → RebuiltShape src p final accepted
  → satisfies src (honest-witness p final) (view final [])
rebuilt-satisfies encoding prepare src p final accepted local =
  forward src p final encoding prepare accepted (RebuiltShape.initial-inputs local)
    (ready-from-preprocess src p final (honest-witness p final) accepted (RebuiltShape.local-shape local))

record ExtractedPair (src : IrSource) (w : CircuitWitness) (target : CircuitState) : Set where
  field
    preimage : ProofPreimage
    final : State
    extracted : extract src w ≡ just preimage
    preprocessed : preprocess src preimage ≡ just final
    rebuilt : satisfies src (honest-witness preimage final) (view final [])
    same-statement : State.pis final ≡ CircuitState.pis target
    same-carried : State.exposed final ≡ CircuitState.accs target
    same-full-input : full-public-inputs final ≡ CircuitWitness.full-pis w

-- Completeness for the extracted pair: the witness computed from the
-- extracted preimage satisfies the source and reproduces both public
-- input blocks, even though its inactive proof slots have been erased.
extracted-witness-complete : ∀ (encoding : EncodingLaws) (prepare : PreparationLaws)
                               src w start target streams
  → validate src ≡ true
  → ValidDeclarations (IrSource.inputs src)
  → initᶜ src w ≡ just start
  → satisfies src w target
  → ReplayTrace src w start (IrSource.instructions src) streams target
  → (IrSource.do-communications-commitment src ≡ true →
       encode-inputs (CircuitState.mem target) (IrSource.inputs src)
       ≡ encode-inputs (CircuitState.mem start) (IrSource.inputs src))
  → (∀ p final → extract src w ≡ just p
       → (accepted : preprocess src p ≡ just final) → RebuiltShape src p final accepted)
  → ExtractedPair src w target
extracted-witness-complete encoding prepare src w start target streams
  valid declarations initialized satisfied trace stable rebuild
  with extraction-complete encoding prepare src w start target streams
         valid declarations initialized satisfied trace stable
... | p , last , extracted , accepted , matches = record
  { preimage = p
  ; final = last
  ; extracted = extracted
  ; preprocessed = accepted
  ; rebuilt = rebuilt-satisfies encoding prepare src p last accepted (rebuild p last extracted accepted)
  ; same-statement = cong CircuitState.pis matches
  ; same-carried = cong CircuitState.accs matches
  ; same-full-input =
      trans (preprocess-full-inputs {src} {p} accepted)
        (trans (cong full-public-inputsᶜ matches)
               (satisfying-public-inputs {src = src} {w = w} satisfied))
  }
