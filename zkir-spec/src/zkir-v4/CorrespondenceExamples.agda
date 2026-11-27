{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.CorrespondenceExamples (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Syntax ⋯
open import zkir-v4.Types ⋯
open import zkir-v4.Producer ⋯ using (Producer)
open import zkir-v4.ReplayFragment ⋯
open import zkir-v4.EncodingProperties ⋯ using (EncodingLaws)
open import zkir-v4.ReferenceExample ⋯ using (module Packing)
open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Maybe using (nothing)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (refl)

-- The byte-packing example in the reference has eight instructions,
-- including a checked equality, a public impact and a typed output.
packing-fragment : ∀ laws binding → Fragment (Packing.source laws binding)
packing-fragment laws binding = tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []

packing-producer : ∀ laws binding → Producer (Packing.source laws binding)
packing-producer laws binding = tt

-- A private read can drive a comparison and both output channels while
-- the commitment binds the original declared input.
compare-source : IrSource
compare-source = mk-ir-source V0 (("limit" ⦂ native) ∷ []) (native ∷ []) true
  (private-input nothing native "value" ∷
   less-than (var "value") (var "limit") 8 "below" ∷
   impact (imm 1ᶠ) (var "below" ∷ []) ∷
   circuit-output (var "below" ∷ []) ∷ []) []

compare-producer : Producer compare-source
compare-producer = tt

compare-fragment : Fragment compare-source
compare-fragment =
  unguarded ∷ refl ∷ tt ∷ tt ∷ []

-- The reference example executes successfully for every binding input.
-- Apply both correspondence theorems to that actual execution.
module PackingRoundTrip (laws : EncodingLaws) (binding : Fr) where
  open Packing laws binding using (source; preimage; example)
  open import zkir-v4.Circuit ⋯ using (satisfies; CircuitState)
  open import zkir-v4.CircuitBridge ⋯ using (view)
  open import zkir-v4.CircuitEffects ⋯ using (PreparationForward; PreparationBackward)
  open import zkir-v4.CircuitExtraction ⋯ using (extract)
  open import zkir-v4.CircuitProof ⋯ using (honest-witness)
  open import zkir-v4.ProducerCorrespondence ⋯ using (producer-forward; fragment-extract; source-domains)
  open import zkir-v4.Semantics ⋯ using (State; preprocess)
  open import zkir-v4.SemanticsProperties ⋯ using (AcceptedRun; preprocess-inversion)
  open import Data.Maybe using (just)
  open import Data.Product using (∃; _×_)
  open import Relation.Binary.PropositionalEquality using (_≡_)

  private
    accepted : ∃ λ final → preprocess source preimage ≡ just final
    accepted with preprocess source preimage in ran | example
    ... | nothing | ()
    ... | just final | _ = final , refl

  round-trip : PreparationForward → PreparationBackward →
    ∃ λ final → preprocess source preimage ≡ just final ×
      satisfies source (honest-witness preimage final) (view final []) ×
      (∃ λ recovered → ∃ λ replayed →
        extract source (honest-witness preimage final) ≡ just recovered ×
        preprocess source recovered ≡ just replayed × view replayed [] ≡ view final [])
  round-trip forward backward with accepted
  ... | final , ran = final , ran , sat ,
    fragment-extract laws backward source (honest-witness preimage final) (view final [])
      (packing-producer laws binding) (packing-fragment laws binding) sat
    where
    domains = source-domains {src = source}
      ((λ _ → tt) ∷ (λ _ → tt) ∷ (λ _ → tt) ∷ (λ _ → tt) ∷
       (λ _ → tt) ∷ (λ _ → tt) ∷ (λ _ → tt) ∷ (λ _ → tt) ∷ [])
      (AcceptedRun.trace (preprocess-inversion {source} {preimage} ran))
    sat = producer-forward source preimage final forward (packing-producer laws binding) ran domains
