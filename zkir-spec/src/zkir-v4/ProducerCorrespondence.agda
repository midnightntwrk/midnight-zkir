{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.ProducerCorrespondence (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Types ⋯
open import zkir-v4.Syntax ⋯
open import zkir-v4.Circuit ⋯
open import zkir-v4.CircuitBridge ⋯ using (view)
open import zkir-v4.CircuitEffects ⋯ using (PreparationForward; PreparationBackward)
open import zkir-v4.CircuitExtraction ⋯ using (extract)
open import zkir-v4.CircuitForward ⋯ using (forward-using)
open import zkir-v4.CircuitProof ⋯ using (honest-witness)
open import zkir-v4.CircuitProperties ⋯ using (SatisfiedRun; satisfying-run)
open import zkir-v4.EncodingProperties ⋯ using (EncodingLaws)
open import zkir-v4.Producer ⋯ using (Producer)
open import zkir-v4.ProducerCompute ⋯ using (compute-types)
open import zkir-v4.ProducerSupport ⋯ using (ForwardDomain)
open import zkir-v4.ProducerForward ⋯ using (ForwardDomains; forward-with-typed-compute; HonestRun; typed-honest-run)
open import zkir-v4.StatementUniqueness ⋯ using (canonical; extract-honest)
import zkir-v4.ReverseProducer ⋯ as Reverse
open import zkir-v4.ProducerResiduals ⋯ using (unchecked-along; producer-along; static-along)
open import zkir-v4.ReplayFragment ⋯ using (Fragment; source-residuals)
open import zkir-v4.Semantics ⋯ using (preprocess; State; ProofPreimage)
open import zkir-v4.SemanticsProperties ⋯ using (AcceptedRun; preprocess-inversion; Trace; done; next)
open import zkir-v4.Validation ⋯ using (validate)
open import zkir-v4.Protocol ⋯
import zkir-v4.ProtocolProperties ⋯ as Completeness
import zkir-v4.StatementSoundness ⋯ as Soundness
open import Data.Bool using (true; false)
open import Data.List using (List; [])
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Unit using (tt)
open import Data.Maybe using (just)
open import Data.Product using (∃; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Source-wide primitive contracts can be supplied before running the VM.
-- For instructions that call neither an aligned hash nor preparation,
-- the local condition is the unit type.
source-domains : ∀ {p src st is final} → All (λ i → ∀ before → ForwardDomain src before i) is
               → (path : Trace p src st is final) → ForwardDomains path
source-domains [] done = tt
source-domains (head ∷ tail) (next {st = st} _ path) = head st , source-domains tail path

producer-forward : ∀ src p final → PreparationForward → Producer src
                 → (ran : preprocess src p ≡ just final)
                 → ForwardDomains (AcceptedRun.trace (preprocess-inversion {src} {p} ran))
                 → satisfies src (honest-witness p final) (view final [])
producer-forward = forward-with-typed-compute compute-types

producer-honest-round-trip : PreparationForward → ∀ src p final → Producer src
  → (ran : preprocess src p ≡ just final)
  → ForwardDomains (AcceptedRun.trace (preprocess-inversion {src} {p} ran))
  → extract src (honest-witness p final) ≡ just (canonical src p final)
producer-honest-round-trip prepare src p final producer ran domains =
  extract-honest src p final prepare ran initialized ready encoded-inputs
    (forward-using src p final prepare ran inputs-agree initialized ready)
  where open HonestRun (typed-honest-run compute-types src p final producer ran domains)

producer-extract : EncodingLaws → PreparationBackward
                 → ∀ src w target → Producer src → (sat : satisfies src w target)
                 → unchecked-along w (IrSource.instructions src) (SatisfiedRun.path (satisfying-run src w target sat))
                 → ∃ λ p → ∃ λ final → extract src w ≡ just p × preprocess src p ≡ just final
                     × view final (CircuitState.proof-rem target) ≡ target
producer-extract codecs prepare src w target producer sat local =
  Reverse.producer-reverse codecs prepare compute-types src w target producer sat
    (producer-along src w target producer (satisfying-run src w target sat) local)

fragment-extract : EncodingLaws → PreparationBackward
                 → ∀ src w target → Producer src → Fragment src → satisfies src w target
                 → ∃ λ p → ∃ λ final → extract src w ≡ just p × preprocess src p ≡ just final
                     × view final (CircuitState.proof-rem target) ≡ target
fragment-extract codecs prepare src w target producer fragment sat =
  producer-extract codecs prepare src w target producer sat
    (static-along (source-residuals w fragment) (SatisfiedRun.path (satisfying-run src w target sat)))

private
  validated : ∀ src → Producer src → validate src ≡ true
  validated src producer with validate src
  ... | true = refl
  ... | false with () ← producer

module ForKey (src : IrSource) (OuterOK : List Byte → List Fr → Set) where
  open Verification OuterOK hiding (sound)
  module Backend = Completeness.Backend OuterOK
  module Shaped = Soundness.ForKey src OuterOK

  -- Knowledge extraction for the outer circuit relates the witness to
  -- the entire verified instance, including the carried accumulator fields.
  ExtractsWitness : Set
  ExtractsWitness = ∀ raw pi → OuterOK raw pi →
    ∃ λ w → ∃ λ st → satisfies src w st × CircuitWitness.full-pis w ≡ pi

  complete-from-producer : ∀ p final → PreparationForward → Producer src → Backend.FromCircuit src
                         → (ran : preprocess src p ≡ just final)
                         → ForwardDomains (AcceptedRun.trace (preprocess-inversion {src} {p} ran))
                         → All PairingOK (State.exposed final)
                         → ∃ λ raw → Accepts (exposures (IrSource.instructions src))
                                             (proof raw (State.exposed final)) (State.pis final)
  complete-from-producer p final prepare producer backend ran domains =
    Backend.prover-complete {src} {p} {final} backend ran
      (producer-forward src p final prepare producer ran domains)

  Explains : Proof → List Fr → Set
  Explains pr stmt =
    (∃ λ w → ∃ λ p → ∃ λ final → extract src w ≡ just p × preprocess src p ≡ just final
       × State.exposed final ≡ Proof.carried pr × State.pis final ≡ stmt) × All PairingOK (Proof.carried pr)

  -- A source-specific argument may use constraints established by preceding
  -- instructions to prove a guard or an exact comparison bound.
  sound-with-residuals : EncodingLaws → PreparationBackward → Producer src
                       → (∀ w st (sat : satisfies src w st) →
                            unchecked-along w (IrSource.instructions src)
                              (SatisfiedRun.path (satisfying-run src w st sat)))
                       → ExtractsWitness → ∀ {pr stmt}
                       → Accepts (exposures (IrSource.instructions src)) pr stmt → Explains pr stmt
  sound-with-residuals codecs prepare producer residuals backend =
    Shaped.sound-using codecs prepare (validated src producer) (Reverse.producer-declarations src producer) shaped
    where
    shaped : Shaped.ExtractsShapedWitness
    shaped raw pi accepted with backend raw pi accepted
    ... | w , target , sat , bound =
      w , target , sat , bound , Reverse.producer-shape codecs prepare compute-types src w target producer
        checked (producer-along src w target producer checked (residuals w target sat))
      where checked = satisfying-run src w target sat

  sound-on-fragment : EncodingLaws → PreparationBackward → Producer src → Fragment src → ExtractsWitness
                    → ∀ {pr stmt} → Accepts (exposures (IrSource.instructions src)) pr stmt → Explains pr stmt
  sound-on-fragment codecs prepare producer fragment =
    sound-with-residuals codecs prepare producer λ w st sat →
      static-along (source-residuals w fragment) (SatisfiedRun.path (satisfying-run src w st sat))
