{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.RunShape (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Syntax ⋯
open import zkir-v4.Types ⋯
open import zkir-v4.Semantics ⋯
open import zkir-v4.SemanticsProperties ⋯ using (AcceptedRun; preprocess-inversion; preprocess-full-inputs)
open import zkir-v4.Circuit ⋯
open import zkir-v4.CircuitBridge ⋯
open import zkir-v4.CircuitProof ⋯ using (honest-witness; Common; apply; core-step)
open import zkir-v4.CircuitEffects ⋯
open import zkir-v4.CircuitPure ⋯
open import zkir-v4.CircuitInputs ⋯ using (InitialInputsAgree; init-forward)
open import zkir-v4.EncodingProperties ⋯ using (EncodingLaws)
open import zkir-v4.Validation ⋯ using (validate; resolve-vk)
open import zkir-v4.ProofSlots using (keep)

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Nat using (_≤_)
open import Data.Product using (_×_; _,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)
import Relation.Nullary

-- Local witness obligations refer to VM values, bounds, transcript
-- slices, and fixed-key preparation.  They certify each actual
-- instruction without assuming circuit execution or satisfaction.
data ReadyStep (p : ProofPreimage) (src : IrSource) (w : CircuitWitness) (st : State)
               : List (List Byte) → Instruction → State → List (List Byte) → Set where
  common : ∀ {retained i writes}
           → Common i
           → compute (State.mem st) i ≡ just writes
           → WriteAgreement (check-shared-writes i) w writes
           → ReadyStep p src w st retained i (apply st writes) retained
  bit-constraint : ∀ {retained op bits writes}
           → bits ≤ FR-BITS
           → compute (State.mem st) (constrain-bits op bits) ≡ just writes
           → WriteAgreement true w writes
           → ReadyStep p src w st retained (constrain-bits op bits) (apply st writes) retained
  division : ∀ {retained op bits outs writes}
           → bits ≤ FR-BITS
           → compute (State.mem st) (div-mod-power-of-two op bits outs) ≡ just writes
           → WriteAgreement true w writes
           → ReadyStep p src w st retained (div-mod-power-of-two op bits outs) (apply st writes) retained
  reconstitution : ∀ {retained div mod bits out writes}
           → bits ≤ FR-BITS
           → compute (State.mem st) (reconstitute-field div mod bits out) ≡ just writes
           → WriteAgreement true w writes
           → ReadyStep p src w st retained (reconstitute-field div mod bits out) (apply st writes) retained
  special : ∀ {retained i writes}
           → Special (State.mem st) i
           → compute (State.mem st) i ≡ just writes
           → WriteAgreement (special-checked i) w writes
           → ReadyStep p src w st retained i (apply st writes) retained
  public-read : ∀ {retained g t id active v}
           → eval-guard (State.mem st) g ≡ just active
           → ReadValue active t (State.pto-rem st) v
           → CircuitWitness.assign w id ≡ just v
           → typeof v ≡ t
           → ReadyStep p src w st retained (public-input g t id) (public-result t st id active v) retained
  private-read : ∀ {retained g t id active v}
           → eval-guard (State.mem st) g ≡ just active
           → ReadValue active t (State.priv-rem st) v
           → CircuitWitness.assign w id ≡ just v
           → typeof v ≡ t
           → ReadyStep p src w st retained (private-input g t id) (private-result t st id active v) retained
  impact-step : ∀ {retained g ops active values}
           → resolve𝔹 (State.mem st) g ≡ just active
           → resolve-all-Fr (State.mem st) ops ≡ just values
           → ImpactRead p st ops active values
           → ReadyStep p src w st retained (impact g ops) (impact-result st ops active values) retained
  proof-slot : ∀ {retained g id raw rest active}
           → State.proof-rem st ≡ raw ∷ rest
           → resolve𝔹 (State.mem st) g ≡ just active
           → ReadyStep p src w st (keep active raw ∷ retained) (inner-proof g id)
                (bind-result st id (keep active raw) rest) retained
  prepare-step : ∀ {retained g hash ops proof out active values blob key acc}
           → resolve𝔹 (State.mem st) g ≡ just active
           → resolve-all-Fr (State.mem st) ops ≡ just values
           → State.proofs st proof ≡ just blob
           → resolve-vk hash (IrSource.inner-vks src) ≡ just key
           → key-well-formed key ≡ true
           → Preparation active key values blob acc
           → Agrees w out (val-accumulator acc)
           → ReadyStep p src w st retained (prepare-verification g hash ops proof out)
                 (out1 st out (val-accumulator acc)) retained
  fold-step : ∀ {retained ops out a b rest acc}
           → resolve-accs (State.mem st) ops ≡ just (a ∷ b ∷ rest)
           → fold-accumulators (a ∷ b ∷ rest) ≡ just acc
           → Agrees w out (val-accumulator acc)
           → ReadyStep p src w st retained (accumulate ops out)
                 (out1 st out (val-accumulator acc)) retained
  expose-step : ∀ {retained op acc}
           → resolve-acc (State.mem st) op ≡ just acc
           → ReadyStep p src w st retained (verify-accumulator op)
                 (exposure-result st acc) retained
  output-step : ∀ {retained ops values}
           → collectOutputs (State.mem st) (IrSource.outputs src) ops ≡ just values
           → ReadyStep p src w st retained (circuit-output ops)
                 (record st { outs = State.outs st ++ values }) retained

-- The premise records the successful preprocessing path together with
-- the extra witness and chip conditions at each instruction.  The
-- retained-list index accounts for normalization at each proof read.
data ReadyRun (p : ProofPreimage) (src : IrSource) (w : CircuitWitness)
             : State → List (List Byte) → List Instruction → State → List (List Byte) → Set where
  empty : ∀ {st retained} → ReadyRun p src w st retained [] st retained
  instr : ∀ {st init-retained i next retained is final final-retained}
          → ReadyStep p src w st init-retained i next retained
          → ReadyRun p src w next retained is final final-retained
          → ReadyRun p src w st init-retained (i ∷ is) final final-retained
