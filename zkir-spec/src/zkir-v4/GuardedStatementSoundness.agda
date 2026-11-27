{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.GuardedStatementSoundness (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Circuit ⋯ using (CircuitWitness; CircuitState; satisfies)
open import zkir-v4.CircuitEffects ⋯ using (PreparationBackward)
open import zkir-v4.CircuitProperties ⋯ using (satisfying-public-inputs)
open import zkir-v4.EncodingProperties ⋯ using (EncodingLaws)
open import zkir-v4.GuardedExamples ⋯ using (module Documented)
open import zkir-v4.ProducerCorrespondence ⋯ using (module ForKey)
open import zkir-v4.Protocol ⋯ using (module Verification; exposures)
open import zkir-v4.ProtocolProperties ⋯ using (instance-inj)
open import zkir-v4.Semantics ⋯ using (State)
open import zkir-v4.SemanticsProperties ⋯ using (preprocess-exposure)
open import zkir-v4.Syntax ⋯ using (IrSource)
open import Data.Bool using (Bool)
open import Data.List using (List; []; length)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; sym; trans)

-- The inner key is the one substituted into the worked source.  OuterOK
-- verifies bytes under the outer key generated for that particular source.
module ForExamples (key : List Byte) (OuterOK : List Byte → List Fr → Set)
                   (codecs : EncodingLaws) (prepare : PreparationBackward) where
  open Documented key
  open Verification OuterOK using (Accepts; Proof)

  -- Keep the canonical VM run, including its guard, slots and skips.
  -- Its carried values and statement are exactly those checked by the ledger.
  record Explanation (src : IrSource) (guards : Bool → List Bool) (statement : Fr → Bool → List Fr)
                     (impacts : Bool → List Fr) (skips : Bool → List (Maybe ℕ))
                     (pr : Proof) (s : List Fr) : Set where
    field
      witness : CircuitWitness
      target : CircuitState
      satisfied : satisfies src witness target
      replay : Replay src witness target guards statement impacts skips
      carried : State.exposed (Replay.final replay) ≡ Proof.carried pr
      published : State.pis (Replay.final replay) ≡ s

  private
    from-replay : ∀ src {guards statement impacts skips} →
      (∀ w st → satisfies src w st → Replay src w st guards statement impacts skips) →
      ForKey.ExtractsWitness src OuterOK → ∀ {pr s} →
      Accepts (exposures (IrSource.instructions src)) pr s →
      Explanation src guards statement impacts skips pr s
    from-replay src replay-witness extracts {pr} {s} accepted
      with extracts _ _ (Accepts.outer-valid accepted)
    ... | w , target , sat , full =
      let r = replay-witness w target sat
          count = proj₂ (preprocess-exposure {src} {Replay.preimage r} (Replay.accepted r))
          checked = instance-inj codecs (CircuitState.accs target) (Proof.carried pr)
                      (trans (cong length (sym (Replay.same-carried r)))
                        (trans count (sym (Accepts.count-matches accepted))))
                      (trans (satisfying-public-inputs {src} {w} {target} sat) full)
      in record
        { witness = w
        ; target = target
        ; satisfied = sat
        ; replay = r
        ; carried = trans (Replay.same-carried r) (proj₁ checked)
        ; published = trans (Replay.same-statement r) (proj₂ checked)
        }

  one-sound : ForKey.ExtractsWitness one-source OuterOK → ∀ {pr s} →
    Accepts 1 pr s →
    Explanation one-source one-guards (λ b _ → one-statement b) (λ _ → []) (λ _ → []) pr s
  one-sound = from-replay one-source (one-replay prepare)

  fold-sound : ForKey.ExtractsWitness fold-source OuterOK → ∀ {pr s} →
    Accepts 1 pr s → Explanation fold-source fold-guards fold-statement fold-impacts fold-skips pr s
  fold-sound = from-replay fold-source (fold-replay prepare)
