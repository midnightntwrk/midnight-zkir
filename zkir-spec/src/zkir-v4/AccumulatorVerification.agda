{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.AccumulatorVerification (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.AccumulatorEffects ⋯ using (Prepared; Valid)
open import zkir-v4.AccumulatorObligations ⋯ using
  (PreparationClaim; PreparationsSatisfy; zip-preparations; BadFold; sound-or-bad-fold)
open import zkir-v4.Circuit ⋯
open import zkir-v4.CircuitAccumulatorFrame ⋯ using (circuit-init-store; circuit-step-frame; CircuitFrame)
open import zkir-v4.CircuitEffects ⋯ using (PreparationLaws)
open import zkir-v4.CircuitProperties ⋯ using (Trace; next; end; SatisfiedRun; satisfying-run; satisfying-public-inputs)
open import zkir-v4.EncodingProperties ⋯ using (EncodingLaws)
open import zkir-v4.Operations ⋯ using (∅)
open import zkir-v4.Producer ⋯ using (Producer; Env; fresh; fold-check; producer-step)
open import zkir-v4.ProducerCorrespondence ⋯ using (module ForKey)
open import zkir-v4.ProducerStore ⋯ using (StoreTyped; infer-success; fold-cons)
open import zkir-v4.Protocol ⋯ using (module Verification; exposures; instance-fields)
open import zkir-v4.RecursiveVerification ⋯ using (instance-inj; DirectLaws; module Active)
open import zkir-v4.Syntax ⋯

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; length; map)
open import Data.List.Properties using (length-++)
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ; _+_)
open import Data.Nat.Properties using (+-identityʳ; +-assoc)
open import Data.Product using (∃; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)

private
  init-count : ∀ src w st → initᶜ src w ≡ just st → length (CircuitState.accs st) ≡ 0
  init-count src w st ok with declare w ∅ (IrSource.inputs src)
  ... | nothing with () ← ok
  init-count src w st ok | just m with IrSource.do-communications-commitment src
  ... | false with refl ← just-injective ok = refl
  init-count src w st ok | just m | true with CircuitWitness.comm-commitment w
  ... | nothing with () ← ok
  init-count src w st ok | just m | true | just _ with refl ← just-injective ok = refl

  trace-count : ∀ src w st is final Γ {Γ′} →
    StoreTyped Γ (CircuitState.mem st) →
    fold-check (producer-step (IrSource.outputs src)) Γ is ≡ just Γ′ →
    Trace src w st (map lower is) final →
    length (CircuitState.accs final) ≡ length (CircuitState.accs st) + exposures is
  trace-count src w st [] .st Γ typed code end = sym (+-identityʳ _)
  trace-count src w st (i ∷ is) final Γ typed code (next {st′ = after} ok rest)
    with fold-cons (producer-step (IrSource.outputs src)) Γ i is code
  ... | env , head , tail with circuit-step-frame src w st i after Γ typed head ok
  ... | frame with CircuitFrame.accs frame
  ... | suffix , width , appended =
    trans (trace-count src w after is final env (CircuitFrame.typed-after frame) tail rest)
      (trans (cong (_+ exposures is) (trans (cong length appended)
          (trans (length-++ (CircuitState.accs st) {suffix}) (cong (length (CircuitState.accs st) +_) width))))
        (+-assoc (length (CircuitState.accs st)) _ (exposures is)))

-- The ledger key fixes the length of the leading accumulator block.  The
-- extracted circuit must have published exactly that many accumulators.
circuit-exposure-count : ∀ src w final → Producer src → SatisfiedRun src w final →
  length (CircuitState.accs final) ≡ exposures (IrSource.instructions src)
circuit-exposure-count src w final producer run with infer-success src producer
... | Γ , final-env , decls , code =
  trans (trace-count src w initial _ final Γ (circuit-init-store src w decls initialized) code (SatisfiedRun.path run))
        (cong (_+ exposures (IrSource.instructions src)) (init-count src w initial initialized))
  where
  initial = SatisfiedRun.start run
  initialized = SatisfiedRun.initialized run

-- Backend extraction binds the witness to the concatenated instance.  The
-- source's exposure count fixes the split between the carries and statement.
module Binding (src : IrSource) (OK : List Byte → List Fr → Set) where
  open Verification OK

  record BoundRun (carried : List Accumulator) (stmt : List Fr) : Set where
    field
      witness : CircuitWitness
      final : CircuitState
      satisfied : satisfies src witness final
      same-carried : CircuitState.accs final ≡ carried
      same-statement : CircuitState.pis final ≡ stmt
    run = satisfying-run src witness final satisfied

  bind-execution : EncodingLaws → Producer src → ForKey.ExtractsWitness src OK →
    ∀ pr stmt → Accepts (exposures (IrSource.instructions src)) pr stmt → BoundRun (Proof.carried pr) stmt
  bind-execution codecs producer extract pr stmt ok with extract (Proof.raw pr) _ (Accepts.outer-valid ok)
  ... | w , final , sat , full
    with instance-inj codecs (CircuitState.accs final) (Proof.carried pr)
           (trans (circuit-exposure-count src w final producer (satisfying-run src w final sat))
                  (sym (Accepts.count-matches ok)))
           (trans (satisfying-public-inputs {src} {w} sat) full)
  ... | same , suffix = record
    { witness = w ; final = final ; satisfied = sat ; same-carried = same ; same-statement = suffix }

module Ledger (src : IrSource) (OuterOK : List Byte → List Fr → Set) where
  open Verification OuterOK
  open Binding src OuterOK
  code = IrSource.instructions src

  record Accounted (P : PreparationClaim src) (pr : Proof) (stmt : List Fr) : Set where
    field
      execution : BoundRun (Proof.carried pr) stmt
    open BoundRun execution public renaming (satisfied to satisfies-source)
    field
      obligations : PreparationsSatisfy P code (SatisfiedRun.path run) ⊎ BadFold code (SatisfiedRun.path run)

  openings-or-bad-fold : EncodingLaws → Producer src → ForKey.ExtractsWitness src OuterOK →
    ∀ pr stmt → Accepts (exposures code) pr stmt → Accounted (λ e → Valid (Prepared.opening e)) pr stmt
  openings-or-bad-fold codecs producer extract pr stmt ok = record
    { execution = e
    ; obligations = sound-or-bad-fold src (BoundRun.witness e) (BoundRun.final e) producer (BoundRun.run e)
        (subst (All Valid) (sym (BoundRun.same-carried e)) (Accepts.pairings ok)) }
    where
    e = bind-execution codecs producer extract pr stmt ok

  module Inner (Direct : List Byte → List Fr → List Byte → Set)
               (chip : PreparationLaws) where

    -- Only active preparations on an extracted execution need verifier agreement.
    LawsOnRun : Set
    LawsOnRun = ∀ {carried stmt} (e : BoundRun carried stmt) →
      PreparationsSatisfy (λ p → DirectLaws Direct (Prepared.key p) (Prepared.fields p))
        code (SatisfiedRun.path (BoundRun.run e))

    DirectlyAccepted : PreparationClaim src
    DirectlyAccepted e = ∃ λ bytes → Direct (Prepared.key e) (Prepared.fields e) bytes

    preparations-or-bad-fold : LawsOnRun → EncodingLaws → Producer src → ForKey.ExtractsWitness src OuterOK →
      ∀ pr stmt → Accepts (exposures code) pr stmt → Accounted DirectlyAccepted pr stmt
    preparations-or-bad-fold laws codecs producer extract pr stmt ok with openings-or-bad-fold codecs producer extract pr stmt ok
    ... | accounted = record
      { execution = Accounted.execution accounted ; obligations = direct-result }
      where
      path = SatisfiedRun.path (Accounted.run accounted)
      direct-result : PreparationsSatisfy DirectlyAccepted code path ⊎ BadFold code path
      direct-result with Accounted.obligations accounted
      ... | inj₂ bad = inj₂ bad
      ... | inj₁ all-valid = inj₁ (zip-preparations direct code path (laws (Accounted.execution accounted)) all-valid)
        where
        direct : ∀ {st g hash ops id out st′} (e : Prepared src st g hash ops id out st′) →
          Prepared.active e ≡ true → DirectLaws Direct (Prepared.key e) (Prepared.fields e) →
          Valid (Prepared.opening e) → DirectlyAccepted e
        direct e on law = Active.circuit-to-direct law
          chip (Prepared.parsed e) (Prepared.raw e) (Prepared.opening e)
          (subst (λ flag → prepare-circuit _ _ _ flag ≡ just _) on (Prepared.prepared e))
