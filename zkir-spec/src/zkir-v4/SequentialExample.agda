{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.SequentialExample (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Circuit ⋯ using (CircuitState)
open import zkir-v4.CircuitEffects ⋯ using (PreparationLaws)
open import zkir-v4.CircuitProperties ⋯ using (satisfying-public-inputs)
open import zkir-v4.EncodingProperties ⋯ using (EncodingLaws)
open import zkir-v4.ProducerCorrespondence ⋯ using (module ForKey)
open import zkir-v4.Protocol ⋯ using (exposures; instance-fields; KeyArity; MatchesKey)
open import zkir-v4.RecursiveVerification ⋯ using (Valid; DirectLaws; instance-inj)
open import zkir-v4.SequentialSource ⋯ hiding (iterate; validated)
open import zkir-v4.SequentialSource ⋯ public using (validated)
open import zkir-v4.SequentialVerification ⋯ using (Claim; claim; module Chain)
open import zkir-v4.Syntax ⋯ using (IrSource)
open import Data.Bool using (true)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Properties using (∷-injective; length-replicate)
open import Data.List.Relation.Unary.All as All using (All)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; zero; suc; _≤_; _+_; _*_)
open import Data.Product using (∃; _×_; _,_; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Relation.Nullary using (¬_)

source-count : ∀ keys n → exposures (IrSource.instructions (source keys n)) ≡ carried-count n
source-count keys zero = refl
source-count keys (suc zero) = refl
source-count keys (suc (suc n)) = refl

-- The key selects this program.  The statement binds its context, both
-- endpoints and a natural count via the number of trailing zero fields.
encode-claim : Claim ⊤ Fr Fr → List Fr
encode-claim (claim tt context start finish n) = fields n context start finish

claim-injective : ∀ {a b} → encode-claim a ≡ encode-claim b → a ≡ b
claim-injective {claim tt c x y n} {claim tt d u v m} eq
  with ∷-injective eq
... | _ , tail with ∷-injective tail
... | refl , tail′ with ∷-injective tail′
... | refl , tail″ with ∷-injective tail″
... | refl , markers = cong (claim tt c x y)
  (trans (sym (length-replicate n {x = 0ᶠ})) (trans (cong length markers) (length-replicate m)))

-- Universal deterministic premise of exact-execution and counter-sound.
-- The computational bad-fold game instead bounds the chance that an
-- algorithm can find a pair violating this implication.
PairSound : Set
PairSound = ∀ a b f → fold-accumulators (a ∷ b ∷ []) ≡ just f → Valid f → Valid a × Valid b

discharge : PairSound → ∀ {as bs} → Carries as bs → All Valid as → All Valid bs
discharge _ single checked = checked
discharge sound (batch {a} {b} {f} eq) (ok All.∷ All.[]) with sound a b f eq ok
... | left , right = left All.∷ right All.∷ All.[]

-- The lists identify the output checked at this layer and the two input
-- equations that the circuit folded into it.
data Cancellation : List Accumulator → List Accumulator → Set where
  cancellation : ∀ {a b f} → fold-accumulators (a ∷ b ∷ []) ≡ just f →
    Valid f → ¬ (Valid a × Valid b) → Cancellation (f ∷ []) (a ∷ b ∷ [])

private
  failed-fold : ∀ {as bs} → Carries as bs → All Valid as → ¬ All Valid bs → Cancellation as bs
  failed-fold single valid invalid = ⊥-elim (invalid valid)
  failed-fold (batch folded) (ok All.∷ All.[]) invalid =
    cancellation folded ok (λ { (left , right) → invalid (left All.∷ right All.∷ All.[]) })

module Counter
  (inner-key ledger-key : ℕ → List Byte)
  (Direct Ledger : List Byte → List Fr → List Byte → Set)
  (codecs : EncodingLaws) (chip : PreparationLaws)
  (limit : ℕ)
  (parsed : ∀ n → n ≤ limit → key-well-formed (inner-key n) ≡ true)
  (arity : KeyArity)
  (schemas : InnerSchema arity inner-key limit)
  (laws : ∀ n → suc n ≤ limit → ∀ ctx start finish carried →
    length carried ≡ carried-count n →
    let pi = instance-fields carried (fields n ctx start finish) in
    MatchesKey arity (inner-key n) pi → DirectLaws Direct (inner-key n) pi) where

  module Example (context : Fr) = Chain tt context
    (λ _ c x → x ≡ c) (λ _ _ previous finish → finish ≡ previous +ᶠ 1ᶠ)
    encode-claim claim-injective Direct Ledger chip inner-key ledger-key
    carried-count carried-count limit parsed arity
    (λ n within start finish → trans (schemas n within)
      (cong (λ width → just (carried-count n * 12 + width)) (sym (fields-width n context start finish))))
    (λ n within → laws n within context) Carries

  -- Both verification keys authenticate the circuit for the requested
  -- level.  That circuit embeds the preceding level's inner key.
  Extracts : (List Byte → List Fr → List Byte → Set) → (ℕ → List Byte) → Set
  Extracts verify key = ∀ n → n ≤ limit → ForKey.ExtractsWitness (source inner-key n) (λ raw pi → verify (key n) pi raw)

  private
    local : ∀ context verify key → Extracts verify key → Example.Local context verify key carried-count
    local context verify key extracts requested@(claim tt c x y n) within raw carried count ok
      with extracts n within raw _ ok
    ... | w , final , sat , full with observe inner-key n w final sat
    ... | seen with instance-inj codecs (CircuitState.accs final) carried
                       (trans (observation-count seen) (sym count))
                       (trans (satisfying-public-inputs {source inner-key n} {w} sat) full)
    ... | refl , suffix = identify seen suffix
      where
      identify : ∀ {binding s as} → Observation inner-key binding n s as → s ≡ encode-claim requested →
        ∃ λ observed → encode-claim observed ≡ encode-claim requested × Example.Layer context as observed
      identify (initial ctx) eq with ∷-injective eq
      ... | refl , tail = claim tt ctx ctx ctx zero , cong (0ᶠ ∷_) tail , Example.base refl
      identify (advanced {n = pred} ctx start previous raw opening count prep carried) eq with ∷-injective eq
      ... | refl , tail = claim tt ctx start (previous +ᶠ 1ᶠ) (suc pred) ,
        cong (0ᶠ ∷_) tail , Example.advance refl count prep carried

  module Verified (inner-extracts : Extracts Direct inner-key)
                  (ledger-extracts : Extracts Ledger ledger-key) where

    module Proof (ctx : Fr) = Example.Soundness ctx (local ctx Direct inner-key inner-extracts)
                                                    (local ctx Ledger ledger-key ledger-extracts)

    -- Reduction from acceptance to an exact-length execution or a reached
    -- binary cancellation, using the extraction and direct-verifier laws.
    execution-or-bad-fold : ∀ ctx n (within : n ≤ limit) start finish pr
      (ok : Example.Root.Accepts ctx n (carried-count n) pr (fields n ctx start finish)) →
      Example.Execution ctx n start finish ⊎
      (Σ (Example.BadCarry ctx) λ bad →
        Proof.Reaches ctx bad (Proof.root-layer ctx n within start finish pr ok) ×
        Cancellation (Example.BadCarry.carried bad) (Example.BadCarry.opening bad ∷ Example.BadCarry.child-carried bad))
    execution-or-bad-fold ctx n within start finish pr ok
      with Proof.sound-or-reached ctx n within start finish pr ok
    ... | inj₁ execution = inj₁ execution
    ... | inj₂ (bad , path) = inj₂ (bad , path , failed-fold (Example.BadCarry.exposed bad)
      (Example.BadCarry.checked bad) (Example.BadCarry.invalid bad))

    -- Corollary given the universal pairing implication for binary folds.
    exact-execution : PairSound → ∀ ctx n → n ≤ limit → ∀ start finish pr →
      Example.Root.Accepts ctx n (carried-count n) pr (fields n ctx start finish) →
      Example.Execution ctx n start finish
    exact-execution folds ctx = Proof.sound ctx (discharge folds)

    open import zkir-v4.SequentialSource ⋯ public using (iterate)

    private
      endpoints : ∀ ctx {n x y} → Example.Execution ctx n x y → x ≡ ctx × y ≡ iterate n x
      endpoints ctx (Example.begin init) = init , refl
      endpoints ctx (Example.extend path advance) with endpoints ctx path
      ... | start-ok , end-ok = start-ok , trans advance (cong (_+ᶠ 1ᶠ) end-ok)

    -- Endpoint corollary under the same deterministic premise.
    counter-sound : PairSound → ∀ ctx n → n ≤ limit → ∀ start finish pr →
      Example.Root.Accepts ctx n (carried-count n) pr (fields n ctx start finish) →
      start ≡ ctx × finish ≡ iterate n start
    counter-sound folds ctx n within start finish pr ok =
      endpoints ctx (exact-execution folds ctx n within start finish pr ok)
