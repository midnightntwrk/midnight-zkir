{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.ProtocolProperties (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Circuit ⋯
open import zkir-v4.CircuitBridge ⋯ using (view)
open import zkir-v4.CircuitProof ⋯ using (honest-witness)
open import zkir-v4.CircuitEffects ⋯ using (PreparationLaws)
open import zkir-v4.Encoding ⋯ using (encode-accumulator; decode)
open import zkir-v4.EncodingProperties ⋯ using (EncodingLaws; encode-decode)
open import zkir-v4.ExtractedWitness ⋯ using (RebuiltShape; rebuilt-satisfies)
open import zkir-v4.Protocol ⋯
open import zkir-v4.Semantics ⋯ using (preprocess; full-public-inputs; State; ProofPreimage)
open import zkir-v4.SemanticsProperties ⋯ using (preprocess-exposure; preprocess-full-inputs)
open import zkir-v4.Syntax ⋯ using (IrSource)
open import zkir-v4.Types ⋯ using (accumulator; val-accumulator)
open import Data.List using (List; []; _∷_; _++_; length; concatMap)
open import Data.List.Properties using (∷-injective; ++-assoc)
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe using (Maybe; just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat.Properties using (suc-injective)
open import Data.Product using (∃; _×_; _,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

private
  split-prefix : ∀ (xs ys : List Fr) {u v} → length xs ≡ length ys →
    xs ++ u ≡ ys ++ v → xs ≡ ys × u ≡ v
  split-prefix [] [] _ eq = refl , eq
  split-prefix (x ∷ xs) (y ∷ ys) n eq with ∷-injective eq
  ... | refl , rest with split-prefix xs ys (suc-injective n) rest
  ...   | refl , tail = refl , tail

  acc-inj : EncodingLaws → ∀ a b → encode-accumulator a ≡ encode-accumulator b → a ≡ b
  acc-inj laws a b eq with just-injective
    (trans (sym (encode-decode laws (val-accumulator a) refl))
      (trans (cong (decode accumulator) eq) (encode-decode laws (val-accumulator b) refl)))
  ... | refl = refl

-- A count check fixes the split between the carried block and statement.
instance-inj : EncodingLaws → ∀ as bs {s t} → length as ≡ length bs →
  instance-fields as s ≡ instance-fields bs t → as ≡ bs × s ≡ t
instance-inj laws [] [] _ eq = refl , eq
instance-inj laws (a ∷ as) (b ∷ bs) {s} {t} n eq with
  split-prefix (encode-accumulator a) (encode-accumulator b)
    (trans (accumulator-width a) (sym (accumulator-width b)))
    (trans (sym (++-assoc (encode-accumulator a) (concatMap encode-accumulator as) s))
     (trans eq (++-assoc (encode-accumulator b) (concatMap encode-accumulator bs) t)))
... | head , tail with acc-inj laws a b head | instance-inj laws as bs (suc-injective n) tail
...   | refl | refl , refl = refl , refl

module Backend (OuterOK : List Byte → List Fr → Set) where
  open Verification OuterOK public

  -- Backend completeness produces proof bytes for a satisfying assignment.
  -- The VM trace supplies the key count and both parts of the instance.
  module ForCircuit (check : IrSource → CircuitWitness → Maybe CircuitState) where
    FromCircuit : IrSource → Set
    FromCircuit src = ∀ w st → check src w ≡ just st
                    → ∃ λ raw → OuterOK raw (CircuitWitness.full-pis w)

    prover-complete : ∀ {src p final}
                    → FromCircuit src
                    → preprocess src p ≡ just final
                    → check src (honest-witness p final) ≡ just (view final [])
                    → All PairingOK (State.exposed final)
                    → ∃ λ raw → Accepts (exposures (IrSource.instructions src))
                                        (proof raw (State.exposed final)) (State.pis final)
    prover-complete {src} {p} {final} backend ran checked pairs with backend _ _ checked
    ... | raw , verifies = raw , complete {s = src}
        (proj₂ (preprocess-exposure {src} {p} ran))
        (subst (OuterOK raw) (preprocess-full-inputs {src} {p} ran) verifies) pairs

  open ForCircuit check-circuit public

  language-complete : ∀ {src p final} → EncodingLaws → PreparationLaws → FromCircuit src
                    → (ran : preprocess src p ≡ just final) → RebuiltShape src p final ran
                    → All PairingOK (State.exposed final)
                    → ∃ λ raw → Accepts (exposures (IrSource.instructions src))
                                        (proof raw (State.exposed final)) (State.pis final)
  language-complete {src} {p} {final} codecs prepare backend ran shape =
    prover-complete {src} {p} {final} backend ran (rebuilt-satisfies codecs prepare src p final ran shape)
