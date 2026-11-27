{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.SegmentJoinWitness (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Circuit ⋯
open import zkir-v4.CircuitBridge ⋯ using (guard-pass; prepare-forward; fold-forward; WriteAgreement)
open import zkir-v4.CircuitProperties ⋯ using (Trace; next; end; trace→run)
open import zkir-v4.Operations ⋯ using (_≟LFr_; insert-proof)
open import zkir-v4.Protocol ⋯ using (instance-fields)
open import zkir-v4.SegmentEncoding ⋯
open import zkir-v4.SegmentSource ⋯
open import zkir-v4.SegmentStatic ⋯ using (KeysSeparated; validate-source; resolve-left; resolve-right)
open import zkir-v4.SequentialSource ⋯ using (active; initial-state; install)
open import zkir-v4.Syntax ⋯
open import zkir-v4.Types ⋯

open import Data.Bool using (true)
open import Data.List using ([]; _∷_; map)
open import Data.Maybe using (just; nothing)
open import Data.Product using (∃; _×_; _,_)
open import Data.Sum using (inj₁)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

private
  encode-agrees : ∀ side c a m b lc rc statement slots carried →
    WriteAgreement true
      (mk-witness (join-memory c a m b lc rc) statement 0ᶠ nothing slots)
      (carry-writes side carried)
  encode-agrees lhs c a m b lc rc statement slots carried =
    inj₁ refl , inj₁ refl , inj₁ refl , inj₁ refl , inj₁ refl , inj₁ refl ,
    inj₁ refl , inj₁ refl , inj₁ refl , inj₁ refl , inj₁ refl , inj₁ refl , tt
  encode-agrees rhs c a m b lc rc statement slots carried =
    inj₁ refl , inj₁ refl , inj₁ refl , inj₁ refl , inj₁ refl , inj₁ refl ,
    inj₁ refl , inj₁ refl , inj₁ refl , inj₁ refl , inj₁ refl , inj₁ refl , tt

build : ∀ keys l r c a m b lc rc raw-l raw-r open-l open-r f →
  KeysSeparated keys (join l r) →
  key-well-formed (keys l) ≡ true →
  key-well-formed (keys r) ≡ true →
  prepare-circuit (keys l) (instance-fields (lc ∷ []) (fields (steps l) c a m)) raw-l true ≡ just open-l →
  prepare-circuit (keys r) (instance-fields (rc ∷ []) (fields (steps r) c m b)) raw-r true ≡ just open-r →
  fold-accumulators (open-l ∷ lc ∷ open-r ∷ rc ∷ []) ≡ just f →
  ∃ λ w → ∃ λ final → satisfies (source keys (join l r)) w final ×
    CircuitState.pis final ≡ fields (steps (join l r)) c a b × CircuitState.accs final ≡ (f ∷ [])
build keys l r c a m b lc rc raw-l raw-r open-l open-r f separated parsed-l parsed-r prepared-l prepared-r folded-ok =
  w , final , satisfied , refl , refl
  where
  src = source keys (join l r)
  statement = fields (steps (join l r)) c a b
  full-instance = instance-fields (f ∷ []) statement
  slots = raw-l ∷ raw-r ∷ []
  w = mk-witness (join-memory c a m b lc rc) full-instance 0ᶠ nothing slots
  first = initial-state w (join-memory c a m b lc rc)
  after-publish = published w (steps (join l r)) c a m b lc rc

  encoded-l = encoded-state lhs after-publish lc
  bound-l = record encoded-l
    { proofs = insert-proof (proof-id lhs) raw-l (CircuitState.proofs encoded-l)
    ; proof-rem = raw-r ∷ []
    }
  opened-l = install bound-l (opening-id lhs) (val-accumulator open-l)

  encoded-r = encoded-state rhs opened-l rc
  bound-r = record encoded-r
    { proofs = insert-proof (proof-id rhs) raw-r (CircuitState.proofs encoded-r)
    ; proof-rem = []
    }
  opened-r = install bound-r (opening-id rhs) (val-accumulator open-r)

  combined = install opened-r folded (val-accumulator f)
  final = record combined { accs = f ∷ [] }

  prepare-l : stepᶜ src w bound-l
    (prepare-proof (imm 1ᶠ) (key-digest (keys l)) (ops lhs (steps l)) (proof-id lhs) (opening-id lhs))
    ≡ just opened-l
  prepare-l = prepare-forward src w bound-l (imm 1ᶠ) (key-digest (keys l)) (ops lhs (steps l))
    (proof-id lhs) (opening-id lhs) true (instance-fields (lc ∷ []) (fields (steps l) c a m))
    raw-l (keys l) open-l active
    (resolve-child lhs (CircuitState.mem bound-l) (steps l) c a m lc
      (resolve-carried-fields lhs after-publish lc) refl refl refl)
    refl (resolve-left (keys l) (keys r)) parsed-l prepared-l (inj₁ refl)

  prepare-r : stepᶜ src w bound-r
    (prepare-proof (imm 1ᶠ) (key-digest (keys r)) (ops rhs (steps r)) (proof-id rhs) (opening-id rhs))
    ≡ just opened-r
  prepare-r = prepare-forward src w bound-r (imm 1ᶠ) (key-digest (keys r)) (ops rhs (steps r))
    (proof-id rhs) (opening-id rhs) true (instance-fields (rc ∷ []) (fields (steps r) c m b))
    raw-r (keys r) open-r active
    (resolve-child rhs (CircuitState.mem bound-r) (steps r) c m b rc
      (resolve-carried-fields rhs opened-l rc) refl refl refl)
    refl (resolve-right (keys l) (keys r) separated) parsed-r prepared-r (inj₁ refl)

  path : Trace src w first (map lower (IrSource.instructions src)) final
  path = next (publish-step src w (steps (join l r)) c a m b lc rc)
    (next (encode-step lhs src w after-publish lc refl (encode-agrees lhs c a m b lc rc full-instance slots lc))
      (next refl
        (next prepare-l
          (next (encode-step rhs src w opened-l rc refl (encode-agrees rhs c a m b lc rc full-instance slots rc))
            (next refl
              (next prepare-r
                (next (fold-forward src w opened-r fold-ops folded open-l lc (open-r ∷ rc ∷ []) f
                  refl folded-ok (inj₁ refl))
                  (next refl end))))))))

  satisfied : satisfies src w final
  satisfied
    rewrite validate-source keys (join l r) separated | trace→run path =
    guard-pass (full-public-inputsᶜ final ≟LFr full-instance) refl (just final)
