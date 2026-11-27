{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.SequentialVerification (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.CircuitEffects ⋯ using (PreparationLaws)
open import zkir-v4.Protocol ⋯ using (instance-fields; KeyArity; KeySchema; MatchesKey; instance-matches-key; module Verification)
open import zkir-v4.RecursiveVerification ⋯ using (DirectLaws; module Nested; Valid)

open import Data.Bool using (true)
open import Data.Bool.Properties using (T?)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; _∷_; length)
open import Data.List.Relation.Unary.All as All using (All)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.Nat.Properties using (≤-refl; m≤n⇒m≤1+n; ≤-trans; n≤1+n)
open import Data.Product using (∃; _×_; _,_; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Relation.Nullary using (¬_; yes; no)

record Claim (Program Context State : Set) : Set where
  constructor claim
  field
    program : Program
    context : Context
    start finish : State
    steps : ℕ

-- The caller selects the program, context, keys and accumulator counts.
-- Only levels within the configured depth require verifier laws.
module Chain
  {Program Context State : Set}
  (program : Program)
  (context : Context)
  (Initial : Program → Context → State → Set)
  (Step : Program → Context → State → State → Set)
  (encode : Claim Program Context State → List Fr)
  (encode-injective : ∀ {s t} → encode s ≡ encode t → s ≡ t)
  (Direct Ledger : List Byte → List Fr → List Byte → Set)
  (chip : PreparationLaws)
  (inner-key ledger-key : ℕ → List Byte)
  (inner-count ledger-count : ℕ → ℕ)
  (limit : ℕ)
  (parsed : ∀ n → n ≤ limit → key-well-formed (inner-key n) ≡ true)
  (arity : KeyArity)
  (key-schema : ∀ n → suc n ≤ limit → ∀ start previous → KeySchema arity (inner-key n) (inner-count n)
    (length (encode (claim program context start previous n))))
  (direct-laws : ∀ n → suc n ≤ limit → ∀ start previous carried →
    length carried ≡ inner-count n →
    let pi = instance-fields carried (encode (claim program context start previous n)) in
    MatchesKey arity (inner-key n) pi → DirectLaws Direct (inner-key n) pi)
  (Carries : List Accumulator → List Accumulator → Set)
  where

  module Inner (n : ℕ) = Verification (λ raw pi → Direct (inner-key n) pi raw)
  module Root (n : ℕ) = Verification (λ raw pi → Ledger (ledger-key n) pi raw)
  module Deferred (n : ℕ) (within : n ≤ limit) = Nested Direct chip (inner-key n) (parsed n within)

  statement : ℕ → State → State → List Fr
  statement n start finish = encode (claim program context start finish n)

  data Execution : ℕ → State → State → Set where
    begin : ∀ {start} → Initial program context start → Execution zero start start
    extend : ∀ {n start previous finish} →
      Execution n start previous → Step program context previous finish → Execution (suc n) start finish

  -- A single circuit exposes its predecessor's opening obligation together
  -- with the predecessor's carried obligations. Carries describes that
  -- exposure, for example by listing the obligations or folding them.
  data Layer (carried : List Accumulator) : Claim Program Context State → Set where
    base : ∀ {p c start} → Initial p c start → Layer carried (claim p c start start zero)
    advance : ∀ {p c start previous finish n} →
      Step p c previous finish →
      ∀ {raw child-carried opening} →
      length child-carried ≡ inner-count n →
      prepare-circuit (inner-key n) (instance-fields child-carried (encode (claim p c start previous n)))
        raw true ≡ just opening →
      Carries carried (opening ∷ child-carried) →
      Layer carried (claim p c start finish (suc n))

  -- A failure occurs at one observed successor layer whose carried values
  -- pass their checks, although its predecessor's obligations fail.
  record BadCarry : Set where
    field
      predecessor-level : ℕ
      predecessor-within : predecessor-level ≤ limit
      start previous finish : State
      raw : List Byte
      carried child-carried : List Accumulator
      opening : Accumulator
      transition : Step program context previous finish
      count : length child-carried ≡ inner-count predecessor-level
      prepared : prepare-circuit (inner-key predecessor-level)
        (instance-fields child-carried (statement predecessor-level start previous)) raw true ≡ just opening
      exposed : Carries carried (opening ∷ child-carried)
      checked : All Valid carried
      invalid : ¬ All Valid (opening ∷ child-carried)

  failed-layer : (bad : BadCarry) → Layer (BadCarry.carried bad)
    (claim program context (BadCarry.start bad) (BadCarry.finish bad) (suc (BadCarry.predecessor-level bad)))
  failed-layer bad = advance {previous = previous} transition {raw} {child-carried} {opening} count prepared exposed
    where open BadCarry bad

  CheckCarried : Set
  CheckCarried = ∀ {as bs} → Carries as bs → All Valid as → All Valid bs

  -- Each backend only has to identify one layer from a proof for its key.
  -- The observation binds the public suffix and uses the actual carried list.
  Local : (List Byte → List Fr → List Byte → Set) →
    (ℕ → List Byte) → (ℕ → ℕ) → Set
  Local Verifies key count =
    ∀ requested → Claim.steps requested ≤ limit → ∀ raw carried →
      length carried ≡ count (Claim.steps requested) →
      Verifies (key (Claim.steps requested)) (instance-fields carried (encode requested)) raw →
      ∃ λ observed → encode observed ≡ encode requested × Layer carried observed

  module Soundness
    (extract-inner : Local Direct inner-key inner-count)
    (extract-root : Local Ledger ledger-key ledger-count)
    where

    opaque
      observed-layer : ∀ {Verifies key count} → Local Verifies key count → ∀ n → n ≤ limit → ∀ start finish pr →
        Verification.Accepts (λ raw pi → Verifies (key n) pi raw) (count n) pr (statement n start finish) →
        Layer (Verification.Proof.carried pr) (claim program context start finish n)
      observed-layer extract n within start finish pr ok
        with extract (claim program context start finish n) within (Verification.Proof.raw pr)
             (Verification.Proof.carried pr) (Verification.Accepts.count-matches ok) (Verification.Accepts.outer-valid ok)
      ... | observed , fields , layer = subst (Layer _) (encode-injective fields) layer

    inner-layer = observed-layer {Direct} {inner-key} {inner-count} extract-inner
    root-layer = observed-layer {Ledger} {ledger-key} {ledger-count} extract-root

    -- A path starts at the layer extracted from the supplied proof.  Each
    -- descent keeps the accepted proof for the predecessor's full instance.
    data Reaches (bad : BadCarry) : ∀ {n start finish carried} →
      Layer carried (claim program context start finish n) → Set where
      here : Reaches bad (failed-layer bad)
      in-predecessor : ∀ {n start previous finish carried raw child-carried opening}
        {step : Step program context previous finish}
        {count : length child-carried ≡ inner-count n}
        {prepared : prepare-circuit (inner-key n) (instance-fields child-carried (statement n start previous))
                      raw true ≡ just opening}
        {exposed : Carries carried (opening ∷ child-carried)} →
        All Valid (opening ∷ child-carried) →
        (within : n ≤ limit) (direct-raw : List Byte)
        (ok : Inner.Accepts n (inner-count n) (Inner.proof direct-raw child-carried) (statement n start previous)) →
        Reaches bad (inner-layer n within start previous (Inner.proof direct-raw child-carried) ok) →
        Reaches bad (advance {previous = previous} step {raw} {child-carried} {opening} count prepared exposed)

    reached-level : ∀ {bad n start finish carried} {layer : Layer carried (claim program context start finish n)} →
      Reaches bad layer → suc (BadCarry.predecessor-level bad) ≤ n
    reached-level here = ≤-refl
    reached-level (in-predecessor _ _ _ _ path) = m≤n⇒m≤1+n (reached-level path)

    private
      base-execution : ∀ {start finish carried} → Layer carried (claim program context start finish zero) →
        Execution zero start finish
      base-execution (base initial) = begin initial

      recover : ∀ n → suc n ≤ limit → ∀ start previous {raw carried opening} →
        length carried ≡ inner-count n →
        prepare-circuit (inner-key n) (instance-fields carried (statement n start previous))
          raw true ≡ just opening →
        All Valid (opening ∷ carried) →
        ∃ λ direct-raw →
          Inner.Accepts n (inner-count n) (Inner.proof direct-raw carried) (statement n start previous)
      recover n within start previous {carried = carried} count prepared checked =
        Deferred.deferred-to-direct n predecessor-within
          (direct-laws n within start previous carried count
            (instance-matches-key arity (inner-key n) carried (statement n start previous)
              (key-schema n within start previous) count refl))
          (Deferred.deferred count _ prepared checked)
        where predecessor-within = ≤-trans (n≤1+n n) within

      extend-or-fail : ∀ n → suc n ≤ limit → ∀ start finish {carried}
        (layer : Layer carried (claim program context start finish (suc n))) →
        All Valid carried →
        ((within : n ≤ limit) → ∀ previous pr (ok : Inner.Accepts n (inner-count n) pr (statement n start previous)) →
          Execution n start previous ⊎ (∃ λ bad → Reaches bad (inner-layer n within start previous pr ok))) →
        Execution (suc n) start finish ⊎ (∃ λ bad → Reaches bad layer)
      extend-or-fail n within start finish {carried}
        (advance {previous = previous} step {raw} {child-carried} {opening} count prepared exposed)
        checked continue
        with All.all? (λ a → T? (pairing-valid a)) (opening ∷ child-carried)
      ... | no invalid = inj₂ (record
        { predecessor-level = n
        ; predecessor-within = ≤-trans (n≤1+n n) within
        ; start = start
        ; previous = previous
        ; finish = finish
        ; raw = raw
        ; carried = carried
        ; child-carried = child-carried
        ; opening = opening
        ; transition = step
        ; count = count
        ; prepared = prepared
        ; exposed = exposed
        ; checked = checked
        ; invalid = invalid } , here)
      ... | yes valid with recover n within start previous count prepared valid
      ...   | direct-raw , previous-ok with continue (≤-trans (n≤1+n n) within) previous (Inner.proof direct-raw child-carried) previous-ok
      ...     | inj₁ prefix = inj₁ (extend prefix step)
      ...     | inj₂ (bad , path) =
        inj₂ (bad , in-predecessor valid (≤-trans (n≤1+n n) within) direct-raw previous-ok path)

    inner-sound-or-reached : ∀ n (within : n ≤ limit) start finish pr
      (ok : Inner.Accepts n (inner-count n) pr (statement n start finish)) →
      Execution n start finish ⊎ (∃ λ bad → Reaches bad (inner-layer n within start finish pr ok))
    inner-sound-or-reached zero within start finish pr ok =
      inj₁ (base-execution (inner-layer zero within start finish pr ok))
    inner-sound-or-reached (suc n) within start finish pr ok =
      extend-or-fail n within start finish
        (inner-layer (suc n) within start finish pr ok) (Inner.Accepts.pairings {n = suc n} ok)
        (λ predecessor-within → inner-sound-or-reached n predecessor-within start)

    -- The root uses the ledger verifier. Only its predecessor goes through
    -- the deferred-to-direct conversion for the inner transcript.
    sound-or-reached : ∀ n (within : n ≤ limit) start finish pr
      (ok : Root.Accepts n (ledger-count n) pr (statement n start finish)) →
      Execution n start finish ⊎ (∃ λ bad → Reaches bad (root-layer n within start finish pr ok))
    sound-or-reached zero within start finish pr ok =
      inj₁ (base-execution (root-layer zero within start finish pr ok))
    sound-or-reached (suc n) within start finish pr ok =
      extend-or-fail n within start finish
        (root-layer (suc n) within start finish pr ok) (Root.Accepts.pairings {n = suc n} ok)
        (λ predecessor-within → inner-sound-or-reached n predecessor-within start)

    inner-sound-or-bad-carry : ∀ n → n ≤ limit → ∀ start finish pr →
      Inner.Accepts n (inner-count n) pr (statement n start finish) → Execution n start finish ⊎ BadCarry
    inner-sound-or-bad-carry n within start finish pr ok =
      Data.Sum.map₂ proj₁ (inner-sound-or-reached n within start finish pr ok)

    sound-or-bad-carry : ∀ n → n ≤ limit → ∀ start finish pr →
      Root.Accepts n (ledger-count n) pr (statement n start finish) → Execution n start finish ⊎ BadCarry
    sound-or-bad-carry n within start finish pr ok =
      Data.Sum.map₂ proj₁ (sound-or-reached n within start finish pr ok)

    private
      exclude-failure : ∀ {n start finish} → CheckCarried →
        Execution n start finish ⊎ BadCarry → Execution n start finish
      exclude-failure check (inj₁ execution) = execution
      exclude-failure check (inj₂ bad) =
        ⊥-elim (BadCarry.invalid bad (check (BadCarry.exposed bad) (BadCarry.checked bad)))

    inner-sound : CheckCarried → ∀ n → n ≤ limit → ∀ start finish pr →
      Inner.Accepts n (inner-count n) pr (statement n start finish) →
      Execution n start finish
    inner-sound check n within start finish pr ok =
      exclude-failure check (inner-sound-or-bad-carry n within start finish pr ok)

    sound : CheckCarried → ∀ n → n ≤ limit → ∀ start finish pr →
      Root.Accepts n (ledger-count n) pr (statement n start finish) →
      Execution n start finish
    sound check n within start finish pr ok =
      exclude-failure check (sound-or-bad-carry n within start finish pr ok)
