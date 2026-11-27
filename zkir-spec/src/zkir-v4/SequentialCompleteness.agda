{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.SequentialCompleteness (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.CircuitEffects ⋯ using (Preparation)
open import zkir-v4.Protocol ⋯ using (instance-fields; KeyArity; MatchesKey; module Verification)
open import zkir-v4.ProtocolProperties ⋯ using (module Backend)
open import zkir-v4.RecursiveVerification ⋯ using (FoldComplete; Valid)
open import zkir-v4.SequentialSource ⋯
  using (source; validated; fields; carried-count; iterate; Observation; initial; advanced; observation-count;
         single; batch; InnerSchema; counter-instance-width)
open import zkir-v4.SequentialWitness ⋯ using (build)

open import Data.Bool using (true)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All as All using (All)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.Nat.Properties using (≤-trans; n≤1+n)
open import Data.Product using (∃; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)

module Counter
  (inner-key ledger-key : ℕ → List Byte)
  (Poseidon Blake2b : List Byte → List Fr → List Byte → Set)
  (limit : ℕ)
  (arity : KeyArity)
  where

  module Inner (n : ℕ) = Verification (λ raw pi → Poseidon (inner-key n) pi raw)
  module Ledger (n : ℕ) = Verification (λ raw pi → Blake2b (ledger-key n) pi raw)

  -- Each premise binds the backend and key to the circuit for that exact level.
  -- At successor levels the circuit pins the preceding Poseidon key.
  Builds : (List Byte → List Fr → List Byte → Set) → (ℕ → List Byte) → Set
  Builds verifies key = ∀ n → n ≤ limit →
    Backend.FromCircuit (λ raw pi → verifies (key n) pi raw) (source inner-key n)

  -- Native verification supplies a valid opening for the same proof bytes
  -- and full instance that the successor will supply to circuit preparation.
  DirectPrepares : Set
  DirectPrepares = ∀ n → suc n ≤ limit → ∀ ctx carried →
    length carried ≡ carried-count n →
    let pi = instance-fields carried (fields n ctx ctx (iterate n ctx)) in
    MatchesKey arity (inner-key n) pi → ∀ raw → Poseidon (inner-key n) pi raw →
    prepare-compatible (inner-key n) pi raw true ≡ true ×
    (∃ λ a → prepare-active (inner-key n) pi raw ≡ just a × Valid a)

  Accepted : ℕ → Fr → Fr → Fr → Set
  Accepted n ctx start finish =
    ∃ λ pr → Ledger.Accepts n (carried-count n) pr (fields n ctx start finish)

  module Honest
    (inner-builds : Builds Poseidon inner-key)
    (ledger-builds : Builds Blake2b ledger-key)
    (parsed : ∀ n → n ≤ limit → key-well-formed (inner-key n) ≡ true)
    (schemas : InnerSchema arity inner-key limit)
    (direct-prepares : DirectPrepares)
    (prepare : ∀ key pi raw a → key-well-formed key ≡ true →
      Preparation true key pi raw a → prepare-circuit key pi raw true ≡ just a)
    (folds : FoldComplete)
    where

    private
      predecessor-within : ∀ n → suc n ≤ limit → n ≤ limit
      predecessor-within n = ≤-trans (n≤1+n n)

      predecessor-parsed : ∀ n → n ≤ limit → ∀ {m} → n ≡ suc m → key-well-formed (inner-key m) ≡ true
      predecessor-parsed (suc m) within refl = parsed m (predecessor-within m within)

      Layer : ℕ → Fr → Set
      Layer n ctx = ∃ λ carried →
        Observation inner-key 0ᶠ n (fields n ctx ctx (iterate n ctx)) carried × All Valid carried

      prove : ∀ {verifies key} → Builds verifies key → ∀ n → n ≤ limit → ∀ ctx →
        Layer n ctx →
        ∃ λ pr → Verification.Accepts (λ raw pi → verifies (key n) pi raw)
          (carried-count n) pr (fields n ctx ctx (iterate n ctx))
      prove {verifies} {key} backend n within ctx (carried , seen , valid)
        with build inner-key n (validated inner-key n) (predecessor-parsed n within) seen
      ... | w , final , sat , bound with backend n within w final sat
      ...   | raw , verifies-witness = Verification.proof raw carried , record
        { count-matches = observation-count seen
        ; outer-valid = subst (λ pi → verifies (key n) pi raw) bound verifies-witness
        ; pairings = valid
        }

      next-layer : ∀ n ctx raw child opening →
        length child ≡ carried-count n →
        prepare-circuit (inner-key n) (instance-fields child (fields n ctx ctx (iterate n ctx)))
          raw true ≡ just opening →
        Valid opening → All Valid child → Layer (suc n) ctx
      next-layer zero ctx raw [] opening refl prepared good All.[] =
        opening ∷ [] , advanced ctx ctx ctx raw opening refl prepared single , good All.∷ All.[]
      next-layer (suc n) ctx raw (a ∷ []) opening refl prepared good (child-good All.∷ All.[])
        with folds opening a good child-good
      ... | f , folded , valid =
        f ∷ [] , advanced ctx ctx (iterate (suc n) ctx) raw opening refl prepared (batch folded) ,
        valid All.∷ All.[]

      advance : ∀ n → suc n ≤ limit → ∀ ctx → Layer n ctx → Layer (suc n) ctx
      advance n within ctx layer with prove {Poseidon} {inner-key} inner-builds n (predecessor-within n within) ctx layer
      ... | Inner.proof raw child , accepted with
        direct-prepares n within ctx child (Inner.Accepts.count-matches {n = n} accepted)
          (trans (schemas n within) (cong just (sym (counter-instance-width n ctx ctx (iterate n ctx) child
            (Inner.Accepts.count-matches {n = n} accepted)))))
          raw (Inner.Accepts.outer-valid {n = n} accepted)
      ...   | compatible , opening , native-prepared , good =
        next-layer n ctx raw child opening (Inner.Accepts.count-matches {n = n} accepted)
          (prepare (inner-key n) _ raw opening (parsed n (predecessor-within n within)) (compatible , native-prepared))
          good (Inner.Accepts.pairings {n = n} accepted)

      honest-layer : ∀ n → n ≤ limit → ∀ ctx → Layer n ctx
      honest-layer zero _ ctx = [] , initial ctx , All.[]
      honest-layer (suc n) within ctx =
        advance n within ctx (honest-layer n previous ctx)
        where previous = predecessor-within n within

    counter-complete : ∀ ctx n → n ≤ limit → Accepted n ctx ctx (iterate n ctx)
    counter-complete ctx n within =
      prove {Blake2b} {ledger-key} ledger-builds n within ctx (honest-layer n within ctx)

    complete-from-endpoints : ∀ ctx n → n ≤ limit → ∀ start finish →
      start ≡ ctx → finish ≡ iterate n start → Accepted n ctx start finish
    complete-from-endpoints ctx n within .ctx .(iterate n ctx) refl refl = counter-complete ctx n within
