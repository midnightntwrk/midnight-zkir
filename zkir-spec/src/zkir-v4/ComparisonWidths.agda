{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.ComparisonWidths (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Syntax ⋯
open import zkir-v4.Circuit ⋯ using (CircuitWitness; CircuitState; even4; check-circuit)
open import zkir-v4.CircuitBridge ⋯ using (view)
open import zkir-v4.CircuitEffects ⋯ using (PreparationForward)
open import zkir-v4.CircuitProof ⋯ using (honest-witness)
open import zkir-v4.Producer ⋯ using (Producer)
open import zkir-v4.ProducerCorrespondence ⋯ using (producer-forward)
open import zkir-v4.ProducerForward ⋯ using (ForwardDomains)
open import zkir-v4.Protocol ⋯ using (module Verification; exposures)
import zkir-v4.ProtocolProperties ⋯ as Completeness
open import zkir-v4.Semantics ⋯ using (preprocess; State)
open import zkir-v4.SemanticsProperties ⋯ using (AcceptedRun; preprocess-inversion)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Bool.ListAction using (all)
open import Data.List using (List; [])
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≤_; _≤ᵇ_; _≤?_; _+_; _%_)
open import Data.Nat.DivMod using (m%n<n)
open import Data.Nat.Properties using
  (+-mono-≤; ≤-pred; ⊔-lub; ≤-trans; m≤m+n; m⊔n≤o⇒m≤o; ≤∧≢⇒<; n≮n)
open import Data.Product using (∃)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (from-yes)

-- RC1 passes even4 n to a native gadget with a maximum width of 253.
comparison-fits? : ℕ → Bool
comparison-fits? n = even4 n ≤ᵇ 253

requested⇒gadget : ∀ n → n ≤ 252 → even4 n ≤ 253
requested⇒gadget n bound =
  ⊔-lub (+-mono-≤ bound (≤-pred (m%n<n n 2))) (from-yes (4 ≤? 253))

gadget⇒requested : ∀ n → even4 n ≤ 253 → n ≤ 252
gadget⇒requested n fits = ≤-pred (≤∧≢⇒< at-most-253 (λ { refl → n≮n 253 fits }))
  where
  at-most-253 : n ≤ 253
  at-most-253 = ≤-trans (m≤m+n n (n % 2)) (m⊔n≤o⇒m≤o (n + n % 2) 4 fits)

width-252 : comparison-fits? 252 ≡ true
width-252 = refl

width-253 : comparison-fits? 253 ≡ false
width-253 = refl

width-254 : comparison-fits? 254 ≡ false
width-254 = refl

comparison-widths? : IrSource → Bool
comparison-widths? src = all fits? (IrSource.instructions src)
  where
  fits? : Instruction → Bool
  fits? (less-than _ _ n _) = comparison-fits? n
  fits? _ = true

-- This specialization adds only the release gadget's static width check.
check-with-comparison-cap : IrSource → CircuitWitness → Maybe CircuitState
check-with-comparison-cap src w =
  if comparison-widths? src then check-circuit src w else nothing

forward-with-comparison-cap : ∀ src p final → PreparationForward → Producer src
  → comparison-widths? src ≡ true → (ran : preprocess src p ≡ just final)
  → ForwardDomains (AcceptedRun.trace (preprocess-inversion {src} {p} ran))
  → check-with-comparison-cap src (honest-witness p final) ≡ just (view final [])
forward-with-comparison-cap src p final prepare producer widths ran domains
  rewrite widths = producer-forward src p final prepare producer ran domains

module ForKey (src : IrSource) (OuterOK : List Byte → List Fr → Set) where
  open Verification OuterOK using (Accepts; PairingOK; proof)
  module Backend = Completeness.Backend.ForCircuit OuterOK check-with-comparison-cap

  complete-with-comparison-cap : ∀ p final → PreparationForward → Producer src
    → comparison-widths? src ≡ true → Backend.FromCircuit src
    → (ran : preprocess src p ≡ just final)
    → ForwardDomains (AcceptedRun.trace (preprocess-inversion {src} {p} ran))
    → All PairingOK (State.exposed final)
    → ∃ λ raw → Accepts (exposures (IrSource.instructions src))
                        (proof raw (State.exposed final)) (State.pis final)
  complete-with-comparison-cap p final prepare producer widths backend ran domains =
    Backend.prover-complete {src} {p} {final} backend ran
      (forward-with-comparison-cap src p final prepare producer widths ran domains)
