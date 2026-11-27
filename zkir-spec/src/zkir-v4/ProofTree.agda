{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.ProofTree (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.AccumulatorVerification ⋯ public using (module Binding)
open import zkir-v4.Protocol ⋯ using (exposures; module Verification)
open import zkir-v4.Syntax ⋯ using (IrSource)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.Product using (∃)

-- A rule states the application fact established at a node given the
-- ordered claims of its children.  For instance, a join can require its
-- left child's final state to equal its right child's initial state.
module Application
  (Claim : Set) (Rule : Claim → List Claim → Set)
  (source : Claim → IrSource) (statement : Claim → List Fr)
  (inner-key : Claim → List Byte)
  (Direct : List Byte → List Fr → List Byte → Set)
  (RootOK : Claim → List Byte → List Fr → Set) where

  module Inner (c : Claim) = Verification (λ raw pi → Direct (inner-key c) pi raw)
  module Root (c : Claim) = Verification (RootOK c)

  count : Claim → ℕ
  count c = exposures (IrSource.instructions (source c))

  InnerAccepted RootAccepted : Claim → Set
  InnerAccepted c = ∃ λ p → Inner.Accepts c (count c) p (statement c)
  RootAccepted c = ∃ λ p → Root.Accepts c (count c) p (statement c)

  infixr 5 _∷ᵈ_
  mutual
    data Derivation (c : Claim) : Set where
      derive : ∀ {cs} → Rule c cs → Derivations cs → Derivation c

    data Derivations : List Claim → Set where
      no-children : Derivations []
      _∷ᵈ_ : ∀ {c cs} → Derivation c → Derivations cs → Derivations (c ∷ cs)
