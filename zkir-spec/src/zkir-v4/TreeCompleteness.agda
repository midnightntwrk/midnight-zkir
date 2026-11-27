{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.TreeCompleteness (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.AccumulatorVerification ⋯ using (circuit-exposure-count)
open import zkir-v4.Circuit ⋯ using (CircuitWitness; CircuitState; satisfies)
open import zkir-v4.CircuitProperties ⋯ using (satisfying-public-inputs; satisfying-run)
open import zkir-v4.Producer ⋯ using (Producer)
open import zkir-v4.ProofTree ⋯ using (module Application)
open import zkir-v4.Protocol ⋯ using (instance-fields; module Verification)
open import zkir-v4.ProtocolProperties ⋯ using (module Backend)
open import zkir-v4.RecursiveVerification ⋯ using (Valid)
open import zkir-v4.Syntax ⋯ using (IrSource)

open import Data.List using (List)
open import Data.List.Relation.Unary.All as All using (All)
open import Data.Product using (∃; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; subst; sym; trans)

module Completeness
  (Claim : Set)
  (Rule : Claim → List Claim → Set)
  (source : Claim → IrSource)
  (statement : Claim → List Fr)
  (inner-key : Claim → List Byte)
  (Direct : List Byte → List Fr → List Byte → Set)
  (RootOK : Claim → List Byte → List Fr → Set)
  where

  open Application Claim Rule source statement inner-key Direct RootOK

  InnerOK : Claim → List Byte → List Fr → Set
  InnerOK c raw pi = Direct (inner-key c) pi raw

  record LocalWitness (c : Claim) : Set where
    field
      witness : CircuitWitness
      final : CircuitState
      checked : satisfies (source c) witness final
      publishes : CircuitState.pis final ≡ statement c
      pairings : All Valid (CircuitState.accs final)

  -- Each constructed node supplies its own producer, backend and witness
  -- construction for the rule's ordered list of accepted children.
  record NodeBuilder {c cs} (rule : Rule c cs) (OuterOK : List Byte → List Fr → Set) : Set where
    field
      producer : Producer (source c)
      backend : Backend.FromCircuit OuterOK (source c)
      build : All InnerAccepted cs → LocalWitness c

  private
    prove-node : ∀ {c} (OuterOK : List Byte → List Fr → Set) →
      Producer (source c) → Backend.FromCircuit OuterOK (source c) → LocalWitness c →
      ∃ λ pr → Verification.Accepts OuterOK (count c) pr (statement c)
    prove-node {c} OuterOK producer backend node with backend witness final checked
      where open LocalWitness node
    ... | raw , outer = Verification.proof raw (CircuitState.accs final) , record
      { count-matches = circuit-exposure-count (source c) witness final
          producer (satisfying-run (source c) witness final checked)
      ; outer-valid = subst (OuterOK raw) instance-bound outer
      ; pairings = pairings
      }
      where
      open LocalWitness node

      instance-bound : CircuitWitness.full-pis witness ≡ instance-fields (CircuitState.accs final) (statement c)
      instance-bound = trans (sym (satisfying-public-inputs {src = source c} {w = witness} checked))
        (cong (instance-fields (CircuitState.accs final)) publishes)

    prove-parent : ∀ {c cs OuterOK} {rule : Rule c cs} →
      NodeBuilder rule OuterOK → All InnerAccepted cs →
      ∃ λ pr → Verification.Accepts OuterOK (count c) pr (statement c)
    prove-parent {OuterOK = OuterOK} builder children =
      prove-node OuterOK producer backend (build children)
      where open NodeBuilder builder

  data PartialTree (c : Claim) : Set where
    reuse-inner : InnerAccepted c → PartialTree c
    build-inner : ∀ {cs} (rule : Rule c cs) →
      NodeBuilder rule (InnerOK c) → All PartialTree cs → PartialTree c

  data PartialRoot (c : Claim) : Set where
    reuse-root : RootAccepted c → PartialRoot c
    build-root : ∀ {cs} (rule : Rule c cs) →
      NodeBuilder rule (RootOK c) → All PartialTree cs → PartialRoot c

  mutual
    grafted-inner-complete : ∀ {c} → PartialTree c → InnerAccepted c
    grafted-inner-complete (reuse-inner accepted) = accepted
    grafted-inner-complete (build-inner rule builder children) = prove-parent builder (grafted-children-complete children)

    grafted-children-complete : ∀ {cs} → All PartialTree cs → All InnerAccepted cs
    grafted-children-complete All.[] = All.[]
    grafted-children-complete (child All.∷ rest) = grafted-inner-complete child All.∷ grafted-children-complete rest

  grafted-tree-complete : ∀ {c} → PartialRoot c → RootAccepted c
  grafted-tree-complete (reuse-root accepted) = accepted
  grafted-tree-complete (build-root rule builder children) = prove-parent builder (grafted-children-complete children)

  BuildNode : Set
  BuildNode = ∀ {c cs} → Rule c cs → All InnerAccepted cs → LocalWitness c

  module Honest
    (producer : ∀ c → Producer (source c))
    (build : BuildNode)
    (inner-backend : ∀ c → Backend.FromCircuit (InnerOK c) (source c))
    (root-backend : ∀ c → Backend.FromCircuit (RootOK c) (source c))
    where

    private
      node-builder : ∀ {c cs OuterOK} (rule : Rule c cs) →
        Backend.FromCircuit OuterOK (source c) → NodeBuilder rule OuterOK
      node-builder {c} rule backend = record
        { producer = producer c
        ; backend = backend
        ; build = build rule
        }

      mutual
        inner-plan : ∀ {c} → Derivation c → PartialTree c
        inner-plan {c} (derive rule children) = build-inner rule (node-builder rule (inner-backend c)) (child-plans children)

        child-plans : ∀ {cs} → Derivations cs → All PartialTree cs
        child-plans no-children = All.[]
        child-plans (child ∷ᵈ rest) = inner-plan child All.∷ child-plans rest

    -- These constructors also allow any already accepted inner proof to
    -- serve as a child of a newly constructed parent.
    inner-parent : ∀ {c cs} → Rule c cs → All InnerAccepted cs → InnerAccepted c
    inner-parent {c} rule = prove-parent (node-builder rule (inner-backend c))

    root-parent : ∀ {c cs} → Rule c cs → All InnerAccepted cs → RootAccepted c
    root-parent {c} rule = prove-parent (node-builder rule (root-backend c))

    inner-complete : ∀ {c} → Derivation c → InnerAccepted c
    inner-complete derivation = grafted-inner-complete (inner-plan derivation)

    children-complete : ∀ {cs} → Derivations cs → All InnerAccepted cs
    children-complete derivations = grafted-children-complete (child-plans derivations)

    tree-complete : ∀ {c} → Derivation c → RootAccepted c
    tree-complete (derive rule children) = root-parent rule (children-complete children)
