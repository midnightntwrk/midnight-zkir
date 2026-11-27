{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.TreeSoundness (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.AccumulatorObligations ⋯ using (BadFold)
open import zkir-v4.Circuit ⋯ using (CircuitState; CircuitWitness; lower; satisfies)
open import zkir-v4.CircuitEffects ⋯ using (PreparationLaws)
open import zkir-v4.CircuitProperties ⋯ using (SatisfiedRun; Trace; satisfying-run)
open import zkir-v4.EncodingProperties ⋯ using (EncodingLaws)
open import zkir-v4.Producer ⋯ using (Producer)
open import zkir-v4.ProducerCorrespondence ⋯ using (module ForKey)
open import zkir-v4.ProofTree ⋯ using (module Application; module Binding)
open import zkir-v4.Protocol ⋯ using (instance-fields; instance-width; KeyArity; KeySchema; MatchesKey; module Verification)
open import zkir-v4.RecursiveVerification ⋯ using (DirectLaws; Valid)
open import zkir-v4.Syntax ⋯ using (IrSource)
open import zkir-v4.TreeTrace ⋯ using (ChildLink; TraceValidity; trace-sound-or-bad-fold; recover-child)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; length; map)
open import Data.List.Relation.Unary.All as All using (All)
open import Data.Maybe using (just)
open import Data.Nat using (_+_; _*_)
open import Data.Product using (∃; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Induction.WellFounded using (Acc; acc; WellFounded)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst; trans)
open import Relation.Nullary using (¬_)

module Soundness
  (Claim : Set) (Rule : Claim → List Claim → Set)
  (source : Claim → IrSource) (statement : Claim → List Fr)
  (inner-key : Claim → List Byte)
  (Direct : List Byte → List Fr → List Byte → Set)
  (RootOK : Claim → List Byte → List Fr → Set)
  (ChildOf : Claim → Claim → Set) where

  open Application Claim Rule source statement inner-key Direct RootOK

  code = λ c → IrSource.instructions (source c)

  -- The statement and full child instance are fixed by the claim and
  -- by the carried values that appear in the parent's actual execution.
  record RequiredChild (parent : Claim) {w start final}
    (path : Trace (source parent) w start (map lower (code parent)) final)
    (child : Claim) : Set where
    field
      carried : List Accumulator
      count-matches : length carried ≡ count child
      link : ChildLink {is = code parent} path (inner-key child)
        (instance-fields carried (statement child)) carried
      smaller : ChildOf child parent

  child-fields : ∀ {parent w start final path child} →
    RequiredChild parent {w} {start} {final} path child → List Fr
  child-fields {child = child} edge = instance-fields (RequiredChild.carried edge) (statement child)

  child-width : ∀ {parent w start final path child}
    (edge : RequiredChild parent {w} {start} {final} path child) →
    length (child-fields edge) ≡ count child * 12 + length (statement child)
  child-width {child = child} edge = trans (instance-width (RequiredChild.carried edge) (statement child))
    (cong (λ n → n * 12 + length (statement child)) (RequiredChild.count-matches edge))

  ChildSchema : KeyArity → Set
  ChildSchema arity = ∀ {parent w start final path child} →
    RequiredChild parent {w} {start} {final} path child →
    KeySchema arity (inner-key child) (count child) (length (statement child))

  ChildLaws : KeyArity → Set
  ChildLaws arity = ∀ {parent w start final path child}
    (edge : RequiredChild parent {w} {start} {final} path child) →
    MatchesKey arity (inner-key child) (child-fields edge) → DirectLaws Direct (inner-key child) (child-fields edge)

  record ObservedRule (c : Claim) {w start final}
    (path : Trace (source c) w start (map lower (code c)) final) : Set where
    field
      children : List Claim
      rule : Rule c children
      required : All (RequiredChild c path) children

  -- The application identifies just one rule from an extracted run and
  -- its bound public statement.  Witness data can determine the children.
  Observe : Set
  Observe = ∀ c w final (sat : satisfies (source c) w final) →
    CircuitState.pis final ≡ statement c →
    ObservedRule c (SatisfiedRun.path (satisfying-run (source c) w final sat))

  data Verifier : Set where
    ledger inner : Verifier

  Verifies : Verifier → Claim → List Byte → List Fr → Set
  Verifies ledger c = RootOK c
  Verifies inner c raw pi = Direct (inner-key c) pi raw

  module At (v : Verifier) (c : Claim) where
    open Verification (Verifies v c) public
    open Binding (source c) (Verifies v c) public

  -- Retain the exact accepted proof and the execution extracted for it.
  record AcceptedRun (v : Verifier) (c : Claim) : Set where
    module Current = At v c
    field
      proof : Current.Proof
      accepted : Current.Accepts (count c) proof (statement c)
      execution : Current.BoundRun (Current.Proof.carried proof) (statement c)
    open Current.BoundRun execution public
    carried = Current.Proof.carried proof
    pairings = Current.Accepts.pairings accepted
    path = SatisfiedRun.path run

  -- Select a particular required link in the rule's ordered child list.
  data Selected {parent w start final}
    {path : Trace (source parent) w start (map lower (code parent)) final}
    {child : Claim} (edge : RequiredChild parent path child) :
    ∀ {cs} → All (RequiredChild parent path) cs → Set where
    first : ∀ {cs} {rest : All (RequiredChild parent path) cs} →
      Selected edge (edge All.∷ rest)
    later : ∀ {c cs} {head : RequiredChild parent path c} {rest : All (RequiredChild parent path) cs} →
      Selected edge rest → Selected edge (head All.∷ rest)

  -- Each descent records a required link and the accepted child for its
  -- full instance.  The terminal event belongs to the terminal run.
  data ReachedBadFold {v c} (node : AcceptedRun v c) : Set where
    at-node : BadFold (code c) (AcceptedRun.path node) → ReachedBadFold node
    in-child : (observed : ObservedRule c (AcceptedRun.path node)) →
      ∀ {child} (edge : RequiredChild c (AcceptedRun.path node) child) →
      Selected edge (ObservedRule.required observed) →
      (next : AcceptedRun inner child) →
      AcceptedRun.carried next ≡ RequiredChild.carried edge →
      ReachedBadFold next → ReachedBadFold node

  NoBadFold : Set
  NoBadFold = ∀ {v c} (node : AcceptedRun v c) →
    ¬ BadFold (code c) (AcceptedRun.path node)

  private
    exclude-reached-fold : NoBadFold → ∀ {v c} {node : AcceptedRun v c} → ReachedBadFold node → ⊥
    exclude-reached-fold no-bad {node = node} (at-node bad) = no-bad node bad
    exclude-reached-fold no-bad (in-child _ _ _ _ _ bad) = exclude-reached-fold no-bad bad

  module Prove
    (well-founded : WellFounded ChildOf)
    (codecs : EncodingLaws) (chip : PreparationLaws)
    (producer : ∀ c → Producer (source c))
    (extract : ∀ v c → ForKey.ExtractsWitness (source c) (Verifies v c))
    (arity : KeyArity)
    (key-schema : ChildSchema arity)
    (direct-laws : ChildLaws arity)
    (observe : Observe) where

    private
      extract-run : ∀ v c (pr : At.Proof v c) →
        At.Accepts v c (count c) pr (statement c) → AcceptedRun v c
      extract-run v c pr ok = record
        { proof = pr ; accepted = ok
        ; execution = At.bind-execution v c codecs (producer c) (extract v c) pr (statement c) ok }

      recover-run : ∀ {v c child} (node : AcceptedRun v c) →
        TraceValidity {is = code c} (AcceptedRun.path node) →
        (edge : RequiredChild c (AcceptedRun.path node) child) →
        ∃ λ (next : AcceptedRun inner child) →
          AcceptedRun.carried next ≡ RequiredChild.carried edge
      recover-run {c = c} {child} node good edge
        with recover-child {is = code c} {path = AcceptedRun.path node}
          chip (direct-laws edge (trans (key-schema edge) (cong just (sym (child-width edge)))))
          good (RequiredChild.link edge)
      ... | (raw , valid) , pairs =
        extract-run inner child (Inner.proof raw (RequiredChild.carried edge)) record
          { count-matches = RequiredChild.count-matches edge
          ; outer-valid = valid ; pairings = pairs } , refl

      accepted-children : ∀ {v c cs} (node : AcceptedRun v c) →
        TraceValidity {is = code c} (AcceptedRun.path node) →
        All (RequiredChild c (AcceptedRun.path node)) cs → All InnerAccepted cs
      accepted-children node good All.[] = All.[]
      accepted-children node good (edge All.∷ rest) with recover-run node good edge
      ... | child , _ = (AcceptedRun.proof child , AcceptedRun.accepted child) All.∷
        accepted-children node good rest

      ChildFailure : ∀ {v c cs} (node : AcceptedRun v c) →
        All (RequiredChild c (AcceptedRun.path node)) cs → Set
      ChildFailure {c = c} node links = ∃ λ child →
        ∃ λ (edge : RequiredChild c (AcceptedRun.path node) child) →
        Selected edge links ×
        (∃ λ (next : AcceptedRun inner child) →
          AcceptedRun.carried next ≡ RequiredChild.carried edge × ReachedBadFold next)

      walk-children : ∀ {v c cs} (node : AcceptedRun v c) →
        TraceValidity {is = code c} (AcceptedRun.path node) →
        (links : All (RequiredChild c (AcceptedRun.path node)) cs) →
        (∀ child → ChildOf child c → (next : AcceptedRun inner child) →
          Derivation child ⊎ ReachedBadFold next) →
        Derivations cs ⊎ ChildFailure node links
      walk-children node good All.[] descend = inj₁ no-children
      walk-children node good (edge All.∷ rest) descend with recover-run node good edge
      ... | next , same with descend _ (RequiredChild.smaller edge) next
      ...   | inj₂ bad = inj₂ (_ , edge , first , next , same , bad)
      ...   | inj₁ tree with walk-children node good rest descend
      ...     | inj₁ trees = inj₁ (tree ∷ᵈ trees)
      ...     | inj₂ (child , link , selected , reached) = inj₂ (child , link , later selected , reached)

      walk : ∀ {v c} → Acc ChildOf c → (node : AcceptedRun v c) →
        Derivation c ⊎ ReachedBadFold node
      walk {v} {c} (acc smaller) node
        with trace-sound-or-bad-fold (source c) witness final (producer c) run final-good
        where
        open AcceptedRun node
        final-good : All Valid (CircuitState.accs final)
        final-good = subst (All Valid) (sym same-carried) pairings
      ... | inj₂ bad = inj₂ (at-node bad)
      ... | inj₁ good with observe c witness final satisfied same-statement
        where open AcceptedRun node
      ...   | observed with walk-children node good (ObservedRule.required observed)
          (λ child below next → walk (smaller below) next)
      ...     | inj₁ trees = inj₁ (derive (ObservedRule.rule observed) trees)
      ...     | inj₂ (child , edge , selected , next , same , bad) =
        inj₂ (in-child observed edge selected next same bad)

    RootFailure : ∀ c (pr : Root.Proof c) → Root.Accepts c (count c) pr (statement c) → Set
    RootFailure c pr ok = ReachedBadFold (extract-run ledger c pr ok)

    -- Retain the accepted child proofs when a caller needs the split itself.
    accepted-children-or-bad-fold : ∀ c (pr : Root.Proof c) (ok : Root.Accepts c (count c) pr (statement c)) →
      (∃ λ cs → Rule c cs × All InnerAccepted cs) ⊎ RootFailure c pr ok
    accepted-children-or-bad-fold c pr ok
      with trace-sound-or-bad-fold (source c) witness final (producer c) run
             (subst (All Valid) (sym same-carried) pairings)
      where open AcceptedRun (extract-run ledger c pr ok)
    ... | inj₂ bad = inj₂ (at-node bad)
    ... | inj₁ good with observe c witness final satisfied same-statement
      where open AcceptedRun (extract-run ledger c pr ok)
    ...   | result = inj₁ (ObservedRule.children result , ObservedRule.rule result ,
                           accepted-children (extract-run ledger c pr ok) good (ObservedRule.required result))

    sound-or-bad-fold : ∀ c (pr : Root.Proof c) (ok : Root.Accepts c (count c) pr (statement c)) →
      Derivation c ⊎ ReachedBadFold (extract-run ledger c pr ok)
    sound-or-bad-fold c pr ok = walk (well-founded c) (extract-run ledger c pr ok)

    tree-sound : NoBadFold → ∀ c (pr : Root.Proof c) →
      Root.Accepts c (count c) pr (statement c) → Derivation c
    tree-sound no-bad c pr ok with sound-or-bad-fold c pr ok
    ... | inj₁ derivation = derivation
    ... | inj₂ bad = ⊥-elim (exclude-reached-fold no-bad bad)
