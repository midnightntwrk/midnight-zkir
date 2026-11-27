{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.SegmentCompleteness (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.CircuitEffects ⋯ using (PreparationLaws)
open import zkir-v4.Protocol ⋯ using (instance-fields; KeyArity; module Verification)
open import zkir-v4.ProtocolProperties ⋯ using (module Backend)
open import zkir-v4.RecursiveVerification ⋯ using (Valid; module Active)
open import zkir-v4.SegmentClaims ⋯
open import zkir-v4.SegmentJoinWitness ⋯ as Join using ()
open import zkir-v4.SegmentLeaf ⋯ using (idle-witness; tick-witness)
open import zkir-v4.SegmentSource ⋯
open import zkir-v4.SegmentStatic ⋯ using (KeysSeparated; producer)
open import Data.Bool using (true)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All as All using (All)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; _≤_; _<_; _+_)
open import Data.Nat.Properties using (<-≤-trans)
open import Data.Product using (∃; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst; cong; cong₂)

module Proving (limit : ℕ) (keys ledger-keys : Shape → List Byte)
  (Direct Ledger : List Byte → List Fr → List Byte → Set)
  (tables : ∀ t → height t ≤ limit → KeysSeparated keys t)
  (chip : PreparationLaws)
  (arity : KeyArity)
  (schemas : InnerSchema arity keys limit)
  (laws : InnerLaws arity keys limit Direct) where

  open Family limit keys ledger-keys Direct Ledger
  open Claim
  open App

  record Backends : Set where
    field
      inner : ∀ t → height t ≤ limit → Backend.FromCircuit (λ raw pi → Direct (keys t) pi raw) (source keys t)
      root  : ∀ t → height t ≤ limit → Backend.FromCircuit (λ raw pi → Ledger (ledger-keys t) pi raw) (source keys t)
      parsed : ∀ t → height t ≤ limit → key-well-formed (keys t) ≡ true
      neutral : Valid trivial-accumulator
      fold-four : ∀ a b d e → Valid a → Valid b → Valid d → Valid e →
        ∃ λ f → fold-accumulators (a ∷ b ∷ d ∷ e ∷ []) ≡ just f × Valid f

  module Honest (backends : Backends) where
    open Backends backends

    private
      record PreparedChild (q : Claim) : Set where
        field
          carry opening : Accumulator
          raw : List Byte
          prepared : prepare-circuit (key q) (instance-fields (carry ∷ []) (statement q)) raw true ≡ just opening
          opening-valid : Valid opening
          carry-valid : Valid carry

      prepare-child : ∀ q → height (shape q) < limit → InnerAccepted q → PreparedChild q
      prepare-child q below (Verification.proof raw as , ok)
        with trans (Verification.Accepts.count-matches ok) (source-count keys (shape q))
           | Verification.Accepts.outer-valid ok | Verification.Accepts.pairings ok
      ... | count-ok | valid | pairs with as | count-ok | valid | pairs
      ...   | a ∷ [] | refl | verifies | va All.∷ All.[]
        with Active.direct-to-circuit (laws (shape q) below (context q) (start q) (finish q) a
               (trans (schemas (shape q) below) (cong just (sym
                 (segment-instance-width (shape q) a (context q) (start q) (finish q)))))) chip
               (parsed (shape q) (within q)) raw verifies
      ...     | opening , prepared , good = record
        { carry = a ; opening = opening ; raw = raw ; prepared = prepared ; opening-valid = good ; carry-valid = va }

      build : Complete.BuildNode
      build (unchanged {c = c} {a}) All.[] with idle-witness keys c a trivial-accumulator
      ... | w , final , sat , fields-ok , accs-ok , _ = record
        { witness = w ; final = final ; checked = sat ; publishes = fields-ok
        ; pairings = subst (All Valid) (sym accs-ok) (neutral All.∷ All.[]) }
      build (increased {c = c} {a}) All.[] with tick-witness keys c a trivial-accumulator
      ... | w , final , sat , fields-ok , accs-ok , _ = record
        { witness = w ; final = final ; checked = sat ; publishes = fields-ok
        ; pairings = subst (All Valid) (sym accs-ok) (neutral All.∷ All.[]) }
      build (joined {l} {r} {h} {c} {a} {b} m) (lp All.∷ rp All.∷ All.[])
        with prepare-child (seg l (left-bound l r h) c a m) (<-≤-trans (below-left l r) h) lp
           | prepare-child (seg r (right-bound l r h) c m b) (<-≤-trans (below-right l r) h) rp
      ... | left | right with fold-four L.opening L.carry R.opening R.carry
            L.opening-valid L.carry-valid R.opening-valid R.carry-valid
        where
        module L = PreparedChild left
        module R = PreparedChild right
      ...   | f , folded-ok , vf with Join.build keys l r c a m b L.carry R.carry L.raw R.raw L.opening R.opening f
              (tables (join l r) h) (parsed l (left-bound l r h)) (parsed r (right-bound l r h))
              L.prepared R.prepared folded-ok
        where
        module L = PreparedChild left
        module R = PreparedChild right
      ...     | w , final , sat , fields-ok , accs-ok = record
        { witness = w ; final = final ; checked = sat ; publishes = fields-ok
        ; pairings = subst (All Valid) (sym accs-ok) (vf All.∷ All.[]) }

    module Tree = Complete.Honest (λ q → producer keys (shape q) (tables (shape q) (within q))) build
      (λ q → inner (shape q) (within q)) (λ q → root (shape q) (within q))

    segment-complete : ∀ t h c {a b} → Execution (steps t) a b → RootAccepted (seg t h c a b)
    segment-complete t h c run = Tree.tree-complete (execution-derivation t h c run)

    initialized-complete : ∀ t h c {b} → Execution (steps t) c b → Initialized t h c b
    initialized-complete t h c run = segment-complete t h c run

    -- Each child can be proved on its own.  Only the join uses both proofs.
    join-complete : ∀ l r h c a m b →
      InnerAccepted (seg l (left-bound l r h) c a m) → InnerAccepted (seg r (right-bound l r h) c m b) →
      RootAccepted (seg (join l r) h c a b)
    join-complete l r h c a m b left right =
      Tree.root-parent (joined {l} {r} {h} {c} {a} {b} m) (left All.∷ right All.∷ All.[])

    SplitProofs : ∀ l r → height (join l r) ≤ limit → Fr → Fr → Fr → Set
    SplitProofs l r h c a b = ∃ λ m → InnerAccepted (seg l (left-bound l r h) c a m) ×
      InnerAccepted (seg r (right-bound l r h) c m b) × RootAccepted (seg (join l r) h c a b)

    split-complete : ∀ l r h c {a b} → Execution (steps (join l r)) a b → SplitProofs l r h c a b
    split-complete l r h c run with split (steps l) (steps r) run
    ... | m , before , after = m , left , right , join-complete l r h c _ m _ left right
      where
      left  = Tree.inner-complete (execution-derivation l (left-bound l r h) c before)
      right = Tree.inner-complete (execution-derivation r (right-bound l r h) c after)

    split-at : ∀ i j h c {a b} → Execution (i + j) a b →
      SplitProofs (linear i) (linear j) h c a b
    split-at i j h c {a} {b} run = split-complete (linear i) (linear j) h c
      (subst (λ n → Execution n a b) (sym (cong₂ _+_ (steps-linear i) (steps-linear j))) run)
