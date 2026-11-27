{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.SegmentSoundness (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Circuit ⋯ using (lower)
open import zkir-v4.CircuitProperties ⋯ using (Trace)
open import zkir-v4.CircuitEffects ⋯ using (PreparationLaws)
open import zkir-v4.EncodingProperties ⋯ using (EncodingLaws)
open import zkir-v4.ProducerCorrespondence ⋯ using (module ForKey)
open import zkir-v4.Protocol ⋯ using (instance-fields; KeyArity)
open import zkir-v4.SegmentClaims ⋯
open import zkir-v4.SegmentJoinObserve ⋯ using (observe-join)
open import zkir-v4.SegmentLeaf ⋯ using (idle-observe; tick-observe)
open import zkir-v4.SegmentSource ⋯
open import zkir-v4.SegmentStatic ⋯ using (KeysSeparated; producer; resolve-left; resolve-right)
open import zkir-v4.SequentialSource ⋯ using (fields-width)

open import zkir-v4.Syntax ⋯ using (IrSource)
open import zkir-v4.TreeTrace ⋯ using (ChildLink)

open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All as All using (All)
open import Data.Nat using (ℕ; _≤_)
open import Data.Nat.Properties using (<-≤-trans)
open import Data.Product using (∃; _×_; _,_)
open import Data.Sum as Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (refl; sym; subst; trans)

module Checking (limit : ℕ) (keys ledger-keys : Shape → List Byte)
  (Direct Ledger : List Byte → List Fr → List Byte → Set)
  (tables : ∀ t → height t ≤ limit → KeysSeparated keys t)
  (chip : PreparationLaws)
  (arity : KeyArity)
  (schemas : InnerSchema arity keys limit)
  (laws : InnerLaws arity keys limit Direct) where

  open Family limit keys ledger-keys Direct Ledger
  open Claim
  open App

  private
    child-schema : Sound.ChildSchema arity
    child-schema {parent = parent} {child = seg t h c a b} edge
      rewrite source-count keys t | fields-width (steps t) c a b =
      schemas t (<-≤-trans (Sound.RequiredChild.smaller edge) (within parent))

    child-laws : Sound.ChildLaws arity
    child-laws {parent = parent} {child = seg t h c a b} edge
      with Sound.RequiredChild.carried edge | trans (Sound.RequiredChild.count-matches edge) (source-count keys t)
    ... | carry ∷ [] | refl = laws t (<-≤-trans (Sound.RequiredChild.smaller edge) (within parent)) c a b carry

    join-rule : ∀ l r h c a b {w start final} →
      let parent = seg (join l r) h c a b
          code = IrSource.instructions (src parent)
      in (path : Trace (src parent) w start (map lower code) final) →
      (∃ λ m → ∃ λ lc → ∃ λ rc →
        ChildLink {is = code} path (keys l)
          (instance-fields (lc ∷ []) (fields (steps l) c a m)) (lc ∷ []) ×
        ChildLink {is = code} path (keys r)
          (instance-fields (rc ∷ []) (fields (steps r) c m b)) (rc ∷ [])) →
      Sound.ObservedRule parent path
    join-rule l r h c a b path (m , lc , rc , left-link , right-link) = record
      { children = seg l (left-bound l r h) c a m ∷ seg r (right-bound l r h) c m b ∷ []
      ; rule = joined m
      ; required =
          record { carried = lc ∷ []; count-matches = sym (source-count keys l)
                 ; link = left-link; smaller = below-left l r } All.∷
          record { carried = rc ∷ []; count-matches = sym (source-count keys r)
                 ; link = right-link; smaller = below-right l r } All.∷ All.[]
      }

  observe : Sound.Observe
  observe (seg idle h c a b) w final sat statement-ok = record
    { children = []
    ; rule = subst (λ end → Rule (seg idle h c a end) [])
        (sym (idle-observe keys w final c a b sat statement-ok)) unchanged
    ; required = All.[]
    }
  observe (seg tick h c a b) w final sat statement-ok = record
    { children = []
    ; rule = subst (λ end → Rule (seg tick h c a end) [])
        (sym (tick-observe keys w final c a b sat statement-ok)) increased
    ; required = All.[]
    }
  observe (seg (join l r) h c a b) w final sat statement-ok =
    join-rule l r h c a b _
      (observe-join keys l r (resolve-left (keys l) (keys r))
        (resolve-right (keys l) (keys r) (tables (join l r) h)) w final sat c a b statement-ok)

  record Extraction : Set where
    field
      codecs : EncodingLaws
      inner : ∀ t → height t ≤ limit →
        ForKey.ExtractsWitness (source keys t) (λ raw pi → Direct (keys t) pi raw)
      root : ∀ t → height t ≤ limit →
        ForKey.ExtractsWitness (source keys t) (λ raw pi → Ledger (ledger-keys t) pi raw)

  module Verified (extraction : Extraction) where
    open Extraction extraction

    extract : ∀ v q → ForKey.ExtractsWitness (src q) (Sound.Verifies v q)
    extract Sound.ledger q = root (shape q) (within q)
    extract Sound.inner q = inner (shape q) (within q)

    module Tree = Sound.Prove well-founded codecs chip
      (λ q → producer keys (shape q) (tables (shape q) (within q)))
      extract arity child-schema child-laws observe

    execution-or-bad-fold : ∀ t h c a b (pr : Root.Proof (seg t h c a b))
      (ok : Root.Accepts (seg t h c a b) (count (seg t h c a b)) pr (statement (seg t h c a b))) →
      Execution (steps t) a b ⊎ Tree.RootFailure (seg t h c a b) pr ok
    execution-or-bad-fold t h c a b pr ok =
      Sum.map derivation-execution (λ bad → bad) (Tree.sound-or-bad-fold (seg t h c a b) pr ok)

    execution-sound : Sound.NoBadFold → ∀ t h c a b (pr : Root.Proof (seg t h c a b)) →
      Root.Accepts (seg t h c a b) (count (seg t h c a b)) pr (statement (seg t h c a b)) →
      Execution (steps t) a b
    execution-sound no-bad t h c a b pr ok =
      derivation-execution (Tree.tree-sound no-bad (seg t h c a b) pr ok)

    initialized-sound : Sound.NoBadFold → ∀ t h c b → Initialized t h c b → Execution (steps t) c b
    initialized-sound no-bad t h c b (pr , ok) = execution-sound no-bad t h c c b pr ok

    private
      split-children : ∀ l r h c a b →
        (∃ λ cs → Rule (seg (join l r) h c a b) cs × All InnerAccepted cs) →
        ∃ λ m → InnerAccepted (seg l (left-bound l r h) c a m) ×
                InnerAccepted (seg r (right-bound l r h) c m b)
      split-children l r h c a b (_ , joined m , left All.∷ right All.∷ All.[]) =
        m , left , right

    accepted-split-or-bad-fold : ∀ l r h c a b (pr : Root.Proof (seg (join l r) h c a b))
      (ok : Root.Accepts (seg (join l r) h c a b) (count (seg (join l r) h c a b)) pr
        (statement (seg (join l r) h c a b))) →
      (∃ λ m → InnerAccepted (seg l (left-bound l r h) c a m) ×
               InnerAccepted (seg r (right-bound l r h) c m b)) ⊎
      Tree.RootFailure (seg (join l r) h c a b) pr ok
    accepted-split-or-bad-fold l r h c a b pr ok =
      Sum.map (split-children l r h c a b) (λ bad → bad)
        (Tree.accepted-children-or-bad-fold (seg (join l r) h c a b) pr ok)
