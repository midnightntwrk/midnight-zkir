{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.SegmentRegroup (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.CircuitEffects ⋯ using (PreparationLaws)
open import zkir-v4.Protocol ⋯ using (KeyArity)
open import zkir-v4.SegmentClaims ⋯ using (Execution; module Family; height; InnerSchema; InnerLaws)
open import zkir-v4.SegmentCompleteness ⋯ using (module Proving)
open import zkir-v4.SegmentSoundness ⋯ using (module Checking)
open import zkir-v4.SegmentSource ⋯ using (Shape; join; steps; fields)
open import zkir-v4.SegmentStatic ⋯ using (KeysSeparated)

open import Data.List using (List)
open import Data.Nat using (ℕ; _≤_)
open import Data.Nat.Properties using (+-assoc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum as Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; subst; sym)

module Regrouping (limit : ℕ) (keys ledger-keys : Shape → List Byte)
  (Direct Ledger : List Byte → List Fr → List Byte → Set)
  (tables : ∀ t → height t ≤ limit → KeysSeparated keys t)
  (chip : PreparationLaws)
  (arity : KeyArity)
  (schemas : InnerSchema arity keys limit)
  (laws : InnerLaws arity keys limit Direct) where

  open Family limit keys ledger-keys Direct Ledger
  open App using (RootAccepted)

  module Prove = Proving limit keys ledger-keys Direct Ledger tables chip arity schemas laws
  module Check = Checking limit keys ledger-keys Direct Ledger tables chip arity schemas laws

  private
    regroup-steps : ∀ l m r → steps (join (join l m) r) ≡ steps (join l (join m r))
    regroup-steps l m r = +-assoc (steps l) (steps m) (steps r)

  same-statement : ∀ l m r h h′ c a b →
    statement (seg (join (join l m) r) h c a b) ≡ statement (seg (join l (join m r)) h′ c a b)
  same-statement l m r h h′ c a b = cong (λ n → fields n c a b) (regroup-steps l m r)

  module Transport (backends : Prove.Backends) (extractors : Check.Extraction) where
    open Prove.Honest backends using (segment-complete)
    open Check.Verified extractors using (module Tree; execution-or-bad-fold)

    private
      reprove : ∀ {n t} h c {a b} → n ≡ steps t →
        Execution n a b → RootAccepted (seg t h c a b)
      reprove h c {a} {b} same run =
        segment-complete _ h c (subst (λ n → Execution n a b) same run)

    -- Re-prove the same public segment under the target shape's ledger key.
    -- A failure is attached to the exact proof accepted under the source key.
    regroup-right : ∀ l m r h h′ c a b
      (input : RootAccepted (seg (join (join l m) r) h c a b)) →
      RootAccepted (seg (join l (join m r)) h′ c a b) ⊎
        Tree.RootFailure (seg (join (join l m) r) h c a b) (proj₁ input) (proj₂ input)
    regroup-right l m r h h′ c a b (pr , ok) =
      Sum.map (reprove h′ c (regroup-steps l m r)) (λ bad → bad)
        (execution-or-bad-fold (join (join l m) r) h c a b pr ok)

    regroup-left : ∀ l m r h h′ c a b
      (input : RootAccepted (seg (join l (join m r)) h′ c a b)) →
      RootAccepted (seg (join (join l m) r) h c a b) ⊎
        Tree.RootFailure (seg (join l (join m r)) h′ c a b) (proj₁ input) (proj₂ input)
    regroup-left l m r h h′ c a b (pr , ok) =
      Sum.map (reprove h c (sym (regroup-steps l m r))) (λ bad → bad)
        (execution-or-bad-fold (join l (join m r)) h′ c a b pr ok)

    regroup-equivalent : Sound.NoBadFold → ∀ l m r h h′ c a b →
      (RootAccepted (seg (join (join l m) r) h c a b) → RootAccepted (seg (join l (join m r)) h′ c a b)) ×
      (RootAccepted (seg (join l (join m r)) h′ c a b) → RootAccepted (seg (join (join l m) r) h c a b))
    regroup-equivalent no-bad l m r h h′ c a b = to-right , to-left
      where
      left = seg (join (join l m) r) h c a b
      right = seg (join l (join m r)) h′ c a b

      to-right : RootAccepted left → RootAccepted right
      to-right (pr , ok) = reprove h′ c (regroup-steps l m r)
        (derivation-execution (Tree.tree-sound no-bad left pr ok))

      to-left : RootAccepted right → RootAccepted left
      to-left (pr , ok) = reprove h c (sym (regroup-steps l m r))
        (derivation-execution (Tree.tree-sound no-bad right pr ok))
