{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.SegmentClaims (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.SegmentSource ⋯
open import zkir-v4.ProofTree ⋯ using (module Application)
open import zkir-v4.Protocol ⋯ using (instance-fields; KeyArity; KeySchema; MatchesKey)
open import zkir-v4.RecursiveVerification ⋯ using (DirectLaws)
open import zkir-v4.TreeSoundness ⋯ using (module Soundness)
open import zkir-v4.TreeCompleteness ⋯ using (module Completeness)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_; _<_; _≤_; s≤s)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m; <⇒≤; ≤-trans)
open import Data.Product using (∃; _×_; _,_)
open import Induction.WellFounded using (WellFounded)
import Relation.Binary.Construct.On as On
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

-- A segment may start at any field value.  Each constructor counts one
-- transition even when the sequence wraps around the native field.
data Execution : ℕ → Fr → Fr → Set where
  stop : ∀ {a} → Execution 0 a a
  increment : ∀ {n a b} → Execution n (a +ᶠ 1ᶠ) b → Execution (suc n) a b

concatenate : ∀ {i j a m b} → Execution i a m → Execution j m b → Execution (i + j) a b
concatenate stop right = right
concatenate (increment left) right = increment (concatenate left right)

split : ∀ i j {a b} → Execution (i + j) a b → ∃ λ m → Execution i a m × Execution j m b
split zero j run = _ , stop , run
split (suc i) j (increment tail) with split i j tail
... | m , left , right = m , increment left , right

height : Shape → ℕ
height idle = 0
height tick = 0
height (join l r) = suc (height l ⊔ height r)

below-left : ∀ l r → height l < height (join l r)
below-left l r = s≤s (m≤m⊔n (height l) (height r))

below-right : ∀ l r → height r < height (join l r)
below-right l r = s≤s (m≤n⊔m (height l) (height r))

InnerSchema : KeyArity → (Shape → List Byte) → ℕ → Set
InnerSchema arity keys limit = ∀ t → height t < limit → KeySchema arity (keys t) 1 (4 + steps t)

InnerLaws : KeyArity → (Shape → List Byte) → ℕ → (List Byte → List Fr → List Byte → Set) → Set
InnerLaws arity keys limit Direct = ∀ t → height t < limit → ∀ ctx start finish carried →
  let pi = instance-fields (carried ∷ []) (fields (steps t) ctx start finish) in
  MatchesKey arity (keys t) pi → DirectLaws Direct (keys t) pi

-- Every natural split has a choice of finite segment shapes, including
-- zero on either side.  The height limit is a property of the chosen keys.
linear : ℕ → Shape
linear zero = idle
linear (suc zero) = tick
linear (suc (suc n)) = join tick (linear (suc n))

steps-linear : ∀ n → steps (linear n) ≡ n
steps-linear zero = refl
steps-linear (suc zero) = refl
steps-linear (suc (suc n)) = cong suc (steps-linear (suc n))

module Bounded (limit : ℕ) where
  record Claim : Set where
    constructor seg
    field
      shape : Shape
      within : height shape ≤ limit
      context start finish : Fr

  left-bound : ∀ l r → height (join l r) ≤ limit → height l ≤ limit
  left-bound l r = ≤-trans (<⇒≤ (below-left l r))

  right-bound : ∀ l r → height (join l r) ≤ limit → height r ≤ limit
  right-bound l r = ≤-trans (<⇒≤ (below-right l r))

  statement : Claim → List Fr
  statement (seg t _ c a b) = fields (steps t) c a b

  data Rule : Claim → List Claim → Set where
    unchanged : ∀ {h c a} → Rule (seg idle h c a a) []
    increased : ∀ {h c a} → Rule (seg tick h c a (a +ᶠ 1ᶠ)) []
    joined : ∀ {l r h c a b} m → Rule (seg (join l r) h c a b)
      (seg l (left-bound l r h) c a m ∷ seg r (right-bound l r h) c m b ∷ [])

  Smaller : Claim → Claim → Set
  Smaller child parent = height (Claim.shape child) < height (Claim.shape parent)

  well-founded : WellFounded Smaller
  well-founded = On.wellFounded (λ c → height (Claim.shape c)) <-wellFounded

module Family (limit : ℕ) (inner-key ledger-key : Shape → List Byte)
  (Direct Ledger : List Byte → List Fr → List Byte → Set) where

  open Bounded limit public
  open Claim

  src = λ c → source inner-key (shape c)
  key = λ c → inner-key (shape c)
  rootOK = λ c raw pi → Ledger (ledger-key (shape c)) pi raw

  module App = Application Claim Rule src statement key Direct rootOK
  module Sound = Soundness Claim Rule src statement key Direct rootOK Smaller
  module Complete = Completeness Claim Rule src statement key Direct rootOK
  open App

  -- The application verifier supplies the context in both public positions
  -- at the root.  Inner segments still admit an arbitrary start.
  Initialized : ∀ t → height t ≤ limit → Fr → Fr → Set
  Initialized t h c b = RootAccepted (seg t h c c b)

  derivation-execution : ∀ {q} → Derivation q →
    Execution (steps (shape q)) (start q) (finish q)
  derivation-execution (derive unchanged no-children) = stop
  derivation-execution (derive increased no-children) = increment stop
  derivation-execution (derive (joined m) (left ∷ᵈ right ∷ᵈ no-children)) =
    concatenate (derivation-execution left) (derivation-execution right)

  execution-derivation : ∀ t h c {a b} → Execution (steps t) a b → Derivation (seg t h c a b)
  execution-derivation idle h c stop = derive unchanged no-children
  execution-derivation tick h c (increment stop) = derive increased no-children
  execution-derivation (join l r) h c run with split (steps l) (steps r) run
  ... | m , left , right = derive (joined m)
    (execution-derivation l _ c left ∷ᵈ execution-derivation r _ c right ∷ᵈ no-children)
