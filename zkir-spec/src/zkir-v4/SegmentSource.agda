{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.SegmentSource (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Operations ⋯ using (_≟B_)
open import zkir-v4.Protocol ⋯ using (exposures; instance-fields; instance-width)
open import zkir-v4.SequentialSource ⋯ using (fields-width)
open import zkir-v4.SequentialSource ⋯ public using (fields; observed-fields; key-digest; iterate)
open import zkir-v4.Syntax ⋯
open import zkir-v4.Types ⋯ using (native; accumulator)
open import Data.Bool using (false)
open import Data.List using (List; []; _∷_; _++_; map; length; replicate)
open import Data.List.Properties using (length-replicate)
open import Data.Nat using (ℕ; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import Relation.Nullary using (yes; no)

data Shape : Set where
  idle tick : Shape
  join : Shape → Shape → Shape

steps : Shape → ℕ
steps idle = 0
steps tick = 1
steps (join l r) = steps l + steps r

segment-instance-width : ∀ t a ctx start finish →
  length (instance-fields (a ∷ []) (fields (steps t) ctx start finish)) ≡ 16 + steps t
segment-instance-width t a ctx start finish = trans (instance-width (a ∷ []) (fields (steps t) ctx start finish))
  (cong (12 +_) (fields-width (steps t) ctx start finish))

data Side : Set where
  lhs rhs : Side

ctx x mid z folded : Identifier
ctx = "%ctx"
x = "%x"
mid = "%mid"
z = "%z"
folded = "%folded"

carry-id proof-id opening-id from-id to-id : Side → Identifier
carry-id lhs = "%left"
carry-id rhs = "%right"
proof-id lhs = "%left-proof"
proof-id rhs = "%right-proof"
opening-id lhs = "%left-opening"
opening-id rhs = "%right-opening"
from-id lhs = x
from-id rhs = mid
to-id lhs = mid
to-id rhs = z

limbs : Side → List Identifier
limbs lhs = "%l0" ∷ "%l1" ∷ "%l2" ∷ "%l3" ∷ "%l4" ∷ "%l5" ∷
            "%l6" ∷ "%l7" ∷ "%l8" ∷ "%l9" ∷ "%l10" ∷ "%l11" ∷ []
limbs rhs = "%r0" ∷ "%r1" ∷ "%r2" ∷ "%r3" ∷ "%r4" ∷ "%r5" ∷
            "%r6" ∷ "%r7" ∷ "%r8" ∷ "%r9" ∷ "%r10" ∷ "%r11" ∷ []

statement-operands : ℕ → Identifier → Identifier → List Operand
statement-operands n a b = var ctx ∷ var a ∷ var b ∷ replicate n (imm 0ᶠ)

ops : Side → ℕ → List Operand
ops s n = map var (limbs s) ++ (imm 0ᶠ ∷ statement-operands n (from-id s) (to-id s))

ops-width : ∀ s n → length (ops s n) ≡ 16 + n
ops-width lhs n = cong (16 +_) (length-replicate n)
ops-width rhs n = cong (16 +_) (length-replicate n)

publish : ℕ → Identifier → Instruction
publish n end-id = impact (imm 1ᶠ) (statement-operands n x end-id)

fold-ops : List Operand
fold-ops = var (opening-id lhs) ∷ var (carry-id lhs) ∷ var (opening-id rhs) ∷ var (carry-id rhs) ∷ []

leaf-inputs join-inputs : List TypedIdentifier
leaf-inputs = ctx ⦂ native ∷ x ⦂ native ∷ carry-id lhs ⦂ accumulator ∷ []
join-inputs = ctx ⦂ native ∷ x ⦂ native ∷ mid ⦂ native ∷ z ⦂ native ∷
              carry-id lhs ⦂ accumulator ∷ carry-id rhs ⦂ accumulator ∷ []

key-table : List Byte → List Byte → List (List Byte)
key-table k h with k ≟B h
... | yes _ = k ∷ []
... | no _ = k ∷ h ∷ []

child-code : Side → ℕ → List Byte → List Instruction
child-code s n key = encode (var (carry-id s)) (limbs s) ∷ inner-proof (imm 1ᶠ) (proof-id s) ∷
  prepare-verification (imm 1ᶠ) (key-digest key) (ops s n) (proof-id s) (opening-id s) ∷ []

source : (Shape → List Byte) → Shape → IrSource
source keys idle = mk-ir-source V0 leaf-inputs [] false
  (publish 0 x ∷ verify-accumulator (var (carry-id lhs)) ∷ []) []
source keys tick = mk-ir-source V0 leaf-inputs [] false
  (add (var x) (imm 1ᶠ) z ∷ publish 1 z ∷ verify-accumulator (var (carry-id lhs)) ∷ []) []
source keys (join l r) = mk-ir-source V0 join-inputs [] false
  (publish (steps l + steps r) z ∷
   child-code lhs (steps l) (keys l) ++ child-code rhs (steps r) (keys r) ++
   (accumulate fold-ops folded ∷ verify-accumulator (var folded) ∷ []))
  (key-table (keys l) (keys r))

source-count : ∀ keys t → exposures (IrSource.instructions (source keys t)) ≡ 1
source-count keys idle = refl
source-count keys tick = refl
source-count keys (join l r) = refl
