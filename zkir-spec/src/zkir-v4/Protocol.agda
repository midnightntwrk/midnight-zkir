{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.Protocol (⋯ : _) (open Assumptions ⋯) where

open import zkir-v4.Syntax ⋯
open import zkir-v4.Encoding ⋯ using (encode-accumulator)
open import Data.List.Base using (List; []; _∷_; _++_; length; concatMap; take; drop)
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe.Base using (Maybe; just)
open import Data.Nat.Base using (ℕ; _+_; _*_)
open import Data.Bool.Base using (T)
open import Data.List.Properties using (length-++)
open import Data.Vec.Base as V using ()
open import Data.Vec.Properties using (length-toList)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

-- The count is recorded when the outer verifier key is generated.
exposure : Instruction → ℕ
exposure (verify-accumulator _) = 1
exposure _ = 0

exposures : List Instruction → ℕ
exposures [] = 0
exposures (i ∷ is) = exposure i + exposures is

instance-fields : List Accumulator → List Fr → List Fr
instance-fields as statement = concatMap encode-accumulator as ++ statement

accumulator-width : ∀ a → length (encode-accumulator a) ≡ 12
accumulator-width (l , r)
  rewrite length-++ (V.toList (g1-to-fields l)) {1ᶠ ∷ V.toList (g1-to-fields r) ++ (1ᶠ ∷ [])}
        | length-++ (V.toList (g1-to-fields r)) {1ᶠ ∷ []}
        | length-toList (g1-to-fields l) | length-toList (g1-to-fields r) = refl

block-width : ∀ as → length (concatMap encode-accumulator as) ≡ length as * 12
block-width [] = refl
block-width (a ∷ as) rewrite length-++ (encode-accumulator a) {concatMap encode-accumulator as}
                           | accumulator-width a | block-width as = refl

instance-width : ∀ as statement → length (instance-fields as statement) ≡ length as * 12 + length statement
instance-width as statement = trans (length-++ (concatMap encode-accumulator as) {statement})
  (cong (_+ length statement) (block-width as))

-- Processed verification keys are opaque.  The caller supplies their
-- expected public-input arity and binds it to the circuit's schema.
KeyArity : Set
KeyArity = List Byte → Maybe ℕ

KeySchema : KeyArity → List Byte → ℕ → ℕ → Set
KeySchema arity key count statement-width = arity key ≡ just (count * 12 + statement-width)

MatchesKey : KeyArity → List Byte → List Fr → Set
MatchesKey arity key fields = arity key ≡ just (length fields)

instance-matches-key : ∀ arity key as statement {count statement-width} →
  KeySchema arity key count statement-width → length as ≡ count → length statement ≡ statement-width →
  MatchesKey arity key (instance-fields as statement)
instance-matches-key arity key as statement {count} schema count-ok statement-ok = trans schema
  (cong just (sym (trans (instance-width as statement)
    (trans (cong (λ n → n * 12 + length statement) count-ok) (cong ((count * 12) +_) statement-ok)))))

private
  take-prefix : ∀ (xs ys : List Fr) → take (length xs) (xs ++ ys) ≡ xs
  take-prefix [] _ = refl
  take-prefix (x ∷ xs) ys = cong (x ∷_) (take-prefix xs ys)

  drop-prefix : ∀ (xs ys : List Fr) → drop (length xs) (xs ++ ys) ≡ ys
  drop-prefix [] _ = refl
  drop-prefix (_ ∷ xs) ys = drop-prefix xs ys

split-carried : ∀ as stmt → take (length as * 12) (instance-fields as stmt)
                         ≡ concatMap encode-accumulator as
split-carried as stmt rewrite sym (block-width as) = take-prefix _ stmt

split-statement : ∀ as stmt → drop (length as * 12) (instance-fields as stmt) ≡ stmt
split-statement as stmt rewrite sym (block-width as) = drop-prefix (concatMap encode-accumulator as) stmt

-- The opaque verifier consumes the outer proof bytes and the *whole*
-- instance.  The RC ledger backend checks the key's public-input count
-- and requires the instance column to fit the usable domain rows.
-- PairingOK refers to one deferred accumulator for the same
-- verifier parameters.  Neither cryptographic algorithm is formalized here.
module Verification (OuterOK : List Byte → List Fr → Set) where

  PairingOK : Accumulator → Set
  PairingOK a = T (pairing-valid a)

  record Proof : Set where
    constructor proof
    field
      raw : List Byte
      carried : List Accumulator

  record Accepts (key-count : ℕ) (p : Proof) (statement : List Fr) : Set where
    open Proof p
    field
      count-matches : length carried ≡ key-count
      outer-valid   : OuterOK raw (instance-fields carried statement)
      pairings      : All PairingOK carried

  -- A caller obtains protocol completeness from backend completeness
  -- only when every exposed accumulator passes its deferred check.
  complete : ∀ {s raw as stmt}
           → length as ≡ exposures (IrSource.instructions s)
           → OuterOK raw (instance-fields as stmt)
           → All PairingOK as
           → Accepts (exposures (IrSource.instructions s)) (proof raw as) stmt
  complete n outer pairs = record
    { count-matches = n ; outer-valid = outer ; pairings = pairs }

  -- Transport the backend's statement guarantee to the externally
  -- returned suffix while retaining the obligations on the carried prefix.
  sound : ∀ {n p stmt} {Meaning : List Fr → Set}
        → (∀ raw pi → OuterOK raw pi → Meaning pi)
        → Accepts n p stmt
        → Meaning (instance-fields (Proof.carried p) stmt) × All PairingOK (Proof.carried p)
  sound {p = p} {stmt} backend ok =
    backend (Proof.raw p) (instance-fields (Proof.carried p) stmt)
            (Accepts.outer-valid ok) , Accepts.pairings ok
