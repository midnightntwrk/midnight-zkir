{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.ProducerAlgebra (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Types ⋯
open import zkir-v4.Syntax ⋯
open import zkir-v4.Operations ⋯
open import zkir-v4.Producer ⋯
open import zkir-v4.ProducerStore ⋯ using (StoreTyped; writes-types)
open import zkir-v4.ProducerValuesHelpers ⋯
open import Data.Bool using (_∨_) renaming (not to bnot)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

module Algebra (sig : List IrType) (Γ : Env) (m : Mem) (store : StoreTyped Γ m) where

  private
    copy-result : ∀ x o v {ws} → resolve m x ≡ just v → compute m (copy x o) ≡ just ws
      → writes-types ws ≡ (o ⦂ typeof v) ∷ []
    copy-result x o v@(val-native _) seen ok rewrite seen = write-type o v refl ok
    copy-result x o v@(val-bytes _) seen ok rewrite seen = write-type o v refl ok
    copy-result x o v@(val-byte _) seen ok rewrite seen = write-type o v refl ok
    copy-result x o v@(val-bool _) seen ok rewrite seen = write-type o v refl ok
    copy-result x o (val-accumulator v) seen ok rewrite seen with () ← ok
    copy-result x o v@(val-jubjub-point _) seen ok rewrite seen = write-type o v refl ok
    copy-result x o v@(val-jubjub-scalar _) seen ok rewrite seen = write-type o v refl ok
    copy-result x o v@(val-secp256k1-point _) seen ok rewrite seen = write-type o v refl ok
    copy-result x o v@(val-secp256k1-base _) seen ok rewrite seen = write-type o v refl ok
    copy-result x o v@(val-secp256k1-scalar _) seen ok rewrite seen = write-type o v refl ok
    copy-result x o v@(val-secp256r1-point _) seen ok rewrite seen = write-type o v refl ok
    copy-result x o v@(val-secp256r1-base _) seen ok rewrite seen = write-type o v refl ok
    copy-result x o v@(val-secp256r1-scalar _) seen ok rewrite seen = write-type o v refl ok
    copy-result x o v@(val-curve25519-point _) seen ok rewrite seen = write-type o v refl ok
    copy-result x o v@(val-curve25519-base _) seen ok rewrite seen = write-type o v refl ok
    copy-result x o v@(val-curve25519-scalar _) seen ok rewrite seen = write-type o v refl ok

  copy-types : ∀ x o → Rule sig Γ m (copy x o)
  copy-types x o declared computed with unary-output sig Γ m (λ t → bnot (equal t accumulator)) x o store declared
  ... | v , seen , bound = trans (copy-result x o v seen computed) bound

  private
    neg-result : ∀ x o v {ws} → resolve m x ≡ just v → compute m (neg x o) ≡ just ws
      → writes-types ws ≡ (o ⦂ typeof v) ∷ []
    neg-result x o (val-native v) seen ok rewrite seen = write-type o _ refl ok
    neg-result x o (val-bytes v) seen ok rewrite seen with () ← ok
    neg-result x o (val-byte v) seen ok rewrite seen with () ← ok
    neg-result x o (val-bool v) seen ok rewrite seen = write-type o _ refl ok
    neg-result x o (val-accumulator v) seen ok rewrite seen with () ← ok
    neg-result x o (val-jubjub-point v) seen ok rewrite seen = write-type o _ refl ok
    neg-result x o (val-jubjub-scalar v) seen ok rewrite seen = write-type o _ refl ok
    neg-result x o (val-secp256k1-point v) seen ok rewrite seen = write-type o _ refl ok
    neg-result x o (val-secp256k1-base v) seen ok rewrite seen = write-type o _ refl ok
    neg-result x o (val-secp256k1-scalar v) seen ok rewrite seen = write-type o _ refl ok
    neg-result x o (val-secp256r1-point v) seen ok rewrite seen = write-type o _ refl ok
    neg-result x o (val-secp256r1-base v) seen ok rewrite seen = write-type o _ refl ok
    neg-result x o (val-secp256r1-scalar v) seen ok rewrite seen = write-type o _ refl ok
    neg-result x o (val-curve25519-point v) seen ok rewrite seen = write-type o _ refl ok
    neg-result x o (val-curve25519-base v) seen ok rewrite seen = write-type o _ refl ok
    neg-result x o (val-curve25519-scalar v) seen ok rewrite seen = write-type o _ refl ok

  neg-types : ∀ x o → Rule sig Γ m (neg x o)
  neg-types x o declared computed with unary-output sig Γ m (λ t → arithmetic t ∨ equal t bool) x o store declared
  ... | v , seen , bound = trans (neg-result x o v seen computed) bound

  private
    inv-result : ∀ x o v {ws} → resolve m x ≡ just v → compute m (inv x o) ≡ just ws
      → writes-types ws ≡ (o ⦂ typeof v) ∷ []
    inv-result x o (val-native v) seen ok rewrite seen
      with mapped-bind-success (invᶠ v) val-native (write o) ok
    ... | result , _ , written = write-type o (val-native result) refl written
    inv-result x o (val-bytes v) seen ok rewrite seen with () ← ok
    inv-result x o (val-byte v) seen ok rewrite seen with () ← ok
    inv-result x o (val-bool v) seen ok rewrite seen with () ← ok
    inv-result x o (val-accumulator v) seen ok rewrite seen with () ← ok
    inv-result x o (val-jubjub-point v) seen ok rewrite seen with () ← ok
    inv-result x o (val-jubjub-scalar v) seen ok rewrite seen
      with mapped-bind-success (invJˢ v) val-jubjub-scalar (write o) ok
    ... | result , _ , written = write-type o (val-jubjub-scalar result) refl written
    inv-result x o (val-secp256k1-point v) seen ok rewrite seen with () ← ok
    inv-result x o (val-secp256k1-base v) seen ok rewrite seen
      with mapped-bind-success (invK1ᵇ v) val-secp256k1-base (write o) ok
    ... | result , _ , written = write-type o (val-secp256k1-base result) refl written
    inv-result x o (val-secp256k1-scalar v) seen ok rewrite seen
      with mapped-bind-success (invK1ˢ v) val-secp256k1-scalar (write o) ok
    ... | result , _ , written = write-type o (val-secp256k1-scalar result) refl written
    inv-result x o (val-secp256r1-point v) seen ok rewrite seen with () ← ok
    inv-result x o (val-secp256r1-base v) seen ok rewrite seen
      with mapped-bind-success (invPᵇ v) val-secp256r1-base (write o) ok
    ... | result , _ , written = write-type o (val-secp256r1-base result) refl written
    inv-result x o (val-secp256r1-scalar v) seen ok rewrite seen
      with mapped-bind-success (invPˢ v) val-secp256r1-scalar (write o) ok
    ... | result , _ , written = write-type o (val-secp256r1-scalar result) refl written
    inv-result x o (val-curve25519-point v) seen ok rewrite seen with () ← ok
    inv-result x o (val-curve25519-base v) seen ok rewrite seen
      with mapped-bind-success (invCᵇ v) val-curve25519-base (write o) ok
    ... | result , _ , written = write-type o (val-curve25519-base result) refl written
    inv-result x o (val-curve25519-scalar v) seen ok rewrite seen
      with mapped-bind-success (invCˢ v) val-curve25519-scalar (write o) ok
    ... | result , _ , written = write-type o (val-curve25519-scalar result) refl written

  inv-types : ∀ x o → Rule sig Γ m (inv x o)
  inv-types x o declared computed with unary-output sig Γ m field-type x o store declared
  ... | v , seen , bound = trans (inv-result x o v seen computed) bound

  private
    add-result : ∀ a b o x y {ws} → typeof y ≡ typeof x
      → resolve m a ≡ just x → resolve m b ≡ just y → compute m (add a b o) ≡ just ws
      → writes-types ws ≡ (o ⦂ typeof x) ∷ []
    add-result a b o (val-native x) (val-native y) _ seen-a seen-b ok rewrite seen-a | seen-b = write-type o _ refl ok
    add-result a b o (val-bytes x) (val-bytes y) _ seen-a seen-b ok rewrite seen-a | seen-b with () ← ok
    add-result a b o (val-byte x) (val-byte y) _ seen-a seen-b ok rewrite seen-a | seen-b with () ← ok
    add-result a b o (val-bool x) (val-bool y) _ seen-a seen-b ok rewrite seen-a | seen-b with () ← ok
    add-result a b o (val-accumulator x) (val-accumulator y) _ seen-a seen-b ok rewrite seen-a | seen-b with () ← ok
    add-result a b o (val-jubjub-point p) (val-jubjub-point q) _ seen-a seen-b ok rewrite seen-a | seen-b = write-type o _ refl ok
    add-result a b o (val-jubjub-scalar x) (val-jubjub-scalar y) _ seen-a seen-b ok rewrite seen-a | seen-b = write-type o _ refl ok
    add-result a b o (val-secp256k1-point p) (val-secp256k1-point q) _ seen-a seen-b ok rewrite seen-a | seen-b = write-type o _ refl ok
    add-result a b o (val-secp256k1-base x) (val-secp256k1-base y) _ seen-a seen-b ok rewrite seen-a | seen-b = write-type o _ refl ok
    add-result a b o (val-secp256k1-scalar x) (val-secp256k1-scalar y) _ seen-a seen-b ok rewrite seen-a | seen-b = write-type o _ refl ok
    add-result a b o (val-secp256r1-point p) (val-secp256r1-point q) _ seen-a seen-b ok rewrite seen-a | seen-b = write-type o _ refl ok
    add-result a b o (val-secp256r1-base x) (val-secp256r1-base y) _ seen-a seen-b ok rewrite seen-a | seen-b = write-type o _ refl ok
    add-result a b o (val-secp256r1-scalar x) (val-secp256r1-scalar y) _ seen-a seen-b ok rewrite seen-a | seen-b = write-type o _ refl ok
    add-result a b o (val-curve25519-point p) (val-curve25519-point q) _ seen-a seen-b ok rewrite seen-a | seen-b = write-type o _ refl ok
    add-result a b o (val-curve25519-base x) (val-curve25519-base y) _ seen-a seen-b ok rewrite seen-a | seen-b = write-type o _ refl ok
    add-result a b o (val-curve25519-scalar x) (val-curve25519-scalar y) _ seen-a seen-b ok rewrite seen-a | seen-b = write-type o _ refl ok

  add-types : ∀ a b o → Rule sig Γ m (add a b o)
  add-types a b o declared computed with binary-output sig Γ m arithmetic a b o store declared
  ... | x , y , seen-a , seen-b , same , bound = trans (add-result a b o x y same seen-a seen-b computed) bound

  private
    mul-result : ∀ a b o x y {ws} → typeof y ≡ typeof x
      → resolve m a ≡ just x → resolve m b ≡ just y → compute m (mul a b o) ≡ just ws
      → writes-types ws ≡ (o ⦂ typeof x) ∷ []
    mul-result a b o (val-native x) (val-native y) _ seen-a seen-b ok rewrite seen-a | seen-b = write-type o _ refl ok
    mul-result a b o (val-bytes x) (val-bytes y) _ seen-a seen-b ok rewrite seen-a | seen-b with () ← ok
    mul-result a b o (val-byte x) (val-byte y) _ seen-a seen-b ok rewrite seen-a | seen-b with () ← ok
    mul-result a b o (val-bool x) (val-bool y) _ seen-a seen-b ok rewrite seen-a | seen-b with () ← ok
    mul-result a b o (val-accumulator x) (val-accumulator y) _ seen-a seen-b ok rewrite seen-a | seen-b with () ← ok
    mul-result a b o (val-jubjub-point p) (val-jubjub-point q) _ seen-a seen-b ok rewrite seen-a | seen-b with () ← ok
    mul-result a b o (val-jubjub-scalar x) (val-jubjub-scalar y) _ seen-a seen-b ok rewrite seen-a | seen-b = write-type o _ refl ok
    mul-result a b o (val-secp256k1-point p) (val-secp256k1-point q) _ seen-a seen-b ok rewrite seen-a | seen-b with () ← ok
    mul-result a b o (val-secp256k1-base x) (val-secp256k1-base y) _ seen-a seen-b ok rewrite seen-a | seen-b = write-type o _ refl ok
    mul-result a b o (val-secp256k1-scalar x) (val-secp256k1-scalar y) _ seen-a seen-b ok rewrite seen-a | seen-b = write-type o _ refl ok
    mul-result a b o (val-secp256r1-point p) (val-secp256r1-point q) _ seen-a seen-b ok rewrite seen-a | seen-b with () ← ok
    mul-result a b o (val-secp256r1-base x) (val-secp256r1-base y) _ seen-a seen-b ok rewrite seen-a | seen-b = write-type o _ refl ok
    mul-result a b o (val-secp256r1-scalar x) (val-secp256r1-scalar y) _ seen-a seen-b ok rewrite seen-a | seen-b = write-type o _ refl ok
    mul-result a b o (val-curve25519-point p) (val-curve25519-point q) _ seen-a seen-b ok rewrite seen-a | seen-b with () ← ok
    mul-result a b o (val-curve25519-base x) (val-curve25519-base y) _ seen-a seen-b ok rewrite seen-a | seen-b = write-type o _ refl ok
    mul-result a b o (val-curve25519-scalar x) (val-curve25519-scalar y) _ seen-a seen-b ok rewrite seen-a | seen-b = write-type o _ refl ok

  mul-types : ∀ a b o → Rule sig Γ m (mul a b o)
  mul-types a b o declared computed with binary-output sig Γ m field-type a b o store declared
  ... | x , y , seen-a , seen-b , same , bound = trans (mul-result a b o x y same seen-a seen-b computed) bound
