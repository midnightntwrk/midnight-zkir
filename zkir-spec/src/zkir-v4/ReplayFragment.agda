{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.ReplayFragment (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Types ⋯
open import zkir-v4.Syntax ⋯
open import zkir-v4.Circuit ⋯
open import zkir-v4.Operations ⋯ using (eval-guard)
open import zkir-v4.ReverseShape ⋯ using (immediate-true; slot-always-active)
open import zkir-v4.ProducerResiduals ⋯ using (Unchecked; unchecked-read-active)
open import Data.Bool using (true)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (_<_; _^_)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

data ActiveGuard : Maybe Operand → Set where
  unguarded : ActiveGuard nothing
  always : ActiveGuard (just (imm 1ᶠ))

private
  active : ∀ st {g} → ActiveGuard g → eval-guard (CircuitState.mem st) g ≡ just true
  active st unguarded = refl
  active st always = immediate-true st

-- These premises mention only the source and its primitive implementations.
-- A comparison at an exact circuit width needs no range hypothesis on cells.
Static : Instruction → Set
Static (assert a) = a ≡ imm 1ᶠ
Static (less-than _ _ n _) = even4 n ≡ n
Static (public-input g t _) = ActiveGuard g
Static (private-input g t _) = ActiveGuard g
Static (inner-proof g _) = g ≡ imm 1ᶠ
Static (persistent-hash a _ _) = ∀ vs → persistent-hash-circuit-fn a vs ≡ persistent-hash-fn a vs
Static (keccak256 a _ _) = ∀ vs → keccak-circuit-fn a vs ≡ keccak-fn a vs
Static (sha512 a _ _) = ∀ vs → sha512-circuit-fn a vs ≡ sha512-fn a vs
Static _ = ⊤

private
  local : ∀ w i → Static i → ∀ st → Unchecked w st i
  local w (encode _ _) ok st = tt
  local w (assert .(imm 1ᶠ)) refl st _ refl _ = refl
  local w (cond-select _ _ _ _) ok st = tt
  local w (constrain-bits _ _) ok st = ok
  local w (constrain-eq _ _) ok st = tt
  local w (constrain-to-boolean _) ok st = tt
  local w (copy _ _) ok st = tt
  local w (impact _ _) ok st = tt
  local w (ec-mul _ _ _) ok st = tt
  local w (ec-mul-generator _ _) ok st = tt
  local w (hash-to-curve _ _) ok st = tt
  local w (into-coordinates _ _) ok st = tt
  local w (from-coordinates _ _) ok st = tt
  local w (into-bytes32 _ _) ok st = tt
  local w (from-bytes32 _ _ _) ok st = tt
  local w (reverse-bytes _ _) ok st = tt
  local w (bytes32-into-low-high _ _) ok st = tt
  local w (bytes32-from-low-high (_ , _) _) ok st = tt
  local w (div-mod-power-of-two _ _ _) ok st = ok
  local w (reconstitute-field _ _ _ _) ok st = ok
  local w (transient-hash _ _) ok st = tt
  local w (persistent-hash _ _ _) law st vs _ = law vs
  local w (keccak256 _ _ _) law st vs _ = law vs
  local w (test-eq _ _ _) ok st = tt
  local w (add _ _ _) ok st = tt
  local w (mul _ _ _) ok st = tt
  local w (neg _ _) ok st = tt
  local w (inv _ _) ok st = tt
  local w (not _ _) ok st = tt
  local w (less-than a b n o) exact st = λ x y _ _ bx by →
    subst (λ k → valFr x < 2 ^ k) exact bx , subst (λ k → valFr y < 2 ^ k) exact by
  local w (jubjub-scalar-from-native _ _) ok st = tt
  local w (public-input g t id) guard st = unchecked-read-active w st g t id (active st guard)
  local w (private-input g t id) guard st = unchecked-read-active w st g t id (active st guard)
  local w (circuit-output _) ok st = tt
  local w (slice _ _ _ _) ok st = tt
  local w (nth _ _ _) ok st = tt
  local w (concat _ _) ok st = tt
  local w (reverse _ _) ok st = tt
  local w (load-constant _ _ _) ok st = tt
  local w (sha512 _ _ _) law st vs _ = law vs
  local w (and _ _) ok st = tt
  local w (or _ _) ok st = tt
  local w (xor _ _) ok st = tt
  local w (to-bytes _ _) ok st = tt
  local w (from-bytes _ _ _) ok st = tt
  local w (bytes-into-natives _ _) ok st = tt
  local w (bytes-from-natives _ _ _) ok st = tt
  local w (inner-proof .(imm 1ᶠ) id) refl st = slot-always-active st (imm 1ᶠ) (immediate-true st)
  local w (prepare-verification _ _ _ _ _) ok st = tt
  local w (accumulate _ _) ok st = tt
  local w (verify-accumulator _) ok st = tt

Fragment : IrSource → Set
Fragment src = All Static (IrSource.instructions src)

source-residuals : ∀ w {is} → All Static is → All (λ i → ∀ st → Unchecked w st i) is
source-residuals w [] = []
source-residuals w (_∷_ {x = i} head tail) = local w i head ∷ source-residuals w tail
