{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.SegmentStatic (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Operations ⋯ using (_≟B_)
open import zkir-v4.Producer ⋯ using (Env; Producer; expect; check-list)
open import zkir-v4.SegmentSource ⋯
open import zkir-v4.Syntax ⋯ using (_⦂_; imm)
open import zkir-v4.Types ⋯ using (native; accumulator)
open import zkir-v4.Validation ⋯ using (validate; resolve-vk)

open import Data.Bool using (true; false)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _++_; reverse; map; replicate)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Relation.Nullary using (Dec; yes; no; does; ¬_)

-- Only children sharing a table need a collision exclusion premise.
-- Equal keys share one entry and can be referenced twice.
KeysSeparated : (Shape → List Byte) → Shape → Set
KeysSeparated keys idle = ⊤
KeysSeparated keys tick = ⊤
KeysSeparated keys (join l r) = key-digest (keys l) ≡ key-digest (keys r) → keys l ≡ keys r

private
  test-yes : ∀ {P : Set} (d : Dec P) → P → does d ≡ true
  test-yes (yes _) _ = refl
  test-yes (no bad) p = ⊥-elim (bad p)

  test-no : ∀ {P : Set} (d : Dec P) → ¬ P → does d ≡ false
  test-no (yes p) bad = ⊥-elim (bad p)
  test-no (no _) _ = refl

  guard-self : does (1ᶠ ≟ᶠ 1ᶠ) ≡ true
  guard-self = test-yes (1ᶠ ≟ᶠ 1ᶠ) refl

  digest-self : ∀ key → does (key-digest key ≟B key-digest key) ≡ true
  digest-self key = test-yes (key-digest key ≟B key-digest key) refl

  digest-mismatch : ∀ k h →
    (key-digest k ≡ key-digest h → k ≡ h) → ¬ (k ≡ h) →
    does (key-digest k ≟B key-digest h) ≡ false
  digest-mismatch k h separated different =
    test-no (key-digest k ≟B key-digest h) (λ eq → different (separated eq))

  resolve-head : ∀ k ks → resolve-vk (key-digest k) (k ∷ ks) ≡ just k
  resolve-head k ks rewrite digest-self k = refl

resolve-left : ∀ k h → resolve-vk (key-digest k) (key-table k h) ≡ just k
resolve-left k h with k ≟B h
... | yes _ = resolve-head k []
... | no _ = resolve-head k (h ∷ [])

resolve-right : ∀ k h → (key-digest k ≡ key-digest h → k ≡ h) →
  resolve-vk (key-digest h) (key-table k h) ≡ just h
resolve-right k h separated with k ≟B h
... | yes refl = resolve-head k []
... | no different
  rewrite digest-mismatch h k (λ eq → sym (separated (sym eq))) (λ eq → different (sym eq)) =
  resolve-head h []

-- The proof-slot walk reaches each guard test only after consuming the
-- preceding slot, so the rewrites follow that order.
validate-source : ∀ keys t → KeysSeparated keys t → validate (source keys t) ≡ true
validate-source keys idle _ = refl
validate-source keys tick _ = refl
validate-source keys (join l r) separated
  with keys l | keys r | separated
... | k | h | separated′ with k ≟B h
... | yes refl
  rewrite guard-self | guard-self | digest-self k = refl
... | no different
  rewrite guard-self | guard-self
    | digest-mismatch k h separated′ different
    | digest-mismatch h k (λ eq → sym (separated′ (sym eq))) (λ eq → different (sym eq))
    | digest-self k | digest-self h = refl

private
  padding-checked : ∀ Γ n →
    check-list (expect [] Γ native) (replicate n (imm 0ᶠ)) ≡ just (replicate n tt)
  padding-checked Γ zero = refl
  padding-checked Γ (suc n) rewrite padding-checked Γ n = refl

  join-env : Env
  join-env = reverse join-inputs

  after-encoding : Side → Env → Env
  after-encoding s Γ = reverse (map (_⦂ native) (limbs s)) ++ Γ

  left-env : Env
  left-env = after-encoding lhs join-env

  right-env : Env
  right-env = after-encoding rhs (opening-id lhs ⦂ accumulator ∷ left-env)

producer : ∀ keys t → KeysSeparated keys t → Producer (source keys t)
producer keys idle _ = tt
producer keys tick _ = tt
producer keys (join l r) separated rewrite validate-source keys (join l r) separated
  | padding-checked join-env (steps l + steps r)
  | padding-checked left-env (steps l)
  | padding-checked right-env (steps r) = tt
