{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.Validation (⋯ : _) (open Assumptions ⋯) where

open import zkir-v4.Types ⋯
open import zkir-v4.Syntax ⋯
open import Data.Bool.Base as B using (Bool; true; false; _∧_; if_then_else_)
open import Data.List.Base as L using (List; []; _∷_)
open import Data.Bool.ListAction using (any; all)
open import Data.Maybe.Base as M using (Maybe; nothing; just; _>>=_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Unit.Base using (⊤; tt)
open import Data.Vec.Base as V using ()
import Data.Fin.Properties as Fin
import Data.List.Properties as Lists
import Data.String.Properties as Strings
open import Relation.Nullary.Decidable using (does)

same-id : Identifier → Identifier → Bool
same-id x y = does (x Strings.≟ y)

private
  same-guard : Operand → Operand → Bool
  same-guard (imm x) (imm y) = does (x ≟ᶠ y)
  same-guard (var x) (var y) = same-id x y
  same-guard _ _ = false

  same-bytes : List Byte → List Byte → Bool
  same-bytes x y = does (Lists.≡-dec Fin._≟_ x y)

  digest : List Byte → List Byte
  digest blob = V.toList (sha256-bytes blob)

-- Each successful use removes exactly one item, irrespective of the
-- order in which bindings were made.  Persistent names prohibit rebinding.
remove-one : ∀ {A : Set} → (A → Bool) → List A → Maybe (List A)
remove-one p [] = nothing
remove-one p (x ∷ xs) with p x
... | true  = just xs
... | false = M.map (x ∷_) (remove-one p xs)

record Uses (A : Set) : Set where
  constructor uses
  field
    seen : List Identifier
    pending : List (Identifier × A)

bind : ∀ {A} → Identifier → A → Uses A → Maybe (Uses A)
bind id a (uses seen pending) with any (same-id id) seen
... | true  = nothing
... | false = just (uses (id ∷ seen) ((id , a) ∷ pending))

private
  consume : ∀ {A} → Identifier → (A → Bool) → Uses A → Maybe (Uses A)
  consume id p (uses seen pending) = M.map (uses seen)
    (remove-one (λ x → same-id id (proj₁ x) ∧ p (proj₂ x)) pending)

fold-check : ∀ {A B : Set} → (B → A → Maybe B) → B → List A → Maybe B
fold-check f b [] = just b
fold-check f b (x ∷ xs) = f b x >>= λ b′ → fold-check f b′ xs

finished : ∀ {A} → Maybe (Uses A) → Bool
finished (just (uses _ [])) = true
finished _ = false

private
  proof-step : Uses Operand → Instruction → Maybe (Uses Operand)
  proof-step u (inner-proof g id) = bind id g u
  proof-step u (prepare-verification g _ _ id _) = consume id (same-guard g) u
  proof-step u _ = just u

AccUses : Set
AccUses = Uses ⊤

acc-input : AccUses → TypedIdentifier → Maybe AccUses
acc-input u (id ⦂ accumulator) = bind id tt u
acc-input u _ = just u

acc-use : AccUses → Operand → Maybe AccUses
acc-use u (var id) = consume id (λ _ → true) u
acc-use u (imm _) = nothing

-- The instruction index connects the two consuming actions to their operands.
data AccAction : Instruction → Set where
  register-accumulator : ∀ {i} → Identifier → AccAction i
  fold-action : ∀ ops id → AccAction (accumulate ops id)
  discharge-accumulator : ∀ op → AccAction (verify-accumulator op)
  unchanged : ∀ {i} → AccAction i

acc-action : (i : Instruction) → AccAction i
acc-action (prepare-verification _ _ _ _ id) = register-accumulator id
acc-action (load-constant accumulator _ id) = register-accumulator id
acc-action (private-input _ accumulator id) = register-accumulator id
acc-action (public-input _ accumulator id) = register-accumulator id
acc-action (accumulate ops id) = fold-action ops id
acc-action (verify-accumulator op) = discharge-accumulator op
acc-action _ = unchanged

acc-step : AccUses → Instruction → Maybe AccUses
acc-step u i with acc-action i
... | register-accumulator id = bind id tt u
... | fold-action ops id = fold-check acc-use u ops >>= bind id tt
... | discharge-accumulator op = acc-use u op
... | unchanged = just u

private
  key-refs : List Instruction → List (List Byte)
  key-refs [] = []
  key-refs (prepare-verification _ h _ _ _ ∷ is) = h ∷ key-refs is
  key-refs (_ ∷ is) = key-refs is

  distinct : List (List Byte) → Bool
  distinct [] = true
  distinct (k ∷ ks) = B.not (any (same-bytes k) ks) ∧ distinct ks

resolve-vk : List Byte → List (List Byte) → Maybe (List Byte)
resolve-vk h [] = nothing
resolve-vk h (b ∷ bs) with same-bytes h (digest b)
... | true = just b
... | false = resolve-vk h bs

-- Key reuse is permitted.  Both directions of membership are required,
-- and duplicate digests in the table fail before the instruction walk.
check-keys : IrSource → Bool
check-keys s = distinct hashes ∧ all (λ h → any (same-bytes h) hashes) refs
                               ∧ all (λ h → any (same-bytes h) refs) hashes
  where
    hashes = L.map digest (IrSource.inner-vks s)
    refs = key-refs (IrSource.instructions s)

check-proofs : IrSource → Bool
check-proofs s = finished (fold-check proof-step (uses [] []) (IrSource.instructions s))

check-accumulators : IrSource → Bool
check-accumulators s = finished
  (fold-check acc-input (uses [] []) (IrSource.inputs s) >>= λ u →
   fold-check acc-step u (IrSource.instructions s))

validate : IrSource → Bool
validate s = check-proofs s ∧ check-accumulators s ∧ check-keys s
