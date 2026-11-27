{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.AccumulatorLifecycle (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Syntax ⋯
open import zkir-v4.Validation ⋯ using
  ( AccUses; Uses; uses; acc-input; acc-use; acc-step; acc-action
  ; unchanged; register-accumulator; discharge-accumulator; fold-action
  ; same-id; remove-one; bind; fold-check; finished
  ; validate; check-accumulators; check-proofs; check-keys
  )

open import Data.Bool.Base using (Bool; true; false; _∧_)
open import Data.Bool.ListAction using (any)
open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base using (Maybe; just; nothing; _>>=_; map)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁)
open import Data.String.Properties using (_≟_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; sym; cong)
open import Relation.Nullary using (Dec; does; yes; no)

Pending : Identifier → AccUses → Set
Pending id u = (id , tt) ∈ Uses.pending u

-- A successful instruction suffix, starting after the declared inputs.
data AccWalk : AccUses → List Instruction → Set where
  done : ∀ {u} → Uses.pending u ≡ [] → AccWalk u []
  next : ∀ {u u′ i is} →
    acc-step u i ≡ just u′ → AccWalk u′ is → AccWalk u (i ∷ is)

private
  bind-success : ∀ {A B : Set} (m : Maybe A) (f : A → Maybe B) {b} →
    (m >>= f) ≡ just b → Σ A λ a → m ≡ just a × f a ≡ just b
  bind-success nothing f ()
  bind-success (just a) f eq = a , refl , eq

  map-success : ∀ {A B : Set} (m : Maybe A) (f : A → B) {b} →
    map f m ≡ just b → Σ A λ a → m ≡ just a × f a ≡ b
  map-success nothing f ()
  map-success (just a) f eq = a , refl , just-injective eq

  nothing-not-just : ∀ {A : Set} {a : A} → nothing ≢ just a
  nothing-not-just ()

  finished-success : ∀ m → finished m ≡ true →
    Σ AccUses λ u → m ≡ just u × Uses.pending u ≡ []
  finished-success nothing ()
  finished-success (just (uses seen [])) _ = uses seen [] , refl , refl
  finished-success (just (uses seen (_ ∷ _))) ()

  walk-success : ∀ u is u′ →
    fold-check acc-step u is ≡ just u′ → Uses.pending u′ ≡ [] → AccWalk u is
  walk-success u [] .u refl empty = done empty
  walk-success u (i ∷ is) u′ checked empty
    with bind-success (acc-step u i) (λ v → fold-check acc-step v is) checked
  ... | v , step , rest = next step (walk-success v is u′ rest empty)

  middle-true : ∀ a b c → (a ∧ b ∧ c) ≡ true → b ≡ true
  middle-true false b c ()
  middle-true true false c ()
  middle-true true true c _ = refl

checked-acc-walk : ∀ s → check-accumulators s ≡ true →
  Σ AccUses λ u → AccWalk u (IrSource.instructions s)
checked-acc-walk s checked
  with finished-success
    (fold-check acc-input (uses [] []) (IrSource.inputs s) >>= λ u →
     fold-check acc-step u (IrSource.instructions s)) checked
... | u′ , ran , empty
  with bind-success (fold-check acc-input (uses [] []) (IrSource.inputs s))
    (λ u → fold-check acc-step u (IrSource.instructions s)) ran
... | u , _ , rest = u , walk-success u (IrSource.instructions s) u′ rest empty

accepted-acc-walk : ∀ s → validate s ≡ true →
  Σ AccUses λ u → AccWalk u (IrSource.instructions s)
accepted-acc-walk s checked =
  checked-acc-walk s (middle-true (check-proofs s) (check-accumulators s) (check-keys s) checked)

private
  bind-pending : ∀ id u {u′} →
    bind id tt u ≡ just u′ → Pending id u′
  bind-pending id (uses seen pending) eq
    with any (same-id id) seen
  ... | true = ⊥-elim (nothing-not-just eq)
  ... | false = subst (Pending id) (just-injective eq) (here refl)

  bind-retains : ∀ id out u {u′} →
    bind out tt u ≡ just u′ → Pending id u → Pending id u′
  bind-retains id out (uses seen pending) eq present
    with any (same-id out) seen
  ... | true = ⊥-elim (nothing-not-just eq)
  ... | false = subst (Pending id) (just-injective eq) (there present)

prepare-pending : ∀ u {u′ g hash ops proof out} →
  acc-step u (prepare-verification g hash ops proof out) ≡ just u′ → Pending out u′
prepare-pending u {out = out} = bind-pending out u

fold-pending : ∀ u {u′ ops out} →
  acc-step u (accumulate ops out) ≡ just u′ → Pending out u′
fold-pending u {ops = ops} {out = out} eq
  with bind-success (fold-check acc-use u ops) (bind out tt) eq
... | v , _ , bound = bind-pending out v bound

private
  remove-retains : ∀ {A : Set} (p : A → Bool) xs {ys x} →
    p x ≡ false → remove-one p xs ≡ just ys → x ∈ xs → x ∈ ys
  remove-retains p (x ∷ xs) {x = .x} eq removed (here refl)
    rewrite eq
    with map-success (remove-one p xs) (x ∷_) removed
  ... | ys , rest , refl = here refl
  remove-retains p (x ∷ xs) eq removed (there present) with p x
  ... | true = subst (_ ∈_) (just-injective removed) present
  ... | false
    with map-success (remove-one p xs) (x ∷_) removed
  ...   | ys , rest , refl = there (remove-retains p xs eq rest present)

  rejects : ∀ {a b : Identifier} (dec : Dec (a ≡ b)) → a ≢ b → does dec ≡ false
  rejects (yes eq) neq = ⊥-elim (neq eq)
  rejects (no _) _ = refl

  use-retains : ∀ id other u {u′} →
    other ≢ id → acc-use u (var other) ≡ just u′ → Pending id u → Pending id u′
  use-retains id other (uses seen pending) neq step present
    with map-success
      (remove-one (λ x → same-id other (proj₁ x) ∧ true) pending)
      (uses seen) step
  ... | rest , removed , refl =
    remove-retains (λ x → same-id other (proj₁ x) ∧ true) pending
      (cong (_∧ true) (rejects (other ≟ id) neq))
      removed present

  operands-disposition : ∀ id ops u {u′} →
    fold-check acc-use u ops ≡ just u′ → Pending id u → var id ∈ ops ⊎ Pending id u′
  operands-disposition id [] u refl present = inj₂ present
  operands-disposition id (imm _ ∷ ops) u () present
  operands-disposition id (var other ∷ ops) u step present
    with id ≟ other
  ... | yes refl = inj₁ (here refl)
  ... | no neq
    with bind-success (acc-use u (var other)) (λ v → fold-check acc-use v ops) step
  ... | v , used , rest
    with operands-disposition id ops v rest
      (use-retains id other u (λ eq → neq (sym eq)) used present)
  ... | inj₁ member = inj₁ (there member)
  ... | inj₂ kept = inj₂ kept

data AccDisposition (id : Identifier) (u′ : AccUses) : Instruction → Set where
  retained : ∀ {i} → Pending id u′ → AccDisposition id u′ i
  discharged : AccDisposition id u′ (verify-accumulator (var id))
  fold-input : ∀ {ops out} → var id ∈ ops → Pending out u′ →
    AccDisposition id u′ (accumulate ops out)

acc-disposition : ∀ id u i {u′} →
  acc-step u i ≡ just u′ → Pending id u → AccDisposition id u′ i
acc-disposition id u i eq present with acc-action i
... | unchanged = retained (subst (Pending id) (just-injective eq) present)
... | register-accumulator out = retained (bind-retains id out u eq present)
... | discharge-accumulator (imm _) = ⊥-elim (nothing-not-just eq)
acc-disposition id u i eq present | discharge-accumulator (var other) with other ≟ id
... | yes refl = discharged
... | no neq = retained (use-retains id other u neq eq present)
acc-disposition id u i eq present | fold-action ops out
  with bind-success (fold-check acc-use u ops) (bind out tt) eq
... | v , used , bound with operands-disposition id ops u used present
... | inj₁ member = fold-input member (bind-pending out v bound)
... | inj₂ kept = retained (bind-retains id out v bound kept)

-- The checker keeps the name pending until its first consuming instruction.
-- A fold starts a new pending lifetime at the output name.
data AccFate (id : Identifier) (u : AccUses) : List Instruction → Set where
  survives : ∀ {u′ i is} →
    acc-step u i ≡ just u′ → Pending id u′ → AccFate id u′ is → AccFate id u (i ∷ is)
  verified : ∀ {u′ is} →
    acc-step u (verify-accumulator (var id)) ≡ just u′ → AccWalk u′ is →
    AccFate id u (verify-accumulator (var id) ∷ is)
  folded : ∀ {u′ ops out is} →
    var id ∈ ops → acc-step u (accumulate ops out) ≡ just u′ →
    Pending out u′ → AccWalk u′ is → AccFate id u (accumulate ops out ∷ is)

follow-pending : ∀ {id u is} → AccWalk u is → Pending id u → AccFate id u is
follow-pending (done refl) ()
follow-pending {id} {u} {i ∷ is} (next eq rest) present
  with acc-disposition id u i eq present
... | retained kept = survives eq kept (follow-pending rest kept)
... | discharged = verified eq rest
... | fold-input member out = folded member eq out rest
