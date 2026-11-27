{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.ProducerResiduals (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Types ⋯
open import zkir-v4.Syntax ⋯
open import zkir-v4.Circuit ⋯
open import zkir-v4.CircuitProperties ⋯ using (Trace; SatisfiedRun)
open import zkir-v4.Operations ⋯ using (Mem; resolveᶠ; eval-guard; default-val; preprocess-bit-bounds)
open import zkir-v4.Producer ⋯
open import zkir-v4.ProducerStore ⋯ using (bind-success; demand-success; infer-success; fold-cons; fresh-success)
open import zkir-v4.ProducerStep ⋯ using (final-bindings)
open import zkir-v4.ProducerValuesHelpers ⋯ using (skip)
open import zkir-v4.ReverseShape ⋯ using (CircuitResidual; ReadResidual; Along)

open import Data.Bool using (Bool; true; false; T; _∧_; if_then_else_)
open import Data.Bool.Properties using (T-∧)
open import Function.Bundles using (Equivalence)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All)
  renaming ([] to []∀; _∷_ to _∷∀_)
open import Data.Maybe using (Maybe; just; _>>=_)
open import Data.Nat using (ℕ; _<_; _<ᵇ_; _≤ᵇ_; _≤?_; _<?_; _∸_; _^_)
open import Data.Nat.Properties using (<ᵇ⇒<; ≤ᵇ⇒≤; ≤-<-trans; ≤-trans; ∸-monoʳ-<)
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (isYes)

UncheckedRead : CircuitWitness → CircuitState → Maybe Operand → IrType → Identifier → Set
UncheckedRead w st g t id = Σ Bool λ active →
  (eval-guard (CircuitState.mem st) g ≡ just active) ×
  (if active then ⊤ else CircuitWitness.assign w id ≡ just (default-val t))

unchecked-read-active : ∀ w st g t id → eval-guard (CircuitState.mem st) g ≡ just true
  → UncheckedRead w st g t id
unchecked-read-active w st g t id bit = true , bit , tt

ComparisonTightening : Mem → Operand → Operand → ℕ → Set
ComparisonTightening m a b n =
  ∀ x y → resolveᶠ m a ≡ just x → resolveᶠ m b ≡ just y
  → valFr x < 2 ^ even4 n → valFr y < 2 ^ even4 n → valFr x < 2 ^ n × valFr y < 2 ^ n

private
  passed : ∀ {A : Set} (prefix : Maybe ⊤) b (result : Maybe A) {out}
    → ((prefix >> demand b) >> result) ≡ just out → T b
  passed prefix b result ok with bind-success (prefix >> demand b) (λ _ → result) ok
  ... | tt , head , _ = subst T (sym (demand-success (skip prefix head))) tt

  yes-true : ∀ {P : Set} (d : Dec P) → P → isYes d ≡ true
  yes-true (yes _) _ = refl
  yes-true (no reject) proof = ⊥-elim (reject proof)

bound-bits : ∀ sig Γ x n {after} → producer-step sig Γ (constrain-bits x n) ≡ just after
  → preprocess-bit-bounds (constrain-bits x n) ≡ true
bound-bits sig Γ x n checked with bind-success (bindings sig Γ (constrain-bits x n)) _ checked
... | _ , binds , _ = yes-true (n <? FR-BITS)
  (<ᵇ⇒< n FR-BITS (passed (expect sig Γ native x) (n <ᵇ FR-BITS) (just []) binds))

bound-division : ∀ sig Γ x n outs {after}
  → producer-step sig Γ (div-mod-power-of-two x n outs) ≡ just after
  → preprocess-bit-bounds (div-mod-power-of-two x n outs) ≡ true
bound-division sig Γ x n outs checked
  with bind-success (bindings sig Γ (div-mod-power-of-two x n outs)) _ checked
... | _ , binds , _ = yes-true (n ≤? 248)
  (≤ᵇ⇒≤ n 248 (passed (expect sig Γ native x) (n ≤ᵇ 248) (natives sig Γ 2 outs) binds))

bound-reconstitution : ∀ sig Γ d m n id {after}
  → producer-step sig Γ (reconstitute-field d m n id) ≡ just after
  → preprocess-bit-bounds (reconstitute-field d m n id) ≡ true
bound-reconstitution sig Γ d m n id checked
  with bind-success (bindings sig Γ (reconstitute-field d m n id)) _ checked
... | _ , binds , _
  with Equivalence.to (T-∧ {0 <ᵇ n} {n ≤ᵇ 248})
    (passed (expect sig Γ native d >> expect sig Γ native m)
      ((0 <ᵇ n) ∧ (n ≤ᵇ 248)) (one sig Γ id native) binds)
...   | positive , width
  rewrite yes-true (n ≤? 248) (≤ᵇ⇒≤ n 248 width)
        | yes-true (n <? FR-BITS) (≤-<-trans (≤ᵇ⇒≤ n 248 width) (<ᵇ⇒< 248 FR-BITS tt))
        | yes-true ((FR-BITS ∸ n) <? FR-BITS)
            (∸-monoʳ-< {m = FR-BITS} {o = 0} (<ᵇ⇒< 0 n positive)
              (≤-trans (≤ᵇ⇒≤ n 248 width) (≤ᵇ⇒≤ 248 FR-BITS tt))) = refl

private
  bound-comparison : ∀ sig Γ a b n id {after}
    → producer-step sig Γ (less-than a b n id) ≡ just after → n < FR-BITS
  bound-comparison sig Γ a b n id checked
    with bind-success (bindings sig Γ (less-than a b n id)) _ checked
  ... | _ , binds , _ = <ᵇ⇒< n FR-BITS
    (passed (expect sig Γ native a >> expect sig Γ native b) (n <ᵇ FR-BITS) (one sig Γ id native) binds)

  read-type : ∀ sig Γ g t id {after}
    → (transcript sig Γ g t id >>= fold-check fresh Γ) ≡ just after → valid-type t ≡ true
  read-type sig Γ g t id checked with bind-success (transcript sig Γ g t id) _ checked
  ... | bs , binds , inserted with refl ← final-bindings {xs = guard-ty sig Γ g} binds
    with fold-cons fresh Γ (id ⦂ t) [] inserted
  ...     | _ , added , _ = proj₂ (proj₂ (fresh-success Γ id t added))

  read-residual : ∀ w st g t id → valid-type t ≡ true
    → UncheckedRead w st g t id → ReadResidual w st g t id
  read-residual w st g t id valid (false , bit , same) = false , bit , same
  read-residual w st g t id valid (true , bit , _) = true , bit , valid

  -- Each rule lists the remaining premise and supplies the part checked by
  -- the producer's executable instruction check.
  ResidualRule : CircuitWitness → CircuitState → Instruction → Set₁
  ResidualRule w st i = Σ Set λ condition → ∀ sig Γ {after}
    → producer-step sig Γ i ≡ just after → condition → CircuitResidual w st i

  residual-rule : ∀ w st i → ResidualRule w st i
  residual-rule w st (constrain-bits x n) =
    ⊤ , λ sig Γ checked _ → bound-bits sig Γ x n checked
  residual-rule w st (div-mod-power-of-two x n outs) =
    ⊤ , λ sig Γ checked _ → bound-division sig Γ x n outs checked
  residual-rule w st (reconstitute-field d m n id) =
    ⊤ , λ sig Γ checked _ → bound-reconstitution sig Γ d m n id checked
  residual-rule w st (less-than a b n id) =
    ComparisonTightening (CircuitState.mem st) a b n ,
    λ sig Γ checked tighten → bound-comparison sig Γ a b n id checked , tighten
  residual-rule w st (public-input g t id) =
    UncheckedRead w st g t id ,
    λ sig Γ checked → read-residual w st g t id (read-type sig Γ g t id checked)
  residual-rule w st (private-input g t id) =
    UncheckedRead w st g t id ,
    λ sig Γ checked → read-residual w st g t id (read-type sig Γ g t id checked)
  residual-rule w st i = CircuitResidual w st i , λ _ _ _ proof → proof

Unchecked : CircuitWitness → CircuitState → Instruction → Set
Unchecked w st i = proj₁ (residual-rule w st i)

unchecked-along : ∀ {src st target} w is → Trace src w st (map lower is) target → Set
unchecked-along w [] Trace.end = ⊤
unchecked-along {st = st} w (i ∷ is) (Trace.next _ rest) =
  Unchecked w st i × unchecked-along w is rest

static-along : ∀ {src st target w is}
  → All (λ i → ∀ before → Unchecked w before i) is
  → (path : Trace src w st (map lower is) target) → unchecked-along w is path
static-along []∀ Trace.end = tt
static-along {st = st} (local ∷∀ later) (Trace.next _ rest) = local st , static-along later rest

private
  checked-along : ∀ {src st target} w is (path : Trace src w st (map lower is) target) Γ {after}
    → fold-check (producer-step (IrSource.outputs src)) Γ is ≡ just after
    → unchecked-along w is path → Along w is path
  checked-along w [] Trace.end Γ _ _ = tt
  checked-along {src} {st} w (i ∷ is) (Trace.next _ rest) Γ checked (local , later)
    with fold-cons (producer-step (IrSource.outputs src)) Γ i is checked
  ... | env , head , tail =
    proj₂ (residual-rule w st i) (IrSource.outputs src) Γ head local ,
    checked-along w is rest env tail later

producer-along : ∀ src w target → Producer src → (checked : SatisfiedRun src w target)
  → unchecked-along w (IrSource.instructions src) (SatisfiedRun.path checked)
  → Along w (IrSource.instructions src) (SatisfiedRun.path checked)
producer-along src w target producer checked local with infer-success src producer
... | Γ , _ , _ , code-check = checked-along w (IrSource.instructions src) (SatisfiedRun.path checked) Γ code-check local
