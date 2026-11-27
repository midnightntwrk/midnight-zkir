{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.CircuitBindingNames (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Producer ⋯
open import zkir-v4.ProducerStore ⋯ using (bind-success; fold-cons; fresh-success; infer-success)
open import zkir-v4.Syntax ⋯
open import zkir-v4.Types ⋯
open import Data.Bool as B using (Bool; _∧_; _∨_)
open import Data.List using (List; []; _∷_; [_]; _++_; map; length; foldr; concatMap)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Properties using (map-++)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.AllPairs as Pairs using ()
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Nat using (_+_; _<ᵇ_; _≤ᵇ_; _≟_)
open import Data.Product using (∃; _×_; _,_; proj₁)
import Data.String.Properties as Strings
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst; sym; trans)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (does)

-- The outputs belong to the expression store.  Inner proof bytes use a
-- separate namespace.
output-names : Instruction → List Identifier
output-names (encode _ os) = os
output-names (assert _) = []
output-names (cond-select _ _ _ o) = [ o ]
output-names (constrain-bits _ _) = []
output-names (constrain-eq _ _) = []
output-names (constrain-to-boolean _) = []
output-names (copy _ o) = [ o ]
output-names (impact _ _) = []
output-names (ec-mul _ _ o) = [ o ]
output-names (ec-mul-generator _ o) = [ o ]
output-names (hash-to-curve _ o) = [ o ]
output-names (into-coordinates _ (x , y)) = x ∷ y ∷ []
output-names (from-coordinates (_ , _) o) = [ o ]
output-names (into-bytes32 _ o) = [ o ]
output-names (from-bytes32 _ _ o) = [ o ]
output-names (reverse-bytes _ o) = [ o ]
output-names (bytes32-into-low-high _ (lo , hi)) = lo ∷ hi ∷ []
output-names (bytes32-from-low-high (_ , _) o) = [ o ]
output-names (div-mod-power-of-two _ _ os) = os
output-names (reconstitute-field _ _ _ o) = [ o ]
output-names (transient-hash _ o) = [ o ]
output-names (persistent-hash _ _ o) = [ o ]
output-names (keccak256 _ _ o) = [ o ]
output-names (test-eq _ _ o) = [ o ]
output-names (add _ _ o) = [ o ]
output-names (mul _ _ o) = [ o ]
output-names (neg _ o) = [ o ]
output-names (inv _ o) = [ o ]
output-names (not _ o) = [ o ]
output-names (less-than _ _ _ o) = [ o ]
output-names (jubjub-scalar-from-native _ o) = [ o ]
output-names (public-input _ _ o) = [ o ]
output-names (private-input _ _ o) = [ o ]
output-names (circuit-output _) = []
output-names (slice _ _ _ o) = [ o ]
output-names (nth _ _ o) = [ o ]
output-names (concat _ o) = [ o ]
output-names (reverse _ o) = [ o ]
output-names (load-constant _ _ o) = [ o ]
output-names (sha512 _ _ o) = [ o ]
output-names (and _ o) = [ o ]
output-names (or _ o) = [ o ]
output-names (xor _ o) = [ o ]
output-names (to-bytes _ o) = [ o ]
output-names (from-bytes _ _ o) = [ o ]
output-names (bytes-into-natives _ os) = os
output-names (bytes-from-natives _ _ o) = [ o ]
output-names (inner-proof _ _) = []
output-names (prepare-verification _ _ _ _ o) = [ o ]
output-names (accumulate _ o) = [ o ]
output-names (verify-accumulator _) = []

private
  name = TypedIdentifier.name

  HasNames : Maybe Env → List Identifier → Set
  HasNames result names = ∀ {bs} → result ≡ just bs → map name bs ≡ names

  after : ∀ {A : Set} {names} (x : Maybe A) {f : A → Maybe Env} →
    (∀ a → HasNames (f a) names) → HasNames (x >>= f) names
  after nothing _ ()
  after (just a) step = step a

  past : ∀ {A : Set} {names} (x : Maybe A) {r : Maybe Env} →
    HasNames r names → HasNames (x >> r) names
  past x step = after x (λ _ → step)

  fixed-names : ∀ bs → HasNames (just bs) (map name bs)
  fixed-names bs refl = refl

  single-name : ∀ sig Γ o t → HasNames (one sig Γ o t) [ o ]
  single-name sig Γ o t = fixed-names ((o ⦂ t) ∷ [])

  native-names : ∀ sig Γ n os → HasNames (natives sig Γ n os) os
  native-names sig Γ n os = past (demand (does (length os ≟ n))) λ { refl → mapped os }
    where
    mapped : ∀ xs → map name (map (_⦂ native) xs) ≡ xs
    mapped [] = refl
    mapped (x ∷ xs) = cong (x ∷_) (mapped xs)

  unary-names : ∀ sig Γ (p : IrType → Bool) x o → HasNames (unary sig Γ p x o) [ o ]
  unary-names sig Γ p x o = after (ty sig Γ x) λ t → past (demand (p t)) (single-name sig Γ o t)

  binary-names : ∀ sig Γ (p : IrType → Bool) x y o → HasNames (binary sig Γ p x y o) [ o ]
  binary-names sig Γ p x y o = after (ty sig Γ x) λ t →
    past (expect sig Γ t y >> demand (p t)) (single-name sig Γ o t)

  bool-names : ∀ sig Γ xs o → HasNames (bools sig Γ xs o) [ o ]
  bool-names sig Γ [] o ()
  bool-names sig Γ (x ∷ xs) o =
    past (expect-all sig Γ bool (x ∷ xs)) (single-name sig Γ o bool)

bindings-names : ∀ sig Γ i {bs} → bindings sig Γ i ≡ just bs →
  map TypedIdentifier.name bs ≡ output-names i
bindings-names sig Γ (encode x os) =
  after (ty sig Γ x) λ t → native-names sig Γ (encoded-len t) os
bindings-names sig Γ (assert x) =
  past (expect sig Γ native x) (fixed-names [])
bindings-names sig Γ (cond-select g a b o) =
  past (expect sig Γ native g) (binary-names sig Γ selectable a b o)
bindings-names sig Γ (constrain-bits x n) =
  past (expect sig Γ native x >> demand (n <ᵇ FR-BITS)) (fixed-names [])
bindings-names sig Γ (constrain-eq x y) =
  after (ty sig Γ x) λ t →
    past (expect sig Γ t y) (past (demand (B.not (equal t accumulator))) (fixed-names []))
bindings-names sig Γ (constrain-to-boolean x) =
  past (expect sig Γ native x) (fixed-names [])
bindings-names sig Γ (copy x o) =
  unary-names sig Γ (λ t → B.not (equal t accumulator)) x o
bindings-names sig Γ (impact g xs) =
  past (expect sig Γ native g >> expect-all sig Γ native xs) (fixed-names [])
bindings-names sig Γ (ec-mul p s o) =
  after (ty sig Γ p) λ t → after (curve t) λ { (scalar , _) →
    past (expect sig Γ scalar s) (single-name sig Γ o t) }
bindings-names sig Γ (ec-mul-generator s o) =
  after (ty sig Γ s >>= from-scalar) (single-name sig Γ o)
bindings-names sig Γ (hash-to-curve xs o) =
  past (expect-all sig Γ native xs) (single-name sig Γ o jubjub-point)
bindings-names sig Γ (into-coordinates p (x , y)) =
  after (ty sig Γ p) λ t → after (curve t) λ { (_ , coord) →
    fixed-names ((x ⦂ coord) ∷ (y ⦂ coord) ∷ []) }
bindings-names sig Γ (from-coordinates (x , y) o) =
  after (ty sig Γ x) λ t → past (expect sig Γ t y)
    (after (from-base t) (single-name sig Γ o))
bindings-names sig Γ (into-bytes32 x o) =
  after (ty sig Γ x >>= repr-width) λ n →
    past (demand (does (n ≟ 32))) (single-name sig Γ o bytes32)
bindings-names sig Γ (from-bytes32 x t o) =
  past (expect sig Γ bytes32 x >> demand (from-width 32 t)) (single-name sig Γ o t)
bindings-names sig Γ (reverse-bytes x o) =
  after (bytelen sig Γ x) λ n → single-name sig Γ o (bytes n)
bindings-names sig Γ (bytes32-into-low-high x (lo , hi)) =
  past (expect sig Γ bytes32 x) (native-names sig Γ 2 (lo ∷ hi ∷ []))
bindings-names sig Γ (bytes32-from-low-high (lo , hi) o) =
  past (expect sig Γ native lo >> expect sig Γ native hi) (single-name sig Γ o bytes32)
bindings-names sig Γ (div-mod-power-of-two x n os) =
  past (expect sig Γ native x >> demand (n ≤ᵇ 248)) (native-names sig Γ 2 os)
bindings-names sig Γ (reconstitute-field d m n o) =
  past (expect sig Γ native d >> expect sig Γ native m >> demand ((0 <ᵇ n) ∧ (n ≤ᵇ 248)))
    (single-name sig Γ o native)
bindings-names sig Γ (transient-hash xs o) =
  past (expect-all sig Γ native xs) (single-name sig Γ o native)
bindings-names sig Γ (persistent-hash a xs o) =
  past (aligned-inputs sig Γ a xs) (single-name sig Γ o bytes32)
bindings-names sig Γ (keccak256 a xs o) =
  past (aligned-inputs sig Γ a xs) (single-name sig Γ o bytes32)
bindings-names sig Γ (test-eq x y o) =
  after (ty sig Γ x) λ t →
    past (expect sig Γ t y) (past (demand (B.not (equal t accumulator))) (single-name sig Γ o native))
bindings-names sig Γ (add x y o) =
  binary-names sig Γ arithmetic x y o
bindings-names sig Γ (mul x y o) =
  binary-names sig Γ field-type x y o
bindings-names sig Γ (neg x o) =
  unary-names sig Γ (λ t → arithmetic t ∨ equal t bool) x o
bindings-names sig Γ (inv x o) =
  unary-names sig Γ field-type x o
bindings-names sig Γ (not x o) =
  past (expect sig Γ native x) (single-name sig Γ o native)
bindings-names sig Γ (less-than x y n o) =
  past (expect sig Γ native x >> expect sig Γ native y >> demand (n <ᵇ FR-BITS))
    (single-name sig Γ o native)
bindings-names sig Γ (jubjub-scalar-from-native x o) =
  past (expect sig Γ native x) (single-name sig Γ o jubjub-scalar)
bindings-names sig Γ (public-input g t o) =
  past (guard-ty sig Γ g) (single-name sig Γ o t)
bindings-names sig Γ (private-input g t o) =
  past (guard-ty sig Γ g) (single-name sig Γ o t)
bindings-names sig Γ (circuit-output xs) =
  after (check-list (ty sig Γ) xs) λ ts → past (demand (eq-types ts sig)) (fixed-names [])
bindings-names sig Γ (slice x start n o) =
  after (bytelen sig Γ x) λ w →
    past (demand (valid-bytes-length n ∧ ((start + n) ≤ᵇ w))) (single-name sig Γ o (bytes n))
bindings-names sig Γ (nth x k o) =
  after (bytelen sig Γ x) λ w → past (demand (k <ᵇ w)) (single-name sig Γ o byte)
bindings-names sig Γ (concat xs o) =
  after (check-list (λ x → ty sig Γ x >>= concat-width) xs) λ ws →
    let n = foldr _+_ 0 ws in past (demand (valid-bytes-length n)) (single-name sig Γ o (bytes n))
bindings-names sig Γ (reverse x o) =
  after (bytelen sig Γ x) λ n → single-name sig Γ o (bytes n)
bindings-names sig Γ (load-constant t raw o) =
  past (demand (does (length raw ≟ encoded-len t))) (single-name sig Γ o t)
bindings-names sig Γ (sha512 a xs o) =
  past (aligned-inputs sig Γ a xs) (single-name sig Γ o (bytes 64))
bindings-names sig Γ (and xs o) =
  bool-names sig Γ xs o
bindings-names sig Γ (or xs o) =
  bool-names sig Γ xs o
bindings-names sig Γ (xor xs o) =
  bool-names sig Γ xs o
bindings-names sig Γ (to-bytes x o) =
  after (ty sig Γ x >>= repr-width) λ n → single-name sig Γ o (bytes n)
bindings-names sig Γ (from-bytes x t o) =
  after (bytelen sig Γ x) λ n → past (demand (from-width n t)) (single-name sig Γ o t)
bindings-names sig Γ (bytes-into-natives x os) =
  after (bytelen sig Γ x) λ n → native-names sig Γ (bytes-encoded-len n) os
bindings-names sig Γ (bytes-from-natives xs n o) =
  past (demand (valid-bytes-length n ∧ does (length xs ≟ bytes-encoded-len n)))
    (past (expect-all sig Γ native xs) (single-name sig Γ o (bytes n)))
bindings-names sig Γ (inner-proof g _) =
  past (expect sig Γ native g) (fixed-names [])
bindings-names sig Γ (prepare-verification g _ xs _ o) =
  past (expect sig Γ native g >> expect-all sig Γ native xs) (single-name sig Γ o accumulator)
bindings-names sig Γ (accumulate xs o) =
  past (demand (2 ≤ᵇ length xs) >> expect-all sig Γ accumulator xs) (single-name sig Γ o accumulator)
bindings-names sig Γ (verify-accumulator x) =
  past (expect sig Γ accumulator x) (fixed-names [])

private
  fold-fresh-++ : ∀ Γ xs ys {mid final} → fold-check fresh Γ xs ≡ just mid →
    fold-check fresh mid ys ≡ just final → fold-check fresh Γ (xs ++ ys) ≡ just final
  fold-fresh-++ Γ [] ys refl tail = tail
  fold-fresh-++ Γ (x ∷ xs) ys head tail with fresh Γ x
  ... | nothing with () ← head
  fold-fresh-++ Γ (x ∷ xs) ys head tail | just next = fold-fresh-++ next xs ys head tail

  flatten-bindings : ∀ sig Γ is {final} → fold-check (producer-step sig) Γ is ≡ just final →
    ∃ λ bs → fold-check fresh Γ bs ≡ just final × map name bs ≡ concatMap output-names is
  flatten-bindings sig Γ [] checked = [] , checked , refl
  flatten-bindings sig Γ (i ∷ is) checked with fold-cons (producer-step sig) Γ i is checked
  ... | mid , step , tail with bind-success (bindings sig Γ i) (fold-check fresh Γ) step
  ...   | bs , binds , inserted with flatten-bindings sig mid is tail
  ...     | rest , run , names = bs ++ rest , fold-fresh-++ Γ bs rest inserted run ,
    trans (map-++ name bs rest) (cong₂ _++_ (bindings-names sig Γ i binds) names)

  lookup-absent : ∀ Γ id → type-of Γ id ≡ nothing → id ∉ map name Γ
  lookup-absent [] id _ ()
  lookup-absent ((x ⦂ t) ∷ Γ) id absent member with x Strings.≟ id
  ... | yes _ with () ← absent
  lookup-absent ((x ⦂ t) ∷ Γ) id absent (here equal) | no different = different (sym equal)
  lookup-absent ((x ⦂ t) ∷ Γ) id absent (there member) | no _ = lookup-absent Γ id absent member

  fold-fresh-unique : ∀ Γ bs {final} → fold-check fresh Γ bs ≡ just final →
    Unique (map name bs) × (∀ {id} → id ∈ map name bs → id ∉ map name Γ)
  fold-fresh-unique Γ [] _ = Pairs.[] , λ ()
  fold-fresh-unique Γ ((id ⦂ t) ∷ bs) checked
    with fold-cons fresh Γ (id ⦂ t) bs checked
  ... | mid , first , rest with fresh-success Γ id t first
  ...   | refl , absent , _ with fold-fresh-unique ((id ⦂ t) ∷ Γ) bs rest
  ...     | unique , disjoint =
    (All.tabulate (λ member equal → disjoint member (here (sym equal))) Pairs.∷ unique) ,
    λ { (here refl) → lookup-absent Γ id absent
      ; (there member) → λ earlier → disjoint member (there earlier) }

producer-names-unique : ∀ src → Producer src →
  Unique (map TypedIdentifier.name (IrSource.inputs src) ++ concatMap output-names (IrSource.instructions src))
producer-names-unique src producer with infer-success src producer
... | Γ , final , declared , checked with flatten-bindings (IrSource.outputs src) Γ (IrSource.instructions src) checked
...   | bs , run , names =
  let declared-names = map name (IrSource.inputs src)
      binds = fold-fresh-++ [] (IrSource.inputs src) bs declared run
  in subst Unique (trans (map-++ name (IrSource.inputs src) bs) (cong (declared-names ++_) names))
       (proj₁ (fold-fresh-unique [] (IrSource.inputs src ++ bs) binds))
