{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.ProducerValues (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Types ⋯
open import zkir-v4.Syntax ⋯
open import zkir-v4.Operations ⋯
open import zkir-v4.Encoding ⋯ using (decode; pack-bytes) renaming (encode to fields)
open import zkir-v4.EncodingProperties ⋯ using (decode-typed)
open import zkir-v4.Producer ⋯
open import zkir-v4.ProducerStore ⋯ using (StoreTyped; bind-success)
open import zkir-v4.ProducerValuesHelpers ⋯
open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; length; take; drop)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (_+_; _≟_; _<?_; _∸_; _^_)
open import Data.Product using (_,_; proj₂)
open import Data.Vec.Properties using (length-toList)
open import Relation.Nullary.Decidable using (does)
open import Relation.Binary.PropositionalEquality using (refl; trans; cong)

module Rules (sig : List IrType) (Γ : Env) (m : Mem) (store : StoreTyped Γ m) where
  private
    Checks = Rule sig Γ m
    expect′ = expect sig Γ
    all′ = expect-all sig Γ
    ty′ = ty sig Γ
    width′ = bytelen sig Γ

  hash-curve : ∀ xs o → Checks (hash-to-curve xs o)
  hash-curve xs o declared computed with bind-success (resolve-all-Fr m xs) _ computed
  ... | vs , _ , resolved = fixed (write-type _ _ refl resolved) (skip (all′ native xs) declared)

  transient : ∀ xs o → Checks (transient-hash xs o)
  transient xs o declared computed with bind-success (resolve-all-Fr m xs) _ computed
  ... | vs , _ , resolved = fixed (write-type _ _ refl resolved) (skip (all′ native xs) declared)

  persistent-value : ∀ a xs o → Checks (persistent-hash a xs o)
  persistent-value a xs o declared computed with bind-success (resolve-all-Fr m xs) _ computed
  ... | vs , _ , resolved with bind-success (persistent-hash-fn a vs) _ resolved
  ... | digest , _ , written = fixed (write-type _ _ (cong bytes (length-toList digest)) written) (skip (aligned-inputs sig Γ a xs) declared)

  keccak-value : ∀ a xs o → Checks (keccak256 a xs o)
  keccak-value a xs o declared computed with bind-success (resolve-all-Fr m xs) _ computed
  ... | vs , _ , resolved with bind-success (keccak-fn a vs) _ resolved
  ... | digest , _ , written = fixed (write-type _ _ (cong bytes (length-toList digest)) written) (skip (aligned-inputs sig Γ a xs) declared)

  sha-value : ∀ a xs o → Checks (sha512 a xs o)
  sha-value a xs o declared computed with bind-success (resolve-all-Fr m xs) _ computed
  ... | vs , _ , resolved with bind-success (sha512-fn a vs) _ resolved
  ... | digest , _ , written = fixed (write-type _ _ (cong bytes (length-toList digest)) written) (skip (aligned-inputs sig Γ a xs) declared)

  native-not : ∀ x o → Checks (not x o)
  native-not x o declared computed with bind-success (resolve𝔹 m x) _ computed
  ... | _ , _ , resolved = fixed (write-type _ _ refl resolved) (skip (expect′ native x) declared)

  native-scalar : ∀ x o → Checks (jubjub-scalar-from-native x o)
  native-scalar x o declared computed with bind-success (resolveᶠ m x) _ computed
  ... | _ , _ , resolved = fixed (write-type _ _ refl resolved) (skip (expect′ native x) declared)

  nth-value : ∀ x n o → Checks (nth x n o)
  nth-value x n o declared computed with bind-success (width′ x) _ declared | bind-success (resolve-bytes m x) _ computed
  ... | w , _ , checked-n | bs , _ , resolved with bind-success (at bs n) _ resolved
  ... | byte-value , _ , written = fixed (write-type _ _ refl written) (skip (demand (n Data.Nat.<ᵇ w)) checked-n)

  and-value : ∀ xs o → Checks (and xs o)
  and-value [] o () _
  and-value xs@(_ ∷ _) o declared computed with bind-success (resolve-typed-bools m xs) _ computed
  ... | vs , _ , written = fixed (write-type _ _ refl written) (skip (all′ bool xs) declared)

  or-value : ∀ xs o → Checks (or xs o)
  or-value [] o () _
  or-value xs@(_ ∷ _) o declared computed with bind-success (resolve-typed-bools m xs) _ computed
  ... | vs , _ , written = fixed (write-type _ _ refl written) (skip (all′ bool xs) declared)

  xor-value : ∀ xs o → Checks (xor xs o)
  xor-value [] o () _
  xor-value xs@(_ ∷ _) o declared computed with bind-success (resolve-typed-bools m xs) _ computed
  ... | vs , _ , written = fixed (write-type _ _ refl written) (skip (all′ bool xs) declared)

  load-value : ∀ t raw o → Checks (load-constant t raw o)
  load-value t raw o declared computed with bind-success (decode t raw) _ computed
  ... | v , decoded , written = fixed (write-type _ _ (decode-typed {t = t} {raw = raw} decoded) written)
                                (skip (demand (does (length raw ≟ encoded-len t))) declared)

  from-natives : ∀ xs n o → Checks (bytes-from-natives xs n o)
  from-natives xs n o declared computed with bind-success (resolve-all-Fr m xs) _ computed
  ... | vs , _ , next with bind-success (decode (bytes n) vs) _ next
  ... | v , decoded , written = fixed (write-type _ _ (decode-typed {t = bytes n} {raw = vs} decoded) written)
    (skip (all′ native xs) (skip (demand (valid-bytes-length n Data.Bool.∧ does (length xs ≟ bytes-encoded-len n))) declared))

  encode-value : ∀ x os → Checks (encode x os)
  encode-value x os declared computed with bind-success (ty′ x) _ declared | bind-success (resolve m x) _ computed
  ... | t , _ , inferred | v , _ , assigned = fixed (native-writes os (fields v) assigned)
                                               (inferred-natives sig Γ (encoded-len t) os inferred)

  into-natives : ∀ x os → Checks (bytes-into-natives x os)
  into-natives x os declared computed with bind-success (width′ x) _ declared | bind-success (resolve-bytes m x) _ computed
  ... | n , _ , inferred | bs , _ , assigned = fixed (native-writes os (pack-bytes bs) assigned)
                                                (inferred-natives sig Γ (bytes-encoded-len n) os inferred)

  into-parts : ∀ x lo hi → Checks (bytes32-into-low-high x (lo , hi))
  into-parts x lo hi declared computed with bind-success (resolve-bytes m x) _ computed
  ... | bs , _ , gated with checked (length bs ≟ 32) gated
  ... | _ , assigned = fixed (native-writes (lo ∷ hi ∷ []) (pack-bytes bs) assigned)
    (inferred-natives sig Γ 2 (lo ∷ hi ∷ []) (skip (expect′ bytes32 x) declared))

  divide-value : ∀ x n os → Checks (div-mod-power-of-two x n os)
  divide-value x n os declared computed with bind-success (resolveᶠ m x) _ (take-result (preprocess-bit-bounds (div-mod-power-of-two x n os)) computed)
  ... | v , _ , assigned = fixed (native-writes os (from-le-bits (drop n (to-le-bits v)) ∷ from-le-bits (take n (to-le-bits v)) ∷ []) assigned)
    (inferred-natives sig Γ 2 os (skip (expect′ native x >> demand (n Data.Nat.≤ᵇ 248)) declared))

  test-value : ∀ a b o → Checks (test-eq a b o)
  test-value a b o declared computed with bind-success (ty′ a) _ declared | bind-success (resolve m a) _ computed
  ... | t , _ , rest | x , _ , step with bind-success (expect′ t b) _ rest | bind-success (resolve m b) _ step
  ... | _ , _ , check | y , _ , result with bind-success (valEq? x y) _ result
  ... | eq , _ , written = fixed (write-type _ _ refl written) (skip (demand (Data.Bool.not (equal t accumulator))) check)

  assert-value : ∀ x → Checks (assert x)
  assert-value x declared computed with bind-success (resolve𝔹 m x) _ computed
  ... | false , _ , ()
  ... | true , _ , refl = just-injective (skip (expect′ native x) declared)

  bool-constraint : ∀ x → Checks (constrain-to-boolean x)
  bool-constraint x declared computed with bind-success (resolve𝔹 m x) _ computed
  ... | b , _ , refl = just-injective (skip (expect′ native x) declared)

  equal-constraint : ∀ a b → Checks (constrain-eq a b)
  equal-constraint a b declared computed with bind-success (ty′ a) _ declared | bind-success (resolve m a) _ computed
  ... | t , _ , rest | x , _ , step with bind-success (expect′ t b) _ rest | bind-success (resolve m b) _ step
  ... | _ , _ , check | y , _ , result with bind-success (constrainEq? x y) _ result
  ... | false , _ , ()
  ... | true , _ , refl = just-injective (skip (demand (Data.Bool.not (equal t accumulator))) check)

  bit-value : ∀ x n → Checks (constrain-bits x n)
  bit-value x n declared computed with bind-success (resolveᶠ m x) _ (take-result (preprocess-bit-bounds (constrain-bits x n)) computed)
  ... | v , _ , gated with checked (valFr v <? 2 ^ n) gated
  ... | _ , refl = just-injective (skip (expect′ native x >> demand (n Data.Nat.<ᵇ FR-BITS)) declared)

  less-value : ∀ a b n o → Checks (less-than a b n o)
  less-value a b n o declared computed with bind-success (resolveᶠ m a) _ computed
  ... | x , _ , rest with bind-success (resolveᶠ m b) _ rest
  ... | y , _ , guarded with checked (n <? FR-BITS) guarded
  ... | _ , x-bound with checked (valFr x <? 2 ^ n) x-bound
  ... | _ , y-bound with checked (valFr y <? 2 ^ n) y-bound
  ... | _ , written = fixed (write-type _ _ refl written)
    (skip (expect′ native a >> expect′ native b >> demand (n Data.Nat.<ᵇ FR-BITS)) declared)

  selected : ∀ g a b o → Checks (cond-select g a b o)
  selected g a b o declared computed with binary-output sig Γ m selectable a b o store (skip (expect′ native g) declared)
  ... | x , y , ra , rb , same , bound with bind-success (resolve𝔹 m g) _ computed
  ... | true , _ , gated rewrite ra | rb = trans (write-type _ _ refl (proj₂ (checked (typeof x ≟T typeof y) gated))) bound
  ... | false , _ , gated rewrite ra | rb = trans (write-type _ _ same (proj₂ (checked (typeof x ≟T typeof y) gated))) bound

  reconstitute-value : ∀ d a n o → Checks (reconstitute-field d a n o)
  reconstitute-value d a n o declared computed
    with bind-success (resolveᶠ m d) _ (take-result (preprocess-bit-bounds (reconstitute-field d a n o)) computed)
  ... | x , _ , rest with bind-success (resolveᶠ m a) _ rest
  ... | y , _ , guarded with checked (valFr y <? 2 ^ n) guarded
  ... | _ , next with checked (valFr x <? 2 ^ (FR-BITS ∸ n)) next
  ... | _ , last with checked (valFr y + 2 ^ n Data.Nat.* valFr x <? FR-ORDER) last
  ... | _ , written = fixed (write-type _ _ refl written)
    (skip (expect′ native d >> expect′ native a >> demand ((0 Data.Nat.<ᵇ n) Data.Bool.∧ (n Data.Nat.≤ᵇ 248))) declared)
