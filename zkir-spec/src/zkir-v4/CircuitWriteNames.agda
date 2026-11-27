{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.CircuitWriteNames (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Types ⋯
open import zkir-v4.Syntax ⋯
open import zkir-v4.Operations ⋯
open import zkir-v4.Encoding ⋯ using (decode; pack-bytes) renaming (encode to encode-value)
open import zkir-v4.CircuitBindingNames ⋯ using (output-names)
open import zkir-v4.ProducerStore ⋯ using (bind-success)

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Nat using (_+_; _*_; _^_; _∸_; _<?_; _≤?_; _≟_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (Dec; yes; no)

private
  WriteNames : Maybe (List (Identifier × IrValue)) → List Identifier → Set
  WriteNames result ids = ∀ {ws} → result ≡ just ws → map proj₁ ws ≡ ids

  after : ∀ {A : Set} (result : Maybe A) {put : A → Maybe (List (Identifier × IrValue))} {ids}
    → (∀ x → WriteNames (put x) ids) → WriteNames (result >>= put) ids
  after nothing _ ()
  after (just x) names = names x

  guarded : ∀ {P : Set} (d : Dec P) {result ids}
    → WriteNames result ids → WriteNames (guardD d result) ids
  guarded (yes _) names = names
  guarded (no _) _ ()

  selected : ∀ (flag : Bool) {result ids}
    → WriteNames result ids → WriteNames (if flag then result else nothing) ids
  selected true names = names
  selected false _ ()

  one : ∀ id v → WriteNames (write id v) (id ∷ [])
  one id v refl = refl

  pair : ∀ x y (values : IrValue × IrValue) →
    WriteNames (just ((x , proj₁ values) ∷ (y , proj₂ values) ∷ [])) (x ∷ y ∷ [])
  pair x y (a , b) refl = refl

  many : ∀ ids vs → WriteNames (writes ids vs) ids
  many [] [] refl = refl
  many (id ∷ ids) (v ∷ vs) accepted
    with bind-success (writes ids vs) _ accepted
  ... | rest , wrote , refl = cong (id ∷_) (many ids vs wrote)
  many [] (_ ∷ _) ()
  many (_ ∷ _) [] ()

bounded-names : ∀ m i → WriteNames (bounded-compute m i) (output-names i)
bounded-names m (constrain-bits x bits) =
  after (resolveᶠ m x) λ v →
    guarded (valFr v <? 2 ^ bits) λ { refl → refl }
bounded-names m (div-mod-power-of-two x bits outs) =
  after (resolveᶠ m x) λ v → many outs _
bounded-names m (reconstitute-field d mo bits out) =
  after (resolveᶠ m d) λ x →
  after (resolveᶠ m mo) λ y →
  guarded (valFr y <? 2 ^ bits)
    (guarded (valFr x <? 2 ^ (FR-BITS ∸ bits))
      (guarded (valFr y + 2 ^ bits * valFr x <? FR-ORDER) (one out _)))
bounded-names _ (encode _ _) ()
bounded-names _ (assert _) ()
bounded-names _ (cond-select _ _ _ _) ()
bounded-names _ (constrain-eq _ _) ()
bounded-names _ (constrain-to-boolean _) ()
bounded-names _ (copy _ _) ()
bounded-names _ (impact _ _) ()
bounded-names _ (ec-mul _ _ _) ()
bounded-names _ (ec-mul-generator _ _) ()
bounded-names _ (hash-to-curve _ _) ()
bounded-names _ (into-coordinates _ _) ()
bounded-names _ (from-coordinates _ _) ()
bounded-names _ (into-bytes32 _ _) ()
bounded-names _ (from-bytes32 _ _ _) ()
bounded-names _ (reverse-bytes _ _) ()
bounded-names _ (bytes32-into-low-high _ _) ()
bounded-names _ (bytes32-from-low-high _ _) ()
bounded-names _ (transient-hash _ _) ()
bounded-names _ (persistent-hash _ _ _) ()
bounded-names _ (keccak256 _ _ _) ()
bounded-names _ (test-eq _ _ _) ()
bounded-names _ (add _ _ _) ()
bounded-names _ (mul _ _ _) ()
bounded-names _ (neg _ _) ()
bounded-names _ (inv _ _) ()
bounded-names _ (not _ _) ()
bounded-names _ (less-than _ _ _ _) ()
bounded-names _ (jubjub-scalar-from-native _ _) ()
bounded-names _ (public-input _ _ _) ()
bounded-names _ (private-input _ _ _) ()
bounded-names _ (circuit-output _) ()
bounded-names _ (slice _ _ _ _) ()
bounded-names _ (nth _ _ _) ()
bounded-names _ (concat _ _) ()
bounded-names _ (reverse _ _) ()
bounded-names _ (load-constant _ _ _) ()
bounded-names _ (sha512 _ _ _) ()
bounded-names _ (and _ _) ()
bounded-names _ (or _ _) ()
bounded-names _ (xor _ _) ()
bounded-names _ (to-bytes _ _) ()
bounded-names _ (from-bytes _ _ _) ()
bounded-names _ (bytes-into-natives _ _) ()
bounded-names _ (bytes-from-natives _ _ _) ()
bounded-names _ (inner-proof _ _) ()
bounded-names _ (prepare-verification _ _ _ _ _) ()
bounded-names _ (accumulate _ _) ()
bounded-names _ (verify-accumulator _) ()

compute-names : ∀ m i → WriteNames (compute m i) (output-names i)
compute-names m (encode x outs) =
  after (resolve m x) λ v → many outs (map val-native (encode-value v))
compute-names m (assert x) = after (resolve𝔹 m x) λ b → selected b λ { refl → refl }
compute-names m (cond-select g a b out) =
  after (resolve𝔹 m g) λ active →
  after (resolve m a) λ x →
  after (resolve m b) λ y →
    guarded (typeof x ≟T typeof y) (one out (if active then x else y))
compute-names m i@(constrain-bits _ _) =
  selected (preprocess-bit-bounds i) (bounded-names m i)
compute-names m (constrain-eq a b) =
  after (resolve m a) λ x →
  after (resolve m b) λ y →
  after (constrainEq? x y) λ equal → selected equal λ { refl → refl }
compute-names m (constrain-to-boolean x) = after (resolve𝔹 m x) λ _ → λ { refl → refl }
compute-names m (copy x out) = after (resolve m x >>= copy-value) (one out)
compute-names m (impact _ _) ()
compute-names m (ec-mul a b out) =
  after (resolve m a) λ x → after (resolve m b) λ y → after (ec-mul-value x y) (one out)
compute-names m (ec-mul-generator x out) =
  after (resolve m x) λ v → after (ec-mul-generator-value v) (one out)
compute-names m (hash-to-curve ops out) =
  after (resolve-all-Fr m ops) λ xs → one out _
compute-names m (into-coordinates x (a , b)) =
  after (resolve m x) λ p → after (into-coordinates-value p) (pair a b)
compute-names m (from-coordinates (a , b) out) =
  after (resolve m a) λ x → after (resolve m b) λ y → after (from-coordinates-value x y) (one out)
compute-names m (into-bytes32 x out) =
  after (resolve m x >>= to-bytes-value) λ bs → guarded (length bs ≟ 32) (one out _)
compute-names m (from-bytes32 x t out) =
  after (resolve-bytes m x) λ bs →
    guarded (length bs ≟ 32) (after (from-bytes-value t bs) (one out))
compute-names m (reverse-bytes x out) = after (resolve-bytes m x) λ _ → one out _
compute-names m (bytes32-into-low-high x (lo , hi)) =
  after (resolve-bytes m x) λ bs →
    guarded (length bs ≟ 32) (many (lo ∷ hi ∷ []) (map val-native (pack-bytes bs)))
compute-names m (bytes32-from-low-high (lo , hi) out) =
  after (resolve m lo) λ l → after (resolve m hi) λ h →
  after (bytes32-from-parts l h) λ _ → one out _
compute-names m i@(div-mod-power-of-two _ _ _) =
  selected (preprocess-bit-bounds i) (bounded-names m i)
compute-names m i@(reconstitute-field _ _ _ _) =
  selected (preprocess-bit-bounds i) (bounded-names m i)
compute-names m (transient-hash ops out) =
  after (resolve-all-Fr m ops) λ _ → one out _
compute-names m (persistent-hash a ops out) =
  after (resolve-all-Fr m ops) λ xs →
  after (persistent-hash-fn a xs) λ _ → one out _
compute-names m (keccak256 a ops out) =
  after (resolve-all-Fr m ops) λ xs →
  after (keccak-fn a xs) λ _ → one out _
compute-names m (test-eq a b out) =
  after (resolve m a) λ x → after (resolve m b) λ y →
  after (valEq? x y) λ _ → one out _
compute-names m (add a b out) =
  after (resolve m a) λ x → after (resolve m b) λ y → after (add-value x y) (one out)
compute-names m (mul a b out) =
  after (resolve m a) λ x → after (resolve m b) λ y → after (mul-value x y) (one out)
compute-names m (neg x out) = after (resolve m x) λ v → after (neg-value v) (one out)
compute-names m (inv x out) = after (resolve m x) λ v → after (inv-value v) (one out)
compute-names m (not x out) = after (resolve𝔹 m x) λ _ → one out _
compute-names m (less-than a b bits out) =
  after (resolveᶠ m a) λ x → after (resolveᶠ m b) λ y →
  guarded (bits <? FR-BITS) (guarded (valFr x <? 2 ^ bits)
    (guarded (valFr y <? 2 ^ bits) (one out _)))
compute-names m (jubjub-scalar-from-native x out) =
  after (resolveᶠ m x) λ _ → one out _
compute-names m (public-input _ _ _) ()
compute-names m (private-input _ _ _) ()
compute-names m (circuit-output _) ()
compute-names m (slice x start len out) =
  after (resolve-bytes m x) λ bs → guarded (0 <? len)
    (guarded (start + len ≤? length bs) (one out _))
compute-names m (nth x index out) =
  after (resolve-bytes m x) λ bs → after (at bs index) λ _ → one out _
compute-names m (concat ops out) =
  after (resolve-concat m ops) λ bs → selected (valid-bytes-length (length bs)) (one out _)
compute-names m (reverse x out) = after (resolve-bytes m x) λ _ → one out _
compute-names m (load-constant t raw out) = after (decode t raw) (one out)
compute-names m (sha512 a ops out) =
  after (resolve-all-Fr m ops) λ xs → after (sha512-fn a xs) λ _ → one out _
compute-names m (and [] out) ()
compute-names m (and ops@(_ ∷ _) out) = after (resolve-typed-bools m ops) λ _ → one out _
compute-names m (or [] out) ()
compute-names m (or ops@(_ ∷ _) out) = after (resolve-typed-bools m ops) λ _ → one out _
compute-names m (xor [] out) ()
compute-names m (xor ops@(_ ∷ _) out) = after (resolve-typed-bools m ops) λ _ → one out _
compute-names m (to-bytes x out) =
  after (resolve m x >>= to-bytes-value) λ _ → one out _
compute-names m (from-bytes x t out) =
  after (resolve-bytes m x >>= from-bytes-value t) (one out)
compute-names m (bytes-into-natives x outs) =
  after (resolve-bytes m x) λ bs → many outs (map val-native (pack-bytes bs))
compute-names m (bytes-from-natives ops len out) =
  after (resolve-all-Fr m ops) λ xs → after (decode (bytes len) xs) (one out)
compute-names m (inner-proof _ _) ()
compute-names m (prepare-verification _ _ _ _ _) ()
compute-names m (accumulate _ _) ()
compute-names m (verify-accumulator _) ()
