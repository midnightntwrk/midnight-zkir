{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.InputProperties (⋯ : _) (open Assumptions ⋯) where

open import zkir-v4.Encoding ⋯ using (decode; encode)
open import zkir-v4.EncodingProperties ⋯
open import zkir-v4.Operations ⋯ using (Mem; ∅; ins)
open import zkir-v4.Semantics ⋯ using (decode-inputs; decode-inputs-from)
open import zkir-v4.Syntax ⋯ using (TypedIdentifier)
open import zkir-v4.Types ⋯

open import Data.Bool using (true)
open import Data.List using (List; []; _∷_; _++_; take; drop)
open import Data.List.Properties using (take++drop≡id)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)

-- A pointwise, ordered correspondence between input declarations and values.
-- The input names may repeat here. The memory function follows the Rust
-- insertion order, while these values retain the original declaration order.
data DeclaredValues : List TypedIdentifier → Set where
  []ᵈ : DeclaredValues []
  _∷ᵈ_ : ∀ {ti rest} (v : IrValue)
    → (typeof v ≡ TypedIdentifier.val-t ti) × (valid-type (typeof v) ≡ true) × DeclaredValues rest
    → DeclaredValues (ti ∷ rest)

declared-raw : ∀ {declarations} → DeclaredValues declarations → List Fr
declared-raw []ᵈ = []
declared-raw (v ∷ᵈ (_ , _ , values)) = encode v ++ declared-raw values

install-declared : ∀ {declarations} → Mem → DeclaredValues declarations → Mem
install-declared m []ᵈ = m
install-declared m (_∷ᵈ_ {ti = ti} v (_ , _ , values)) =
  install-declared (ins (TypedIdentifier.name ti) v m) values

private
  bind-evidence : ∀ {A B : Set} (m : Maybe A) (f : A → Maybe B) {y}
    → (m >>= f) ≡ just y → Σ A (λ x → (m ≡ just x) × (f x ≡ just y))
  bind-evidence nothing _ ()
  bind-evidence (just x) _ eq = x , refl , eq

decode-inputs-from-sound : ∀ m declarations raw {out}
  → decode-inputs-from m declarations raw ≡ just out
  → Σ (DeclaredValues declarations) λ values →
      (declared-raw values ≡ raw) × (install-declared m values ≡ out)
decode-inputs-from-sound m [] [] ok = []ᵈ , refl , just-injective ok
decode-inputs-from-sound _ [] (_ ∷ _) ()
decode-inputs-from-sound m (ti ∷ tis) raw ok
  with bind-evidence (decode t (take n raw))
         (λ v → decode-inputs-from (ins (TypedIdentifier.name ti) v m) tis (drop n raw))
         ok
  where
  t = TypedIdentifier.val-t ti
  n = encoded-len t
... | v , decoded , continued
  with decode-inputs-from-sound (ins (TypedIdentifier.name ti) v m) tis
         (drop (encoded-len (TypedIdentifier.val-t ti)) raw) continued
...   | values , raw-rest , memory-ok =
  (v ∷ᵈ (typed , admissible , values)) , raw-ok , memory-ok
  where
  t = TypedIdentifier.val-t ti
  n = encoded-len t
  typed : typeof v ≡ t
  typed = decode-typed decoded
  admissible : valid-type (typeof v) ≡ true
  admissible = trans (cong valid-type typed) (decode-admissible {t = t} {raw = take n raw} decoded)
  raw-ok : encode v ++ declared-raw values ≡ raw
  raw-ok = trans (cong (encode v ++_) raw-rest)
    (trans (cong (_++ drop n raw) (decode-encode-sound {t = t} decoded)) (take++drop≡id n raw))

decode-inputs-sound : ∀ declarations raw {out}
  → decode-inputs declarations raw ≡ just out
  → Σ (DeclaredValues declarations) λ values →
      (declared-raw values ≡ raw) × (install-declared ∅ values ≡ out)
decode-inputs-sound = decode-inputs-from-sound ∅

decode-inputs-from-round : EncodingLaws → ∀ m {declarations} (values : DeclaredValues declarations)
  → decode-inputs-from m declarations (declared-raw values) ≡ just (install-declared m values)
decode-inputs-from-round _ m []ᵈ = refl
decode-inputs-from-round laws m (_∷ᵈ_ {ti = ti} v (typed , admissible , values))
  rewrite sym typed
        | take-encode v (declared-raw values)
        | encode-decode laws v admissible
        | drop-encode v (declared-raw values) =
  decode-inputs-from-round laws (ins (TypedIdentifier.name ti) v m) values

decode-inputs-round : EncodingLaws → ∀ {declarations} (values : DeclaredValues declarations)
  → decode-inputs declarations (declared-raw values) ≡ just (install-declared ∅ values)
decode-inputs-round laws = decode-inputs-from-round laws ∅
