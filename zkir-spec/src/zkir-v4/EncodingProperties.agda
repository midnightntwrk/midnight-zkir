{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.EncodingProperties (⋯ : _) (open Assumptions ⋯) where

open import zkir-v4.Encoding ⋯
open import zkir-v4.Types ⋯

open import Data.Bool using (true; false)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _++_; length; take; drop)
import Data.List.Properties as ListP
open import Data.Maybe using (Maybe; just; nothing; map; _>>=_)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _⊓_; _≤_; _≤?_; z≤n; s≤s)
open import Data.Nat.DivMod using (_/_; m/n≡1+[m∸n]/n; m<n⇒m/n≡0)
import Data.Nat.Properties as NatP
open import Data.Product using (Σ; _×_; _,_; uncurry)
open import Data.Vec using (toList; head)
  renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
import Data.Vec.Properties as VecP
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; subst)
open import Relation.Nullary using (yes; no)

-- The existing Assumptions record supplies round-trips for the
-- inherited field and curve codecs. These two additions concern the
-- new primitive encodings only, not typed values or byte-string packing.
record EncodingLaws : Set where
  field
    byte-chunk-round : ∀ bs → length bs ≤ bytes-per-field
      → take (length bs) (toList (nativeToBytes (native-from-bytes bs))) ≡ bs
    g1-fields-round : ∀ p → g1-from-fields (g1-to-fields p) ≡ just p

private
  bind-evidence : ∀ {A B : Set} (m : Maybe A) (f : A → Maybe B) {y}
    → (m >>= f) ≡ just y → Σ A (λ x → (m ≡ just x) × (f x ≡ just y))
  bind-evidence nothing _ ()
  bind-evidence (just x) _ eq = x , refl , eq

  canonical-sound : ∀ raw v {result}
    → canonical raw v ≡ just result → encode result ≡ raw
  canonical-sound raw v eq with raw ≟LFr encode v
  ... | yes raw-eq = trans (cong encode (sym (just-injective eq))) (sym raw-eq)
  ... | no _ with eq
  ...   | ()

  canonical-round : ∀ v → canonical (encode v) v ≡ just v
  canonical-round v with encode v ≟LFr encode v
  ... | yes _ = refl
  ... | no ne = ⊥-elim (ne refl)

  pack-chunks-width : ∀ k bs → length (pack-chunks k bs) ≡ k
  pack-chunks-width zero _ = refl
  pack-chunks-width (suc k) bs = cong suc (pack-chunks-width k (drop bytes-per-field bs))

  chunk-count-suc : ∀ n
    → bytes-encoded-len (suc n) ≡ suc (bytes-encoded-len (suc n ∸ bytes-per-field))
  chunk-count-suc n with bytes-per-field ≤? suc n
  ... | yes le =
    trans (m/n≡1+[m∸n]/n {m = suc n + 30} {n = 31}
            (NatP.≤-trans le (NatP.m≤m+n (suc n) 30)))
          (cong (λ q → suc (q / 31)) (NatP.+-∸-comm 30 le))
  ... | no lt
    rewrite NatP.m≤n⇒m∸n≡0 (NatP.<⇒≤ (NatP.≰⇒> lt))
          =
    trans (cong (_/ 31) (NatP.+-comm (suc n) 30))
      (trans (m/n≡1+[m∸n]/n {m = 31 + n} {n = 31} (NatP.m≤m+n 31 n))
        (cong suc (trans (cong (_/ 31) (NatP.m+n∸m≡n 31 n))
          (m<n⇒m/n≡0 {m = n} {n = 31}
            (NatP.≤-<-trans (NatP.n≤1+n n) (NatP.≰⇒> lt))))))

  unpack-length : ∀ n raw {bs} → unpack-bytes n raw ≡ just bs → length bs ≡ n
  unpack-length zero [] refl = refl
  unpack-length zero (_ ∷ _) ()
  unpack-length (suc n) [] ()
  unpack-length (suc n) (f ∷ raw) eq
    with bind-evidence (unpack-bytes (suc n ∸ bytes-per-field) raw)
                       (λ xs → just (take (suc n ⊓ bytes-per-field) (toList (nativeToBytes f)) ++ xs))
                       eq
  ... | rest , rest-ok , refl =
    trans (ListP.length-++ (take k (toList (nativeToBytes f))) {ys = rest})
      (trans (cong₂ _+_ local-length (unpack-length (suc n ∸ bytes-per-field) raw rest-ok))
             (trans (cong (_+ (suc n ∸ bytes-per-field)) (NatP.⊓-comm (suc n) bytes-per-field))
                    (NatP.m⊓n+n∸m≡n bytes-per-field (suc n))))
    where
    k = suc n ⊓ bytes-per-field
    local-length : length (take k (toList (nativeToBytes f))) ≡ k
    local-length = trans (ListP.length-take k (toList (nativeToBytes f)))
      (trans (cong (k ⊓_) (VecP.length-toList (nativeToBytes f)))
             (NatP.m≤n⇒m⊓n≡m (NatP.≤-trans (NatP.m⊓n≤n (suc n) 31) (NatP.n≤1+n 31))))

-- The re-encoding test alone proves canonicity of accepted inputs.
decode-encode-sound : ∀ {t raw v} → decode t raw ≡ just v → encode v ≡ raw
decode-encode-sound {t} {raw} eq with valid-type t
... | false with eq
...   | ()
decode-encode-sound {t} {raw} eq | true
  with bind-evidence (decode-candidate t raw) (canonical raw) eq
... | candidate , _ , canon = canonical-sound raw candidate canon

encode-width : ∀ v → length (encode v) ≡ encoded-len (typeof v)
encode-width (val-native _) = refl
encode-width (val-jubjub-scalar _) = refl
encode-width (val-bool true) = refl
encode-width (val-bool false) = refl
encode-width (val-byte _) = refl
encode-width (val-bytes bs) = pack-chunks-width (bytes-encoded-len (length bs)) bs
encode-width (val-accumulator (l , r)) with g1-to-fields l | g1-to-fields r
... | _ ∷ᵛ _ ∷ᵛ _ ∷ᵛ _ ∷ᵛ _ ∷ᵛ []ᵛ | _ ∷ᵛ _ ∷ᵛ _ ∷ᵛ _ ∷ᵛ _ ∷ᵛ []ᵛ = refl
encode-width (val-jubjub-point p) with coordsJ p
... | _ , _ = refl
encode-width (val-secp256k1-base x) with secp256k1Base→limbs x
... | _ , _ = refl
encode-width (val-secp256k1-scalar x) with secp256k1Scalar→limbs x
... | _ , _ = refl
encode-width (val-secp256k1-point p) with secp256k1Point→limbs p
... | _ , _ , _ , _ , _ = refl
encode-width (val-secp256r1-base x) with secp256r1Base→limbs x
... | _ , _ = refl
encode-width (val-secp256r1-scalar x) with secp256r1Scalar→limbs x
... | _ , _ = refl
encode-width (val-secp256r1-point p) with secp256r1Point→limbs p
... | _ , _ , _ , _ , _ = refl
encode-width (val-curve25519-base x) with curve25519Base→limbs x
... | _ , _ = refl
encode-width (val-curve25519-scalar x) with curve25519Scalar→limbs x
... | _ , _ = refl
encode-width (val-curve25519-point p) with curve25519Point→limbs p
... | _ , _ , _ , _ = refl

private
  map-evidence : ∀ {A B : Set} {f : A → B} (m : Maybe A) {v}
    → map f m ≡ just v → Σ A (λ x → (m ≡ just x) × (f x ≡ v))
  map-evidence nothing ()
  map-evidence (just x) eq = x , refl , just-injective eq

  candidate-type : ∀ t raw {v} → decode-candidate t raw ≡ just v → typeof v ≡ t
  candidate-type (bytes n) raw eq with map-evidence {f = val-bytes} (unpack-bytes n raw) eq
  ... | _ , unpacked , refl = cong bytes (unpack-length n raw unpacked)
  candidate-type accumulator raw eq
    with map-evidence {f = val-accumulator} (decode-accumulator raw) eq
  ... | _ , _ , refl = refl
  candidate-type bool [] ()
  candidate-type bool (_ ∷ _ ∷ _) ()
  candidate-type bool (f ∷ []) eq with f ≟ᶠ 0ᶠ | f ≟ᶠ 1ᶠ
  ... | yes _ | _ = cong typeof (sym (just-injective eq))
  ... | no _ | yes _ = cong typeof (sym (just-injective eq))
  ... | no _ | no _ with eq
  ...   | ()
  candidate-type native [] ()
  candidate-type native (_ ∷ _ ∷ _) ()
  candidate-type native (a ∷ []) eq = cong typeof (sym (just-injective eq))
  candidate-type byte [] ()
  candidate-type byte (_ ∷ _ ∷ _) ()
  candidate-type byte (a ∷ []) eq = cong typeof (sym (just-injective eq))
  candidate-type jubjub-scalar [] ()
  candidate-type jubjub-scalar (_ ∷ _ ∷ _) ()
  candidate-type jubjub-scalar (a ∷ []) eq
    with map-evidence {f = val-jubjub-scalar} (jubjubScalarFromFr a) eq
  ... | _ , _ , refl = refl
  candidate-type jubjub-point [] ()
  candidate-type jubjub-point (_ ∷ []) ()
  candidate-type jubjub-point (_ ∷ _ ∷ _ ∷ _) ()
  candidate-type jubjub-point (a ∷ b ∷ []) eq
    with map-evidence {f = val-jubjub-point} (fromCoordsJ a b) eq
  ... | _ , _ , refl = refl
  candidate-type secp256k1-base [] ()
  candidate-type secp256k1-base (_ ∷ []) ()
  candidate-type secp256k1-base (_ ∷ _ ∷ _ ∷ _) ()
  candidate-type secp256k1-base (a ∷ b ∷ []) eq
    with map-evidence {f = val-secp256k1-base} (limbs→secp256k1Base a b) eq
  ... | _ , _ , refl = refl
  candidate-type secp256k1-scalar [] ()
  candidate-type secp256k1-scalar (_ ∷ []) ()
  candidate-type secp256k1-scalar (_ ∷ _ ∷ _ ∷ _) ()
  candidate-type secp256k1-scalar (a ∷ b ∷ []) eq
    with map-evidence {f = val-secp256k1-scalar} (limbs→secp256k1Scalar a b) eq
  ... | _ , _ , refl = refl
  candidate-type secp256k1-point [] ()
  candidate-type secp256k1-point (_ ∷ []) ()
  candidate-type secp256k1-point (_ ∷ _ ∷ []) ()
  candidate-type secp256k1-point (_ ∷ _ ∷ _ ∷ []) ()
  candidate-type secp256k1-point (_ ∷ _ ∷ _ ∷ _ ∷ []) ()
  candidate-type secp256k1-point (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _) ()
  candidate-type secp256k1-point (a ∷ b ∷ c ∷ d ∷ e ∷ []) eq
    with map-evidence {f = val-secp256k1-point} (limbs→secp256k1Point a b c d e) eq
  ... | _ , _ , refl = refl
  candidate-type secp256r1-base [] ()
  candidate-type secp256r1-base (_ ∷ []) ()
  candidate-type secp256r1-base (_ ∷ _ ∷ _ ∷ _) ()
  candidate-type secp256r1-base (a ∷ b ∷ []) eq
    with map-evidence {f = val-secp256r1-base} (limbs→secp256r1Base a b) eq
  ... | _ , _ , refl = refl
  candidate-type secp256r1-scalar [] ()
  candidate-type secp256r1-scalar (_ ∷ []) ()
  candidate-type secp256r1-scalar (_ ∷ _ ∷ _ ∷ _) ()
  candidate-type secp256r1-scalar (a ∷ b ∷ []) eq
    with map-evidence {f = val-secp256r1-scalar} (limbs→secp256r1Scalar a b) eq
  ... | _ , _ , refl = refl
  candidate-type secp256r1-point [] ()
  candidate-type secp256r1-point (_ ∷ []) ()
  candidate-type secp256r1-point (_ ∷ _ ∷ []) ()
  candidate-type secp256r1-point (_ ∷ _ ∷ _ ∷ []) ()
  candidate-type secp256r1-point (_ ∷ _ ∷ _ ∷ _ ∷ []) ()
  candidate-type secp256r1-point (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _) ()
  candidate-type secp256r1-point (a ∷ b ∷ c ∷ d ∷ e ∷ []) eq
    with map-evidence {f = val-secp256r1-point} (limbs→secp256r1Point a b c d e) eq
  ... | _ , _ , refl = refl
  candidate-type curve25519-base [] ()
  candidate-type curve25519-base (_ ∷ []) ()
  candidate-type curve25519-base (_ ∷ _ ∷ _ ∷ _) ()
  candidate-type curve25519-base (a ∷ b ∷ []) eq
    with map-evidence {f = val-curve25519-base} (limbs→curve25519Base a b) eq
  ... | _ , _ , refl = refl
  candidate-type curve25519-scalar [] ()
  candidate-type curve25519-scalar (_ ∷ []) ()
  candidate-type curve25519-scalar (_ ∷ _ ∷ _ ∷ _) ()
  candidate-type curve25519-scalar (a ∷ b ∷ []) eq
    with map-evidence {f = val-curve25519-scalar} (limbs→curve25519Scalar a b) eq
  ... | _ , _ , refl = refl
  candidate-type curve25519-point [] ()
  candidate-type curve25519-point (_ ∷ []) ()
  candidate-type curve25519-point (_ ∷ _ ∷ []) ()
  candidate-type curve25519-point (_ ∷ _ ∷ _ ∷ []) ()
  candidate-type curve25519-point (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _) ()
  candidate-type curve25519-point (a ∷ b ∷ c ∷ d ∷ []) eq
    with map-evidence {f = val-curve25519-point} (limbs→curve25519Point a b c d) eq
  ... | _ , _ , refl = refl

decode-typed : ∀ {t raw v} → decode t raw ≡ just v → typeof v ≡ t
decode-typed {t} {raw} eq with valid-type t
... | false with eq
...   | ()
decode-typed {t} {raw} eq | true
  with bind-evidence (decode-candidate t raw) (canonical raw) eq
... | candidate , found , canon with raw ≟LFr encode candidate
...   | yes _ = trans (cong typeof (sym (just-injective canon))) (candidate-type t raw found)
...   | no _ with canon
...     | ()

take-encode : ∀ v rest → take (encoded-len (typeof v)) (encode v ++ rest) ≡ encode v
take-encode v rest rewrite sym (encode-width v) = go (encode v) rest
  where
  go : ∀ (xs ys : List Fr) → take (length xs) (xs ++ ys) ≡ xs
  go [] ys = refl
  go (x ∷ xs) ys = cong (x ∷_) (go xs ys)

drop-encode : ∀ v rest → drop (encoded-len (typeof v)) (encode v ++ rest) ≡ rest
drop-encode v rest rewrite sym (encode-width v) = go (encode v) rest
  where
  go : ∀ (xs ys : List Fr) → drop (length xs) (xs ++ ys) ≡ ys
  go [] ys = refl
  go (_ ∷ xs) ys = go xs ys

private
  unpack-round : EncodingLaws → ∀ k bs → bytes-encoded-len (length bs) ≡ k
    → unpack-bytes (length bs) (pack-chunks k bs) ≡ just bs
  unpack-round laws zero [] _ = refl
  unpack-round laws zero (b ∷ bs) count
    with trans (sym (chunk-count-suc (length bs))) count
  ... | ()
  unpack-round laws (suc k) [] ()
  unpack-round laws (suc k) (b ∷ bs) count = proof
    where
    chunk-source = b ∷ bs
    prefix = take bytes-per-field chunk-source
    rest = drop bytes-per-field chunk-source
    rest-count : bytes-encoded-len (length rest) ≡ k
    rest-count = NatP.suc-injective
      (trans (cong (λ n → suc (bytes-encoded-len n)) (ListP.length-drop bytes-per-field chunk-source))
        (trans (sym (chunk-count-suc (length bs))) count))
    prefix-fits : length prefix ≤ bytes-per-field
    prefix-fits = NatP.≤-trans
      (NatP.≤-reflexive (ListP.length-take bytes-per-field chunk-source))
      (NatP.m⊓n≤m bytes-per-field (length chunk-source))

    proof : unpack-bytes (length chunk-source) (pack-chunks (suc k) chunk-source) ≡ just chunk-source
    proof
      rewrite sym (ListP.length-drop bytes-per-field chunk-source)
            | unpack-round laws k rest rest-count
            | sym (NatP.⊓-comm bytes-per-field (length chunk-source))
            | sym (ListP.length-take bytes-per-field chunk-source)
            | EncodingLaws.byte-chunk-round laws prefix prefix-fits
            | ListP.take++drop≡id bytes-per-field chunk-source = refl

  just-map : ∀ {A B : Set} (f : A → B) {m x}
    → m ≡ just x → map f m ≡ just (f x)
  just-map _ refl = refl

  byte-candidate-round : EncodingLaws → ∀ b
    → decode-candidate byte (encode (val-byte b)) ≡ just (val-byte b)
  byte-candidate-round laws b
    with nativeToBytes (native-from-bytes (b ∷ []))
       | EncodingLaws.byte-chunk-round laws (b ∷ []) (s≤s z≤n)
  ... | b′ ∷ᵛ tail | eq =
    cong (λ x → just (val-byte x)) (ListP.∷-injectiveˡ eq)

  accumulator-candidate-round : EncodingLaws → ∀ l r
    → decode-candidate accumulator (encode (val-accumulator (l , r))) ≡ just (val-accumulator (l , r))
  accumulator-candidate-round laws l r with g1-to-fields l in left | g1-to-fields r in right
  ... | a ∷ᵛ b ∷ᵛ c ∷ᵛ d ∷ᵛ e ∷ᵛ []ᵛ | f ∷ᵛ g ∷ᵛ h ∷ᵛ i ∷ᵛ j ∷ᵛ []ᵛ
    with 1ᶠ ≟ᶠ 1ᶠ
  ... | no ne = ⊥-elim (ne refl)
  ... | yes _
    rewrite trans (cong g1-from-fields (sym left)) (EncodingLaws.g1-fields-round laws l)
          | trans (cong g1-from-fields (sym right)) (EncodingLaws.g1-fields-round laws r) = refl

  candidate-round : EncodingLaws → ∀ v → decode-candidate (typeof v) (encode v) ≡ just v
  candidate-round laws (val-native f) = refl
  candidate-round laws (val-bool false) with 0ᶠ ≟ᶠ 0ᶠ | 0ᶠ ≟ᶠ 1ᶠ
  ... | yes _ | _ = refl
  ... | no ne | _ = ⊥-elim (ne refl)
  candidate-round laws (val-bool true) with 1ᶠ ≟ᶠ 0ᶠ | 1ᶠ ≟ᶠ 1ᶠ
  ... | yes e | _ = ⊥-elim (1ᶠ≢0ᶠ e)
  ... | no _ | yes _ = refl
  ... | no _ | no ne = ⊥-elim (ne refl)
  candidate-round laws (val-byte b) = byte-candidate-round laws b
  candidate-round laws (val-bytes bs) =
    just-map val-bytes (unpack-round laws (bytes-encoded-len (length bs)) bs refl)
  candidate-round laws (val-accumulator (l , r)) = accumulator-candidate-round laws l r
  candidate-round laws (val-jubjub-scalar s) = just-map val-jubjub-scalar (jubjubScalar-round s)
  candidate-round laws (val-jubjub-point p) with coordsJ p in eq
  ... | x , y = just-map val-jubjub-point
    (trans (cong (uncurry fromCoordsJ) (sym eq)) (coordsJ-fromCoordsJ p))
  candidate-round laws (val-secp256k1-base x) with secp256k1Base→limbs x in eq
  ... | l , h = just-map val-secp256k1-base
    (trans (cong (uncurry limbs→secp256k1Base) (sym eq)) (secp256k1Base-round x))
  candidate-round laws (val-secp256k1-scalar x) with secp256k1Scalar→limbs x in eq
  ... | l , h = just-map val-secp256k1-scalar
    (trans (cong (uncurry limbs→secp256k1Scalar) (sym eq)) (secp256k1Scalar-round x))
  candidate-round laws (val-secp256k1-point p) with secp256k1Point→limbs p in eq
  ... | a , b , c , d , e = just-map val-secp256k1-point (secp256k1Point-round eq)
  candidate-round laws (val-secp256r1-base x) with secp256r1Base→limbs x in eq
  ... | l , h = just-map val-secp256r1-base
    (trans (cong (uncurry limbs→secp256r1Base) (sym eq)) (secp256r1Base-round x))
  candidate-round laws (val-secp256r1-scalar x) with secp256r1Scalar→limbs x in eq
  ... | l , h = just-map val-secp256r1-scalar
    (trans (cong (uncurry limbs→secp256r1Scalar) (sym eq)) (secp256r1Scalar-round x))
  candidate-round laws (val-secp256r1-point p) with secp256r1Point→limbs p in eq
  ... | a , b , c , d , e = just-map val-secp256r1-point (secp256r1Point-round eq)
  candidate-round laws (val-curve25519-base x) with curve25519Base→limbs x in eq
  ... | l , h = just-map val-curve25519-base
    (trans (cong (uncurry limbs→curve25519Base) (sym eq)) (curve25519Base-round x))
  candidate-round laws (val-curve25519-scalar x) with curve25519Scalar→limbs x in eq
  ... | l , h = just-map val-curve25519-scalar
    (trans (cong (uncurry limbs→curve25519Scalar) (sym eq)) (curve25519Scalar-round x))
  candidate-round laws (val-curve25519-point p) with curve25519Point→limbs p in eq
  ... | a , b , c , d = just-map val-curve25519-point (curve25519Point-round eq)

encode-decode : EncodingLaws → ∀ v → valid-type (typeof v) ≡ true
  → decode (typeof v) (encode v) ≡ just v
encode-decode laws v admissible
  rewrite admissible | candidate-round laws v = canonical-round v

decode-admissible : ∀ {t raw v} → decode t raw ≡ just v → valid-type t ≡ true
decode-admissible {t} eq with valid-type t
... | true = refl
... | false with eq
...   | ()
