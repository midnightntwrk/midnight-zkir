{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

------------------------------------------------------------------------
-- Encoding of typed values to raw Fr  (ir_instructions/encode.rs)
--
-- `encode`/`decode` are the wire format crossing every circuit boundary
-- (inputs, transcripts, outputs, commitment).  They are *derived* from
-- the per-type trust-base primitives rather than assumed, keeping them
-- out of the trusted surface; only the primitives they call are trusted.
------------------------------------------------------------------------

module zkir-v4.Encoding (⋯ : _) (open Assumptions ⋯) where

open import zkir-v4.Types ⋯

open import Data.Bool    using (Bool; true; false)
open import Data.List    using
  (List; []; _∷_; _++_; length; take; drop; concatMap)
open import Data.Maybe   using (Maybe; just; nothing; map; _>>=_)
open import Data.Nat     using (ℕ; zero; suc; _∸_; _⊓_; _≟_)
open import Data.Nat.DivMod using (_/_; _%_)
open import Data.Product using (_,_)
open import Data.Vec     using (toList; head)
  renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
import Data.Fin as Fin
import Data.List.Properties as ListP
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (isYes)

_≟LFr_ : DecidableEquality (List Fr)
_≟LFr_ = ListP.≡-dec _≟ᶠ_

low-bits : ℕ → ℕ → List Bool
low-bits zero    n = []
low-bits (suc k) n = isYes (n % 2 ≟ 1) ∷ low-bits k (n / 2)

-- Interprets arbitrary-length bytes as a little-endian integer, reducing
-- modulo the native field order.  Encoding uses this only on ≤31 bytes.
native-from-bytes : List Byte → Fr
native-from-bytes = λ bs → from-le-bits (concatMap (λ b → low-bits 8 (Fin.toℕ b)) bs)

pack-chunks : ℕ → List Byte → List Fr
pack-chunks zero    _  = []
pack-chunks (suc n) xs =
  native-from-bytes (take bytes-per-field xs) ∷
  pack-chunks n (drop bytes-per-field xs)

pack-bytes : List Byte → List Fr
pack-bytes bs = pack-chunks (bytes-encoded-len (length bs)) bs

unpack-bytes : ℕ → List Fr → Maybe (List Byte)
unpack-bytes zero    [] = just []
unpack-bytes (suc _) [] = nothing
unpack-bytes zero    (_ ∷ _) = nothing
unpack-bytes n@(suc _) (x ∷ xs) =
  let k = n ⊓ bytes-per-field in
  let chunk = take k (toList (nativeToBytes x)) in
  unpack-bytes (n ∸ bytes-per-field) xs >>= λ bs →
  just (chunk ++ bs)

encode-accumulator : Accumulator → List Fr
encode-accumulator (l , r) =
  toList (g1-to-fields l) ++ (1ᶠ ∷ toList (g1-to-fields r) ++ (1ᶠ ∷ []))

decode-accumulator : List Fr → Maybe Accumulator
decode-accumulator (a ∷ b ∷ c ∷ d ∷ e ∷ l ∷ f ∷ g ∷ h ∷ i ∷ j ∷ r ∷ [])
  with l ≟ᶠ 1ᶠ | r ≟ᶠ 1ᶠ
... | yes _ | yes _ =
  g1-from-fields (a ∷ᵛ b ∷ᵛ c ∷ᵛ d ∷ᵛ e ∷ᵛ []ᵛ) >>= λ lhs →
  g1-from-fields (f ∷ᵛ g ∷ᵛ h ∷ᵛ i ∷ᵛ j ∷ᵛ []ᵛ) >>= λ rhs →
  just (lhs , rhs)
... | _ | _ = nothing
decode-accumulator _ = nothing

------------------------------------------------------------------------
-- encode : flatten a typed value into raw field elements.
------------------------------------------------------------------------

encode : IrValue → List Fr
encode (val-native x)        = x ∷ []
encode (val-jubjub-scalar s) = jubjubScalarToFr s ∷ []
encode (val-bool true)       = 1ᶠ ∷ []
encode (val-bool false)      = 0ᶠ ∷ []
encode (val-byte b)          = native-from-bytes (b ∷ []) ∷ []
encode (val-bytes bs)        = pack-bytes bs
encode (val-accumulator acc) = encode-accumulator acc
encode (val-jubjub-point p)  = let (x , y)   = coordsJ p          in x  ∷ y  ∷ []
encode (val-secp256k1-base x)     = let (l , h) = secp256k1Base→limbs x   in l ∷ h ∷ []
encode (val-secp256k1-scalar s)   = let (l , h) = secp256k1Scalar→limbs s in l ∷ h ∷ []
encode (val-secp256k1-point p)    =
  let (a , b , c , d , e) = secp256k1Point→limbs p in a ∷ b ∷ c ∷ d ∷ e ∷ []
encode (val-secp256r1-base x)   =
  let (l , h) = secp256r1Base→limbs x   in l ∷ h ∷ []
encode (val-secp256r1-scalar s) =
  let (l , h) = secp256r1Scalar→limbs s in l ∷ h ∷ []
encode (val-secp256r1-point p)  =
  let (a , b , c , d , e) = secp256r1Point→limbs p in a ∷ b ∷ c ∷ d ∷ e ∷ []
encode (val-curve25519-base x)   =
  let (l , h) = curve25519Base→limbs x   in l ∷ h ∷ []
encode (val-curve25519-scalar s) =
  let (l , h) = curve25519Scalar→limbs s in l ∷ h ∷ []
encode (val-curve25519-point p)  =
  let (a , b , c , d) = curve25519Point→limbs p in a ∷ b ∷ c ∷ d ∷ []

------------------------------------------------------------------------
-- decode : read raw field elements as a value of the given type.
-- Partial: the wrong number of elements, or an invalid encoding (a
-- non-subgroup point, a noncanonical byte chunk or scalar), yields `nothing`.
------------------------------------------------------------------------

decode-candidate : IrType → List Fr → Maybe IrValue
decode-candidate native        (x ∷ [])       = just (val-native x)
decode-candidate jubjub-scalar (s ∷ [])       = map val-jubjub-scalar (jubjubScalarFromFr s)
decode-candidate bool (x ∷ []) with x ≟ᶠ 0ᶠ | x ≟ᶠ 1ᶠ
... | yes _ | _ = just (val-bool false)
... | no _  | yes _ = just (val-bool true)
... | no _  | no _  = nothing
decode-candidate byte (x ∷ []) = just (val-byte (head (nativeToBytes x)))
decode-candidate (bytes n) raw = map val-bytes (unpack-bytes n raw)
decode-candidate accumulator raw = map val-accumulator (decode-accumulator raw)
decode-candidate jubjub-point  (x ∷ y ∷ [])   = map val-jubjub-point  (fromCoordsJ x y)
decode-candidate secp256k1-base     (l ∷ h ∷ [])   = map val-secp256k1-base     (limbs→secp256k1Base l h)
decode-candidate secp256k1-scalar   (l ∷ h ∷ [])   = map val-secp256k1-scalar   (limbs→secp256k1Scalar l h)
decode-candidate secp256k1-point    (a ∷ b ∷ c ∷ d ∷ e ∷ []) =
  map val-secp256k1-point (limbs→secp256k1Point a b c d e)
decode-candidate secp256r1-base   (l ∷ h ∷ []) =
  map val-secp256r1-base   (limbs→secp256r1Base l h)
decode-candidate secp256r1-scalar (l ∷ h ∷ []) =
  map val-secp256r1-scalar (limbs→secp256r1Scalar l h)
decode-candidate secp256r1-point  (a ∷ b ∷ c ∷ d ∷ e ∷ []) =
  map val-secp256r1-point (limbs→secp256r1Point a b c d e)
decode-candidate curve25519-base   (l ∷ h ∷ []) =
  map val-curve25519-base   (limbs→curve25519Base l h)
decode-candidate curve25519-scalar (l ∷ h ∷ []) =
  map val-curve25519-scalar (limbs→curve25519Scalar l h)
decode-candidate curve25519-point  (a ∷ b ∷ c ∷ d ∷ []) =
  map val-curve25519-point (limbs→curve25519Point a b c d)
decode-candidate _             _              = nothing

-- Every candidate decoder is followed by re-encoding, as in
-- decode_offcircuit.  For Bytes, this rejects non-zero high bytes of
-- each native field element, including those beyond the short final chunk.
canonical : List Fr → IrValue → Maybe IrValue
canonical raw v with raw ≟LFr encode v
... | yes _ = just v
... | no _ = nothing

decode : IrType → List Fr → Maybe IrValue
decode t raw with valid-type t
... | false = nothing
... | true = decode-candidate t raw >>= canonical raw
