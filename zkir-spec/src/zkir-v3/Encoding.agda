{-# OPTIONS --safe #-}
open import zkir-v3.Assumptions

------------------------------------------------------------------------
-- Encoding of typed values to raw Fr  (ir_instructions/encode.rs)
--
-- `encode`/`decode` are the wire format crossing every circuit boundary
-- (inputs, transcripts, outputs, commitment).  They are *derived* from
-- the per-type trust-base primitives rather than assumed, keeping them
-- out of the trusted surface; only the primitives they call are trusted.
------------------------------------------------------------------------

module zkir-v3.Encoding (⋯ : _) (open Assumptions ⋯) where

open import zkir-v3.Types ⋯

open import Data.List    using (List; []; _∷_)
open import Data.Maybe   using (Maybe; just; nothing; map)
open import Data.Product using (_,_)

------------------------------------------------------------------------
-- encode : flatten a typed value into raw field elements.
------------------------------------------------------------------------

encode : IrValue → List Fr
encode (val-native x)        = x ∷ []
encode (val-jubjub-scalar s) = jubjubScalarToFr s ∷ []
encode (val-bytes32 b)       = let (lo , hi) = bytes32→low-high b in lo ∷ hi ∷ []
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
-- non-subgroup point, a non-canonical Bytes32/scalar), yields `nothing`.
------------------------------------------------------------------------

decode : IrType → List Fr → Maybe IrValue
decode native        (x ∷ [])       = just (val-native x)
decode jubjub-scalar (s ∷ [])       = map val-jubjub-scalar (jubjubScalarFromFr s)
decode bytes32       (lo ∷ hi ∷ []) = map val-bytes32       (low-high→bytes32 lo hi)
decode jubjub-point  (x ∷ y ∷ [])   = map val-jubjub-point  (fromCoordsJ x y)
decode secp256k1-base     (l ∷ h ∷ [])   = map val-secp256k1-base     (limbs→secp256k1Base l h)
decode secp256k1-scalar   (l ∷ h ∷ [])   = map val-secp256k1-scalar   (limbs→secp256k1Scalar l h)
decode secp256k1-point    (a ∷ b ∷ c ∷ d ∷ e ∷ []) =
  map val-secp256k1-point (limbs→secp256k1Point a b c d e)
decode secp256r1-base   (l ∷ h ∷ []) =
  map val-secp256r1-base   (limbs→secp256r1Base l h)
decode secp256r1-scalar (l ∷ h ∷ []) =
  map val-secp256r1-scalar (limbs→secp256r1Scalar l h)
decode secp256r1-point  (a ∷ b ∷ c ∷ d ∷ e ∷ []) =
  map val-secp256r1-point (limbs→secp256r1Point a b c d e)
decode curve25519-base   (l ∷ h ∷ []) =
  map val-curve25519-base   (limbs→curve25519Base l h)
decode curve25519-scalar (l ∷ h ∷ []) =
  map val-curve25519-scalar (limbs→curve25519Scalar l h)
decode curve25519-point  (a ∷ b ∷ c ∷ d ∷ []) =
  map val-curve25519-point (limbs→curve25519Point a b c d)
decode _             _              = nothing
