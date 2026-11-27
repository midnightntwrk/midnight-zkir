{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

------------------------------------------------------------------------
-- Types and values of zkir-v4  (ir_types.rs)
--
-- The IR's type set, the off-circuit value domain `IrValue`, the
-- per-type encoding width, and the value→type and default-value maps.
------------------------------------------------------------------------

module zkir-v4.Types (⋯ : _) (open Assumptions ⋯) where

open import Data.Bool using (Bool; true; _∧_)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; length)
open import Data.Vec using (toList)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _+_; _∸_; _^_; _≤?_; _≟_)
open import Data.Nat.DivMod using (_/_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (isYes)

------------------------------------------------------------------------
-- Types  (ir_types.rs: IrType)
------------------------------------------------------------------------

data IrType : Set where
  native            : IrType   -- Scalar<BLS12-381>
  bytes             : ℕ → IrType
  byte bool         : IrType
  accumulator       : IrType
  jubjub-point      : IrType   -- Point<Jubjub>
  jubjub-scalar     : IrType   -- Scalar<Jubjub>
  secp256k1-point        : IrType   -- Point<Secp256k1>
  secp256k1-base         : IrType   -- Base<Secp256k1>
  secp256k1-scalar       : IrType   -- Scalar<Secp256k1>
  secp256r1-point   : IrType   -- Point<Secp256r1>
  secp256r1-base    : IrType   -- Base<Secp256r1>
  secp256r1-scalar  : IrType   -- Scalar<Secp256r1>
  curve25519-point  : IrType   -- Point<Curve25519>
  curve25519-base   : IrType   -- Base<Curve25519>
  curve25519-scalar : IrType   -- Scalar<Curve25519>

bytes32 : IrType
bytes32 = bytes 32

max-bytes-len : ℕ
max-bytes-len = 2 ^ 24

valid-bytes-length : ℕ → Bool
valid-bytes-length n = isYes (1 ≤? n) ∧ isYes (n ≤? max-bytes-len)

valid-type : IrType → Bool
valid-type (bytes n) = valid-bytes-length n
valid-type _ = true

bytes-per-field : ℕ
bytes-per-field = 31

bytes-encoded-len : ℕ → ℕ
bytes-encoded-len n = (n + 30) / 31

-- Number of raw Fr elements needed to encode a value of this type
-- (ir_types.rs: IrType::encoded_len).
encoded-len : IrType → ℕ
encoded-len native            = 1
encoded-len (bytes n)         = bytes-encoded-len n
encoded-len byte              = 1
encoded-len bool              = 1
encoded-len accumulator       = 12
encoded-len jubjub-point      = 2
encoded-len jubjub-scalar     = 1
encoded-len secp256k1-point        = 5
encoded-len secp256k1-base         = 2
encoded-len secp256k1-scalar       = 2
encoded-len secp256r1-point   = 5
encoded-len secp256r1-base    = 2
encoded-len secp256r1-scalar  = 2
encoded-len curve25519-point  = 4
encoded-len curve25519-base   = 2
encoded-len curve25519-scalar = 2

------------------------------------------------------------------------
-- Off-circuit values  (ir_types.rs: IrValue)
--
-- Constructors carry the concrete carrier; they are named distinctly
-- from the `IrType` tags to avoid overloading.
------------------------------------------------------------------------

data IrValue : Set where
  val-native            : Fr               → IrValue
  val-bytes             : List Byte        → IrValue
  val-byte              : Byte             → IrValue
  val-bool              : Bool             → IrValue
  val-accumulator       : Accumulator      → IrValue
  val-jubjub-point      : JubjubPoint      → IrValue
  val-jubjub-scalar     : JubjubScalar     → IrValue
  val-secp256k1-point        : Secp256k1Point        → IrValue
  val-secp256k1-base         : Secp256k1Base         → IrValue
  val-secp256k1-scalar       : Secp256k1Scalar       → IrValue
  val-secp256r1-point   : Secp256r1Point   → IrValue
  val-secp256r1-base    : Secp256r1Base    → IrValue
  val-secp256r1-scalar  : Secp256r1Scalar  → IrValue
  val-curve25519-point  : Curve25519Point  → IrValue
  val-curve25519-base   : Curve25519Base   → IrValue
  val-curve25519-scalar : Curve25519Scalar → IrValue

val-bytes32 : Bytes32 → IrValue
val-bytes32 bs = val-bytes (toList bs)

-- The type of a value  (ir_types.rs: IrValue::get_type).
typeof : IrValue → IrType
typeof (val-native            _) = native
typeof (val-bytes bs) = bytes (length bs)
typeof (val-byte _) = byte
typeof (val-bool _) = bool
typeof (val-accumulator _) = accumulator
typeof (val-jubjub-point      _) = jubjub-point
typeof (val-jubjub-scalar     _) = jubjub-scalar
typeof (val-secp256k1-point        _) = secp256k1-point
typeof (val-secp256k1-base         _) = secp256k1-base
typeof (val-secp256k1-scalar       _) = secp256k1-scalar
typeof (val-secp256r1-point   _) = secp256r1-point
typeof (val-secp256r1-base    _) = secp256r1-base
typeof (val-secp256r1-scalar  _) = secp256r1-scalar
typeof (val-curve25519-point  _) = curve25519-point
typeof (val-curve25519-base   _) = curve25519-base
typeof (val-curve25519-scalar _) = curve25519-scalar

-- Decidable type equality via an injective code.  This code is internal
-- to the decision procedure.  The binary wire tags belong to ir_types.rs.
type-code : IrType → ℕ
type-code native = 0
type-code byte = 1
type-code bool = 2
type-code accumulator = 3
type-code jubjub-point = 4
type-code jubjub-scalar = 5
type-code secp256k1-point = 6
type-code secp256k1-base = 7
type-code secp256k1-scalar = 8
type-code secp256r1-point = 9
type-code secp256r1-base = 10
type-code secp256r1-scalar = 11
type-code curve25519-point = 12
type-code curve25519-base = 13
type-code curve25519-scalar = 14
type-code (bytes n) = 15 + n

type-from-code : ℕ → IrType
type-from-code 0 = native
type-from-code 1 = byte
type-from-code 2 = bool
type-from-code 3 = accumulator
type-from-code 4 = jubjub-point
type-from-code 5 = jubjub-scalar
type-from-code 6 = secp256k1-point
type-from-code 7 = secp256k1-base
type-from-code 8 = secp256k1-scalar
type-from-code 9 = secp256r1-point
type-from-code 10 = secp256r1-base
type-from-code 11 = secp256r1-scalar
type-from-code 12 = curve25519-point
type-from-code 13 = curve25519-base
type-from-code 14 = curve25519-scalar
type-from-code n = bytes (n ∸ 15)

type-code-round : ∀ t → type-from-code (type-code t) ≡ t
type-code-round native = refl
type-code-round byte = refl
type-code-round bool = refl
type-code-round accumulator = refl
type-code-round jubjub-point = refl
type-code-round jubjub-scalar = refl
type-code-round secp256k1-point = refl
type-code-round secp256k1-base = refl
type-code-round secp256k1-scalar = refl
type-code-round secp256r1-point = refl
type-code-round secp256r1-base = refl
type-code-round secp256r1-scalar = refl
type-code-round curve25519-point = refl
type-code-round curve25519-base = refl
type-code-round curve25519-scalar = refl
type-code-round (bytes n) = refl

_≟T_ : DecidableEquality IrType
t ≟T u with type-code t ≟ type-code u
... | yes eq =
  yes (trans (sym (type-code-round t)) (trans (cong type-from-code eq) (type-code-round u)))
... | no neq = no (λ eq → neq (cong type-code eq))

------------------------------------------------------------------------
-- The elliptic-curve families that `ec-mul-generator`,
-- `into-coordinates` and `from-coordinates` dispatch on.
--
-- Each of those three instructions picks a curve from an operand's type
-- and produces a result in a matching type of the same curve.
-- `ECFamily` names the curve; the columns give its point type, the type
-- of a point's x/y coordinates, its scalar type, the carriers behind the
-- point and coordinate types, and the `IrValue` constructors injecting
-- those carriers.  The recognizers invert the type columns, reading the
-- family off an operand's type.  So the point ↔ coordinate ↔ scalar
-- pairing lives in one table instead of being re-derived at each
-- dispatch site.
--
-- `ec-families` is the dispatch table of `into-coordinates` and
-- `from-coordinates` and `ec-mul-generator`.
------------------------------------------------------------------------

data ECFamily : Set where
  jubjub secp256k1 secp256r1 curve25519 : ECFamily

pointTy : ECFamily → IrType
pointTy jubjub     = jubjub-point
pointTy secp256k1  = secp256k1-point
pointTy secp256r1  = secp256r1-point
pointTy curve25519 = curve25519-point

coordTy : ECFamily → IrType
coordTy jubjub     = native
coordTy secp256k1  = secp256k1-base
coordTy secp256r1  = secp256r1-base
coordTy curve25519 = curve25519-base

scalarTy : ECFamily → IrType
scalarTy jubjub     = jubjub-scalar
scalarTy secp256k1  = secp256k1-scalar
scalarTy secp256r1  = secp256r1-scalar
scalarTy curve25519 = curve25519-scalar

Pointᶠ : ECFamily → Set
Pointᶠ jubjub     = JubjubPoint
Pointᶠ secp256k1  = Secp256k1Point
Pointᶠ secp256r1  = Secp256r1Point
Pointᶠ curve25519 = Curve25519Point

-- Jubjub's coordinates are plain `Fr`: on the Edwards model its base
-- field is the circuit's own field, which is why `coordTy jubjub` is
-- `native` rather than a curve-specific base type.
Coordᶠ : ECFamily → Set
Coordᶠ jubjub     = Fr
Coordᶠ secp256k1  = Secp256k1Base
Coordᶠ secp256r1  = Secp256r1Base
Coordᶠ curve25519 = Curve25519Base

val-pointᶠ : ∀ f → Pointᶠ f → IrValue
val-pointᶠ jubjub     = val-jubjub-point
val-pointᶠ secp256k1  = val-secp256k1-point
val-pointᶠ secp256r1  = val-secp256r1-point
val-pointᶠ curve25519 = val-curve25519-point

val-coordᶠ : ∀ f → Coordᶠ f → IrValue
val-coordᶠ jubjub     = val-native
val-coordᶠ secp256k1  = val-secp256k1-base
val-coordᶠ secp256r1  = val-secp256r1-base
val-coordᶠ curve25519 = val-curve25519-base

pointFamily : IrType → Maybe ECFamily
pointFamily jubjub-point     = just jubjub
pointFamily secp256k1-point  = just secp256k1
pointFamily secp256r1-point  = just secp256r1
pointFamily curve25519-point = just curve25519
pointFamily _                = nothing

coordFamily : IrType → Maybe ECFamily
coordFamily native          = just jubjub
coordFamily secp256k1-base  = just secp256k1
coordFamily secp256r1-base  = just secp256r1
coordFamily curve25519-base = just curve25519
coordFamily _               = nothing

genScalarFamily : IrType → Maybe ECFamily
genScalarFamily jubjub-scalar    = just jubjub
genScalarFamily secp256k1-scalar = just secp256k1
genScalarFamily secp256r1-scalar = just secp256r1
genScalarFamily curve25519-scalar = just curve25519
genScalarFamily _                = nothing

-- Every recognizer inverts its type column, and every value column
-- lands in the type column it is paired with.
_ : ∀ f → pointFamily (pointTy f) ≡ just f
        × coordFamily (coordTy f) ≡ just f
        × (∀ p → typeof (val-pointᶠ f p) ≡ pointTy f)
        × (∀ x → typeof (val-coordᶠ f x) ≡ coordTy f)
_ = λ { jubjub     → refl , refl , (λ _ → refl) , (λ _ → refl)
      ; secp256k1  → refl , refl , (λ _ → refl) , (λ _ → refl)
      ; secp256r1  → refl , refl , (λ _ → refl) , (λ _ → refl)
      ; curve25519 → refl , refl , (λ _ → refl) , (λ _ → refl) }

ec-families : List ECFamily
ec-families = jubjub ∷ secp256k1 ∷ secp256r1 ∷ curve25519 ∷ []

gen-families : List ECFamily
gen-families = ec-families

-- "`P` holds of one of `fs`", laid out as the right-nested `⊎` that the
-- dispatching instructions' per-family disjuncts are consumed as.
Anyᶠ : (ECFamily → Set) → List ECFamily → Set
Anyᶠ P []           = ⊥
Anyᶠ P (f ∷ [])     = P f
Anyᶠ P (f ∷ g ∷ fs) = P f ⊎ Anyᶠ P (g ∷ fs)
