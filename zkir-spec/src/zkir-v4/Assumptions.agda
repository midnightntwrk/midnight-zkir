{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- Assumptions of the zkir-v4 formalization
--
-- Downstream modules take the primitive operations and laws in this
-- record as a module parameter.  The chip contracts describe their
-- inputs, outputs and failure conditions.  The encoding, interpreter
-- and circuit walk derive the instruction behavior from these contracts.
------------------------------------------------------------------------

module zkir-v4.Assumptions where

open import Data.Bool    using (Bool; if_then_else_)
open import Data.Fin     using (Fin)
open import Data.List    using (List; []; _∷_)
open import Data.Maybe   using (Maybe; just)
open import Data.Nat     using (ℕ; _+_; _*_)
open import Data.Product using (_×_; _,_; uncurry)
open import Data.Vec     using (Vec)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)

-- Integer value of a little-endian bit list (used by the valuation `valFr`).
bits-to-ℕ : List Bool → ℕ
bits-to-ℕ []       = 0
bits-to-ℕ (b ∷ bs) = (if b then 1 else 0) + 2 * bits-to-ℕ bs

------------------------------------------------------------------------
-- Concrete byte types (ir_types.rs: Bytes32 = [u8; 32]).
--
-- A byte is an element of Fin 256; a `Bytes32` is a length-32 vector of
-- bytes.  These are concrete (they do not depend on the trust base) and
-- are shared by the record fields below and by downstream modules.
------------------------------------------------------------------------

Byte : Set
Byte = Fin 256

Bytes32 : Set
Bytes32 = Vec Byte 32

-- Ledger FAB descriptors are ordered sequences.  An option contains its
-- alternative descriptors, each of which is itself an ordered sequence.
data AlignmentSegment : Set where
  field-atom compress-atom : AlignmentSegment
  bytes-atom : ℕ → AlignmentSegment
  option : List (List AlignmentSegment) → AlignmentSegment

Alignment : Set
Alignment = List AlignmentSegment

record Assumptions : Set₁ where

  ----------------------------------------------------------------------
  -- Carrier types.
  ----------------------------------------------------------------------

  field
    Fr               : Set
    -- ^ BLS12-381 scalar field element; the native field and the base
    --   field of Jubjub (transient_crypto::curve::Fr).
    JubjubPoint      : Set
    -- ^ Point of the Jubjub curve (in its prime-order subgroup).
    JubjubScalar     : Set
    -- ^ Element of the Jubjub scalar field.
    Secp256k1Point        : Set
    -- ^ Point of the Secp256k1 curve (midnight_curves::k256::K256, a
    --   Weierstrass curve of cofactor 1 over a foreign field), including
    --   the identity.
    Secp256k1Base         : Set
    -- ^ Secp256k1 base field element (k256::Fp).
    Secp256k1Scalar       : Set
    -- ^ Secp256k1 scalar field element (k256::Fq).
    Secp256r1Point   : Set
    -- ^ Point of the Secp256r1 curve (midnight_curves::p256::P256, a
    --   Weierstrass curve — NIST P-256 — over a foreign field), including
    --   the identity.
    Secp256r1Base    : Set
    -- ^ Secp256r1 base field element (p256::Fp).
    Secp256r1Scalar  : Set
    -- ^ Secp256r1 scalar field element (p256::Fq).
    Curve25519Point  : Set
    -- ^ Point of the Curve25519 curve (midnight_curves::curve25519::
    --   Curve25519Subgroup, a twisted Edwards curve over a foreign
    --   field), including the identity — which, unlike the Weierstrass
    --   curves above, has real affine coordinates ((0, 1)) rather than
    --   being a special-cased sentinel.
    Curve25519Base   : Set
    -- ^ Curve25519 base field element (curve25519::Fp, the 2²⁵⁵-19 field).
    Curve25519Scalar : Set
    -- ^ Curve25519 scalar field element (curve25519::Scalar, the
    --   standard Ed25519 subgroup order).
    G1Point : Set  -- BLS12-381 G1 prime-order subgroup, including identity.

  -- A deferred accumulator contains exactly one resolved G1 point per
  -- side, each with implicit scalar one.
  Accumulator : Set
  Accumulator = G1Point × G1Point

  ----------------------------------------------------------------------
  -- Native field (ZkStdLib arithmetic over Fr).
  ----------------------------------------------------------------------

  field
    0ᶠ 1ᶠ : Fr
    _+ᶠ_ _*ᶠ_ : Fr → Fr → Fr
    -ᶠ_       : Fr → Fr
    -- Inversion is partial: `nothing` exactly on 0ᶠ (Inv errors on zero).
    invᶠ      : Fr → Maybe Fr
    _≟ᶠ_      : DecidableEquality Fr

    -- Canonical little-endian decomposition and reduction of arbitrary
    -- little-endian bit strings modulo the scalar field order.
    to-le-bits   : Fr → List Bool
    from-le-bits : List Bool → Fr

  ----------------------------------------------------------------------
  -- Jubjub (native embedded curve) gadget contracts.
  ----------------------------------------------------------------------

  field
    _+J_ : JubjubPoint → JubjubPoint → JubjubPoint   -- point addition
    _·J_ : JubjubScalar → JubjubPoint → JubjubPoint  -- scalar mult.
    genJ : JubjubPoint                               -- group generator
    idJ  : JubjubPoint                               -- identity (default)
    negJ : JubjubPoint → JubjubPoint                 -- point negation
    _≟J_ : DecidableEquality JubjubPoint

    -- Affine coordinates.  `coordsJ` is total (every subgroup point has
    -- affine coordinates on the Edwards model); `fromCoordsJ` is partial
    -- (the coordinates must denote a point in the prime-order subgroup).
    --
    -- The circuit contract uses the chip's subgroup-checked
    -- point_from_coordinates operation.
    coordsJ     : JubjubPoint → Fr × Fr
    fromCoordsJ : Fr → Fr → Maybe JubjubPoint

    -- Scalar encoding (canonical 252-bit) and the Native → JubjubScalar
    -- reduction (JubjubScalarFromNative).
    jubjubScalarToFr   : JubjubScalar → Fr
    jubjubScalarFromFr : Fr → Maybe JubjubScalar
    native→jubjubScalar : Fr → JubjubScalar
    _+Jˢ_ _*Jˢ_ : JubjubScalar → JubjubScalar → JubjubScalar
    -Jˢ_ : JubjubScalar → JubjubScalar
    invJˢ : JubjubScalar → Maybe JubjubScalar
    _≟Jˢ_ : DecidableEquality JubjubScalar
    jubjubScalarToBytes : JubjubScalar → Bytes32
    jubjubScalarFromBytes : List Byte → JubjubScalar

    -- Hash a sequence of native elements to a Jubjub point.
    hash-to-curve-fn : List Fr → JubjubPoint

  ----------------------------------------------------------------------
  -- Secp256k1 (foreign-field emulated curve) gadget contracts.
  --
  -- The in-circuit side is the `midnight-circuits` foreign-field /
  -- foreign-ECC chips (`AssignedField`, `AssignedForeignPoint`), modeled
  -- here by their functional contracts; the CRT/limb internals stay
  -- inside the chip contract.
  ----------------------------------------------------------------------

  field
    -- Base field Fp (k256::Fp).  Inversion is partial: `nothing`
    -- exactly on 0 (Inv errors on zero).
    _+K1ᵇ_ _*K1ᵇ_ : Secp256k1Base → Secp256k1Base → Secp256k1Base
    -K1ᵇ_       : Secp256k1Base → Secp256k1Base
    invK1ᵇ      : Secp256k1Base → Maybe Secp256k1Base
    _≟K1ᵇ_      : DecidableEquality Secp256k1Base

    -- Scalar field Fq (k256::Fq).
    _+K1ˢ_ _*K1ˢ_ : Secp256k1Scalar → Secp256k1Scalar → Secp256k1Scalar
    -K1ˢ_       : Secp256k1Scalar → Secp256k1Scalar
    invK1ˢ      : Secp256k1Scalar → Maybe Secp256k1Scalar
    _≟K1ˢ_      : DecidableEquality Secp256k1Scalar

    -- Curve group.
    _+K1_ : Secp256k1Point → Secp256k1Point → Secp256k1Point    -- point addition
    negK1 : Secp256k1Point → Secp256k1Point                -- point negation
    _·K1_ : Secp256k1Scalar → Secp256k1Point → Secp256k1Point   -- scalar mult. (msm)
    genK1 : Secp256k1Point                            -- group generator
    idK1  : Secp256k1Point                            -- identity (default)
    _≟K1_ : DecidableEquality Secp256k1Point

    -- Affine coordinates.  `coordsK1` is partial: `nothing` exactly on
    -- the Weierstrass identity, which has no affine coordinates
    -- (IntoCoordinates errors off-circuit / asserts non-zero
    -- in-circuit).  `fromCoordsK1` is partial (on-curve check); the
    -- identity is not constructible from coordinates.
    coordsK1     : Secp256k1Point → Maybe (Secp256k1Base × Secp256k1Base)
    fromCoordsK1 : Secp256k1Base → Secp256k1Base → Maybe Secp256k1Point

    -- Limb encodings (`as_public_input` / `from_public_input` of the
    -- assigned foreign types): a 256-bit field element is two native
    -- limbs; a point is x-limbs ++ y-limbs ++ an identity flag (widths
    -- 2 / 2 / 5, ir_types.rs encoded_len).
    --
    -- TRUST NOTE: the decoders modeled here are the *canonical*
    -- partial inverses — they reject any limb vector the encoder
    -- cannot emit, as the Group C `secp*-sound` laws demand.
    secp256k1Base→limbs   : Secp256k1Base → Fr × Fr
    limbs→secp256k1Base   : Fr → Fr → Maybe Secp256k1Base
    secp256k1Scalar→limbs : Secp256k1Scalar → Fr × Fr
    limbs→secp256k1Scalar : Fr → Fr → Maybe Secp256k1Scalar
    secp256k1Point→limbs  : Secp256k1Point → Fr × Fr × Fr × Fr × Fr
    limbs→secp256k1Point  : Fr → Fr → Fr → Fr → Fr → Maybe Secp256k1Point

    -- Bytes32 conversions (IntoBytes32 / FromBytes32 on the foreign
    -- fields): `to_bytes_le` and the *total* little-endian reduction
    -- `from_le_bytes_with_reduction` (non-canonical bytes reduce mod
    -- the field order).
    secp256k1BaseToBytes     : Secp256k1Base → Bytes32
    secp256k1BaseFromBytes   : List Byte → Secp256k1Base
    secp256k1ScalarToBytes   : Secp256k1Scalar → Bytes32
    secp256k1ScalarFromBytes : List Byte → Secp256k1Scalar

  ----------------------------------------------------------------------
  -- Secp256r1 (foreign-field emulated curve) gadget contracts.
  --
  -- Structurally identical to the Secp256k1 block above (also a
  -- Weierstrass foreign curve); the `P` tag mirrors `K`, both derived
  -- from the underlying midnight_curves module name (p256 / k256).
  ----------------------------------------------------------------------

  field
    -- Base field Fp (p256::Fp).  Inversion is partial: `nothing`
    -- exactly on 0 (Inv errors on zero).
    _+Pᵇ_ _*Pᵇ_ : Secp256r1Base → Secp256r1Base → Secp256r1Base
    -Pᵇ_        : Secp256r1Base → Secp256r1Base
    invPᵇ       : Secp256r1Base → Maybe Secp256r1Base
    _≟Pᵇ_       : DecidableEquality Secp256r1Base

    -- Scalar field Fq (p256::Fq).
    _+Pˢ_ _*Pˢ_ : Secp256r1Scalar → Secp256r1Scalar → Secp256r1Scalar
    -Pˢ_        : Secp256r1Scalar → Secp256r1Scalar
    invPˢ       : Secp256r1Scalar → Maybe Secp256r1Scalar
    _≟Pˢ_       : DecidableEquality Secp256r1Scalar

    -- Curve group.
    genP : Secp256r1Point
    _+P_ : Secp256r1Point → Secp256r1Point → Secp256r1Point   -- point add.
    negP : Secp256r1Point → Secp256r1Point                    -- point neg.
    _·P_ : Secp256r1Scalar → Secp256r1Point → Secp256r1Point  -- scalar mult.
    idP  : Secp256r1Point                                     -- identity
    _≟P_ : DecidableEquality Secp256r1Point

    -- Affine coordinates.  `coordsP` is partial: `nothing` exactly on
    -- the Weierstrass identity, which has no affine coordinates
    -- (IntoCoordinates errors off-circuit / asserts non-zero
    -- in-circuit).  `fromCoordsP` is partial (on-curve check); the
    -- identity is not constructible from coordinates.
    coordsP     : Secp256r1Point → Maybe (Secp256r1Base × Secp256r1Base)
    fromCoordsP : Secp256r1Base → Secp256r1Base → Maybe Secp256r1Point

    -- Limb encodings (`as_public_input` / `from_public_input` of the
    -- assigned foreign types): a 256-bit field element is two native
    -- limbs; a point is x-limbs ++ y-limbs ++ an identity flag (widths
    -- 2 / 2 / 5, matching Secp256k1's — ir_types.rs encoded_len).
    --
    -- TRUST NOTE: the decoders modeled here are the canonical partial
    -- inverses, matching the same modeling approach used for
    -- Secp256k1 above.
    secp256r1Base→limbs   : Secp256r1Base → Fr × Fr
    limbs→secp256r1Base   : Fr → Fr → Maybe Secp256r1Base
    secp256r1Scalar→limbs : Secp256r1Scalar → Fr × Fr
    limbs→secp256r1Scalar : Fr → Fr → Maybe Secp256r1Scalar
    secp256r1Point→limbs  : Secp256r1Point → Fr × Fr × Fr × Fr × Fr
    limbs→secp256r1Point  : Fr → Fr → Fr → Fr → Fr → Maybe Secp256r1Point

    -- Bytes32 conversions (IntoBytes32 / FromBytes32 on the foreign
    -- fields): `to_bytes_le` and the *total* little-endian reduction
    -- `from_le_bytes_with_reduction` (non-canonical bytes reduce mod
    -- the field order).
    secp256r1BaseToBytes     : Secp256r1Base → Bytes32
    secp256r1BaseFromBytes   : List Byte → Secp256r1Base
    secp256r1ScalarToBytes   : Secp256r1Scalar → Bytes32
    secp256r1ScalarFromBytes : List Byte → Secp256r1Scalar

  ----------------------------------------------------------------------
  -- Curve25519 (foreign-field emulated Edwards curve) gadget contracts.
  --
  -- Unlike Secp256k1/Secp256r1 (foreign Weierstrass curves) and unlike
  -- Jubjub (a native Edwards curve), Curve25519 is a foreign Edwards
  -- curve — the one combination that needs the identity to be a real
  -- point rather than a special-cased sentinel: `coordsC` below is
  -- TOTAL, mirroring `coordsJ`'s shape, not `coordsK1`/`coordsP`'s
  -- `Maybe`-wrapped shape. Everything else (field arithmetic, limb
  -- encoding, Bytes32 conversion, curve-group operations) mirrors the
  -- Secp256k1/Secp256r1 block's shape (foreign-field carriers); the `C`
  -- tag is derived from the underlying midnight_curves module name
  -- (curve25519), following the same convention as K/k256, P/p256.
  ----------------------------------------------------------------------

  field
    -- Base field Fp (curve25519::Fp).  Inversion is partial: `nothing`
    -- exactly on 0 (Inv errors on zero).
    _+Cᵇ_ _*Cᵇ_ : Curve25519Base → Curve25519Base → Curve25519Base
    -Cᵇ_        : Curve25519Base → Curve25519Base
    invCᵇ       : Curve25519Base → Maybe Curve25519Base
    _≟Cᵇ_       : DecidableEquality Curve25519Base

    -- Scalar field (curve25519::Scalar).
    _+Cˢ_ _*Cˢ_ : Curve25519Scalar → Curve25519Scalar → Curve25519Scalar
    -Cˢ_        : Curve25519Scalar → Curve25519Scalar
    invCˢ       : Curve25519Scalar → Maybe Curve25519Scalar
    _≟Cˢ_       : DecidableEquality Curve25519Scalar

    -- Curve group.
    genC : Curve25519Point
    _+C_ : Curve25519Point → Curve25519Point → Curve25519Point  -- point add.
    negC : Curve25519Point → Curve25519Point                    -- point neg.
    _·C_ : Curve25519Scalar → Curve25519Point → Curve25519Point -- scalar mult.
    idC  : Curve25519Point                                      -- identity
    _≟C_ : DecidableEquality Curve25519Point

    -- Affine coordinates are total for subgroup points, including the
    -- Edwards identity (0, 1).  Construction from coordinates checks
    -- the curve equation and membership in the prime-order subgroup.
    coordsC     : Curve25519Point → Curve25519Base × Curve25519Base
    fromCoordsC : Curve25519Base → Curve25519Base → Maybe Curve25519Point

    -- Limb encodings (`as_public_input` / `from_public_input`): a
    -- 256-bit field element is two native limbs (same widths as
    -- Secp256k1/Secp256r1); a point is x-limbs ++ y-limbs, with NO
    -- identity flag (widths 2 / 2 / 4, ir_types.rs encoded_len — one
    -- element fewer than the Weierstrass curves' 5, since there's no
    -- flag element).
    --
    -- TRUST NOTE: the decoders modeled here are the canonical partial
    -- inverses (they reject what the encoder cannot emit and any
    -- non-torsion-free point).
    curve25519Base→limbs   : Curve25519Base → Fr × Fr
    limbs→curve25519Base   : Fr → Fr → Maybe Curve25519Base
    curve25519Scalar→limbs : Curve25519Scalar → Fr × Fr
    limbs→curve25519Scalar : Fr → Fr → Maybe Curve25519Scalar
    curve25519Point→limbs  : Curve25519Point → Fr × Fr × Fr × Fr
    limbs→curve25519Point  : Fr → Fr → Fr → Fr → Maybe Curve25519Point

    -- Bytes32 conversions (IntoBytes32 / FromBytes32 on the foreign
    -- fields): `to_bytes_le` and the *total* little-endian reduction
    -- `from_le_bytes_with_reduction` (non-canonical bytes reduce mod
    -- the field order).
    curve25519BaseToBytes     : Curve25519Base → Bytes32
    curve25519BaseFromBytes   : List Byte → Curve25519Base
    curve25519ScalarToBytes   : Curve25519Scalar → Bytes32
    curve25519ScalarFromBytes : List Byte → Curve25519Scalar

  ----------------------------------------------------------------------
  -- Bytes32 ↔ field conversions.
  ----------------------------------------------------------------------

  field
    -- Canonical 32-byte little-endian representation of a native value.
    nativeToBytes   : Fr → Bytes32

    -- The byte decoders of the prime fields reduce a little-endian
    -- unsigned integer of any length modulo that field's order.
    -- Point decompression instead checks a curve and its subgroup.  The
    -- caller checks the length and rejects a result that re-encodes
    -- differently.  The two SEC1 encoders use 33 zero bytes for identity.
    jubjubPointToBytes : JubjubPoint → Bytes32
    jubjubPointFromBytes : Bytes32 → Maybe JubjubPoint
    curve25519PointToBytes : Curve25519Point → Bytes32
    curve25519PointFromBytes : Bytes32 → Maybe Curve25519Point
    secp256k1PointToBytes : Secp256k1Point → Vec Byte 33
    secp256k1PointFromBytes : Vec Byte 33 → Maybe Secp256k1Point
    secp256r1PointToBytes : Secp256r1Point → Vec Byte 33
    secp256r1PointFromBytes : Vec Byte 33 → Maybe Secp256r1Point

  ----------------------------------------------------------------------
  -- Hashing and the communications commitment.
  ----------------------------------------------------------------------

  field
    transient-hash-fn  : List Fr → Fr
    -- Persistent (SHA-256) and Keccak-256 hashes parse their inputs under
    -- the alignment, hence partial; each yields a 32-byte digest.
    -- `persistent-hash-fn` models SHA-256 (`Sha256::digest`); `keccak-fn`
    -- models Keccak-256.  Both remain opaque.
    persistent-hash-fn : Alignment → List Fr → Maybe Bytes32
    keccak-fn          : Alignment → List Fr → Maybe Bytes32
    sha512-fn          : Alignment → List Fr → Maybe (Vec Byte 64)

    -- Circuit FAB parsing contracts.  The circuit walks the alignment
    -- itself and rejects option and compressed atoms.  It may leave extra
    -- input fields unused.  Hashing uses the resulting byte representation.
    persistent-hash-circuit-fn : Alignment → List Fr → Maybe Bytes32
    keccak-circuit-fn          : Alignment → List Fr → Maybe Bytes32
    sha512-circuit-fn          : Alignment → List Fr → Maybe (Vec Byte 64)

  -- RC1 prepends the opening to the ordered input and return fields.
  transient-commit : List Fr → Fr → Fr
  transient-commit message opening = transient-hash-fn (opening ∷ message)

  ----------------------------------------------------------------------
  -- Deferred inner proofs (prepare_verification.rs and accumulate.rs).
  ----------------------------------------------------------------------

  field
    sha256-bytes : List Byte → Bytes32
    -- Reading a Processed MidnightVK<KZG> includes its architecture version
    -- and the PLONK key's supported evaluation domain.
    key-well-formed : List Byte → Bool
    -- Active preprocessing parses the processed verification key and
    -- runs PLONK preparation with the supplied instance and proof bytes.
    prepare-active : List Byte → List Fr → List Byte → Maybe Accumulator
    -- Synthesis parses the key and invokes the verifier gadget for either
    -- guard value.  It scales the accumulator by the guard and collapses it.
    prepare-circuit : List Byte → List Fr → List Byte → Bool → Maybe Accumulator
    -- The key, instance layout and proof representation must be supported.
    -- Even a disabled preparation needs space for its instance column
    -- after reserving the blinding rows and one extra row.  DirectLaws
    -- concerns verification for the same instance, ExactAt for the same bytes.
    prepare-compatible : List Byte → List Fr → List Byte → Bool → Bool
    fold-accumulators : List Accumulator → Maybe Accumulator
    trivial-accumulator : Accumulator
    pairing-valid : Accumulator → Bool

    -- Pin the public-input layout at two packed x−1 fields, two packed
    -- y−1 fields and the identity flag.  Encoding adds scalar one per side.
    g1-to-fields : G1Point → Vec Fr 5
    g1-from-fields : Vec Fr 5 → Maybe G1Point
    _≟G1_ : DecidableEquality G1Point

  ----------------------------------------------------------------------
  -- Field non-triviality, used for Boolean guards.
  ----------------------------------------------------------------------

  field
    1ᶠ≢0ᶠ : ¬ (1ᶠ ≡ 0ᶠ)

  ----------------------------------------------------------------------
  -- Canonical valuation, used for unsigned range checks.
  ----------------------------------------------------------------------

  valFr : Fr → ℕ
  valFr x = bits-to-ℕ (to-le-bits x)

  ----------------------------------------------------------------------
  -- Primitive encoding round-trips.
  ----------------------------------------------------------------------

  field
    coordsJ-fromCoordsJ : ∀ p → uncurry fromCoordsJ (coordsJ p) ≡ just p

    jubjubScalar-round : ∀ s
      → jubjubScalarFromFr (jubjubScalarToFr s) ≡ just s

    secp256k1Base-round : ∀ x
      → uncurry limbs→secp256k1Base (secp256k1Base→limbs x) ≡ just x

    secp256k1Scalar-round : ∀ s
      → uncurry limbs→secp256k1Scalar (secp256k1Scalar→limbs s) ≡ just s

    secp256k1Point-round : ∀ {p a b c d e}
      → secp256k1Point→limbs p ≡ (a , b , c , d , e)
      → limbs→secp256k1Point a b c d e ≡ just p

    secp256r1Base-round : ∀ x
      → uncurry limbs→secp256r1Base (secp256r1Base→limbs x) ≡ just x

    secp256r1Scalar-round : ∀ s
      → uncurry limbs→secp256r1Scalar (secp256r1Scalar→limbs s) ≡ just s

    secp256r1Point-round : ∀ {p a b c d e}
      → secp256r1Point→limbs p ≡ (a , b , c , d , e)
      → limbs→secp256r1Point a b c d e ≡ just p

    curve25519Base-round : ∀ x
      → uncurry limbs→curve25519Base (curve25519Base→limbs x) ≡ just x

    curve25519Scalar-round : ∀ s
      → uncurry limbs→curve25519Scalar (curve25519Scalar→limbs s) ≡ just s

    curve25519Point-round : ∀ {p a b c d}
      → curve25519Point→limbs p ≡ (a , b , c , d)
      → limbs→curve25519Point a b c d ≡ just p

  -- BLS12-381 scalar field parameters from the pinned backend.
  FR-BITS FR-ORDER : ℕ
  FR-BITS = 255
  FR-ORDER = 52435875175126190479447740508185965837690552500527637822603658699938581184513
