{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

-- Deterministic value-level contracts shared by the preprocess interpreter
-- and the circuit model.  These operations have no transcript or proof state.
module zkir-v4.Operations (⋯ : _) (open Assumptions ⋯) where

open import zkir-v4.Types ⋯
open import zkir-v4.Syntax ⋯
open import zkir-v4.Encoding ⋯ public using (_≟LFr_)
open import zkir-v4.Encoding ⋯ renaming (encode to encodeᵉ)

open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_; _xor_)
  renaming (not to bnot)
import Data.Bool.Properties as BoolP
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_; _<?_; _≤?_; _≟_)
open import Data.List using
  (List; []; _∷_; _++_; length; take; drop; map; foldr; replicate)
  renaming (reverse to reverse-list)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
  renaming (map to map-maybe)
open import Data.Product using (_×_; _,_)
open import Data.String using () renaming (_≟_ to _≟str_)
import Data.Fin as F
import Data.Fin.Properties as FinP
import Data.List.Properties as ListP
open import Data.Vec using (Vec; fromList; toList)
open import Function using (case_of_)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (subst)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (isYes)

-- A decision used as a guard: keep the continuation iff it holds.
guardD : {P A : Set} → Dec P → Maybe A → Maybe A
guardD (yes _) k = k
guardD (no  _) _ = nothing

-- `bits-to-ℕ` and `valFr` come from the trust base (`Assumptions`).

-- 2^n as a field element.
pow2ᶠ : ℕ → Fr
pow2ᶠ zero    = 1ᶠ
pow2ᶠ (suc n) = (1ᶠ +ᶠ 1ᶠ) *ᶠ pow2ᶠ n

-- Boolean → field embedding.
χ : Bool → Fr
χ true  = 1ᶠ
χ false = 0ᶠ

_≟B_ : DecidableEquality (List Byte)
_≟B_ = ListP.≡-dec FinP._≟_

-- Read a field element as a boolean: 0 ↦ false, 1 ↦ true, else fail.
to𝔹 : Fr → Maybe Bool
to𝔹 x with x ≟ᶠ 0ᶠ
... | yes _ = just false
... | no  _ with x ≟ᶠ 1ᶠ
...   | yes _ = just true
...   | no  _ = nothing

-- The default value of each type (guarded transcript reads).  The secp
-- field defaults are the Rust `Fp::default()` / `Fq::default()` = 0,
-- obtained here as the reduction of an empty byte string, which represents zero (keeping
-- zero out of the trust base); `K256::default()` is the identity.
default-val : IrType → IrValue
default-val native           = val-native 0ᶠ
default-val (bytes n)        = val-bytes (replicate n F.zero)
default-val byte             = val-byte F.zero
default-val bool             = val-bool false
default-val accumulator      = val-accumulator trivial-accumulator
default-val jubjub-point     = val-jubjub-point idJ
default-val jubjub-scalar    = val-jubjub-scalar (native→jubjubScalar 0ᶠ)
default-val secp256k1-point       = val-secp256k1-point idK1
default-val secp256k1-base        =
  val-secp256k1-base (secp256k1BaseFromBytes [])
default-val secp256k1-scalar      =
  val-secp256k1-scalar (secp256k1ScalarFromBytes [])
default-val secp256r1-point  = val-secp256r1-point idP
default-val secp256r1-base   =
  val-secp256r1-base (secp256r1BaseFromBytes [])
default-val secp256r1-scalar =
  val-secp256r1-scalar (secp256r1ScalarFromBytes [])
default-val curve25519-point  = val-curve25519-point idC
default-val curve25519-base   =
  val-curve25519-base (curve25519BaseFromBytes [])
default-val curve25519-scalar =
  val-curve25519-scalar (curve25519ScalarFromBytes [])

------------------------------------------------------------------------
-- The named value store.
------------------------------------------------------------------------

Mem : Set
Mem = Identifier → Maybe IrValue

∅ : Mem
∅ _ = nothing

ins : Identifier → IrValue → Mem → Mem
ins id v m i = case (i ≟str id) of λ { (yes _) → just v ; (no _) → m i }

------------------------------------------------------------------------
-- Operand resolution.
------------------------------------------------------------------------

resolve : Mem → Operand → Maybe IrValue
resolve m (var id) = m id
resolve m (imm x)  = just (val-native x)

-- Resolve, expecting a Native value (an immediate, or a Native variable).
resolveᶠ : Mem → Operand → Maybe Fr
resolveᶠ m op = resolve m op >>= λ { (val-native x) → just x ; _ → nothing }

resolve𝔹 : Mem → Operand → Maybe Bool
resolve𝔹 m op = resolveᶠ m op >>= to𝔹

eval-guard : Mem → Maybe Operand → Maybe Bool
eval-guard m nothing   = just true
eval-guard m (just op) = resolve𝔹 m op

resolve-all-Fr : Mem → List Operand → Maybe (List Fr)
resolve-all-Fr m []         = just []
resolve-all-Fr m (op ∷ ops) =
  resolveᶠ m op        >>= λ x  →
  resolve-all-Fr m ops >>= λ xs →
  just (x ∷ xs)

------------------------------------------------------------------------
ProofStore : Set
ProofStore = Identifier → Maybe (List Byte)

insert-proof : Identifier → List Byte → ProofStore → ProofStore
insert-proof id v m i = case (i ≟str id) of λ { (yes _) → just v ; (no _) → m i }

apply-writes : Mem → List (Identifier × IrValue) → Mem
apply-writes m [] = m
apply-writes m ((id , v) ∷ vs) = apply-writes (ins id v m) vs

resolve-bytes : Mem → Operand → Maybe (List Byte)
resolve-bytes m op = resolve m op >>= λ { (val-bytes bs) → just bs ; _ → nothing }

resolve-typed-bools : Mem → List Operand → Maybe (List Bool)
resolve-typed-bools m [] = just []
resolve-typed-bools m (op ∷ ops) =
  resolve m op >>= λ
    { (val-bool b) → resolve-typed-bools m ops >>= λ bs → just (b ∷ bs)
    ; _ → nothing }

resolve-acc : Mem → Operand → Maybe Accumulator
resolve-acc m op = resolve m op >>= λ { (val-accumulator a) → just a ; _ → nothing }

resolve-accs : Mem → List Operand → Maybe (List Accumulator)
resolve-accs m [] = just []
resolve-accs m (op ∷ ops) =
  resolve-acc m op >>= λ a →
  resolve-accs m ops >>= λ as → just (a ∷ as)

resolve-concat : Mem → List Operand → Maybe (List Byte)
resolve-concat m [] = just []
resolve-concat m (op ∷ ops) =
  resolve m op >>= λ
    { (val-byte b) → resolve-concat m ops >>= λ bs → just (b ∷ bs)
    ; (val-bytes bs) → resolve-concat m ops >>= λ cs → just (bs ++ cs)
    ; _ → nothing }

at : ∀ {A : Set} → List A → ℕ → Maybe A
at [] _ = nothing
at (x ∷ xs) zero = just x
at (x ∷ xs) (suc n) = at xs n

as-vector : ∀ n → List Byte → Maybe (Vec Byte n)
as-vector n bs with length bs ≟ n
... | yes eq = just (subst (Vec Byte) eq (fromList bs))
... | no _ = nothing

valEq? : IrValue → IrValue → Maybe Bool
valEq? (val-native x)           (val-native y)           = just (isYes (x ≟ᶠ y))
valEq? (val-bytes a)            (val-bytes b)            = just (isYes (a ≟B b))
valEq? (val-byte a)             (val-byte b)             = just (isYes (FinP._≟_ a b))
valEq? (val-bool a)             (val-bool b)             = just (isYes (BoolP._≟_ a b))
valEq? (val-jubjub-scalar a)    (val-jubjub-scalar b)    = just (isYes (a ≟Jˢ b))
valEq? (val-jubjub-point p)     (val-jubjub-point q)     = just (isYes (p ≟J q))
valEq? (val-secp256k1-point p)       (val-secp256k1-point q)       = just (isYes (p ≟K1 q))
valEq? (val-secp256k1-base x)        (val-secp256k1-base y)        = just (isYes (x ≟K1ᵇ y))
valEq? (val-secp256k1-scalar x)      (val-secp256k1-scalar y)      = just (isYes (x ≟K1ˢ y))
valEq? (val-secp256r1-point p)  (val-secp256r1-point q)  = just (isYes (p ≟P q))
valEq? (val-secp256r1-base x)   (val-secp256r1-base y)   = just (isYes (x ≟Pᵇ y))
valEq? (val-secp256r1-scalar x) (val-secp256r1-scalar y) = just (isYes (x ≟Pˢ y))
valEq? (val-curve25519-point p) (val-curve25519-point q) =
  just (isYes (p ≟C q))
valEq? (val-curve25519-base x) (val-curve25519-base y) =
  just (isYes (x ≟Cᵇ y))
valEq? (val-curve25519-scalar x) (val-curve25519-scalar y) =
  just (isYes (x ≟Cˢ y))
valEq? _                        _                        = nothing

-- ConstrainEq compares the full value, including accumulators.
constrainEq? : IrValue → IrValue → Maybe Bool
constrainEq? (val-accumulator (l , r)) (val-accumulator (l′ , r′)) =
  just (isYes (l ≟G1 l′) ∧ isYes (r ≟G1 r′))
constrainEq? a b = valEq? a b

-- The SEC1 representation uses 33 zero bytes for the identity.
sec1-identity : List Byte
sec1-identity = replicate 33 F.zero

sec1-bytes : ∀ {Point : Set} → DecidableEquality Point → Point →
             (Point → Vec Byte 33) → Point → List Byte
sec1-bytes eq identity compress point with eq point identity
... | yes _ = sec1-identity
... | no _ = toList (compress point)

sec1-point : ∀ {Point : Set} → DecidableEquality Point → Point →
             (Point → Vec Byte 33) → (Vec Byte 33 → Maybe Point) →
             List Byte → Maybe Point
sec1-point eq identity compress decompress bs with bs ≟B sec1-identity
... | yes _ = just identity
... | no _ =
  as-vector 33 bs >>= λ raw →
  decompress raw >>= λ point →
  guardD (bs ≟B sec1-bytes eq identity compress point) (just point)

-- Compressed point encodings and fixed-width prime-field representations.
to-bytes-value : IrValue → Maybe (List Byte)
to-bytes-value (val-native x) = just (toList (nativeToBytes x))
to-bytes-value (val-jubjub-scalar x) = just (toList (jubjubScalarToBytes x))
to-bytes-value (val-secp256k1-base x) = just (toList (secp256k1BaseToBytes x))
to-bytes-value (val-secp256k1-scalar x) = just (toList (secp256k1ScalarToBytes x))
to-bytes-value (val-secp256r1-base x) = just (toList (secp256r1BaseToBytes x))
to-bytes-value (val-secp256r1-scalar x) = just (toList (secp256r1ScalarToBytes x))
to-bytes-value (val-curve25519-base x) = just (toList (curve25519BaseToBytes x))
to-bytes-value (val-curve25519-scalar x) = just (toList (curve25519ScalarToBytes x))
to-bytes-value (val-jubjub-point x) = just (toList (jubjubPointToBytes x))
to-bytes-value (val-secp256k1-point x) = just (sec1-bytes _≟K1_ idK1 secp256k1PointToBytes x)
to-bytes-value (val-secp256r1-point x) = just (sec1-bytes _≟P_ idP secp256r1PointToBytes x)
to-bytes-value (val-curve25519-point x) = just (toList (curve25519PointToBytes x))
to-bytes-value _ = nothing

-- Typed encoding is canonical.  By contrast, FromBytes on a field
-- reduces the integer represented by an arbitrary-length byte string.
from-bytes-value : IrType → List Byte → Maybe IrValue
from-bytes-value native bs = just (val-native (native-from-bytes bs))
from-bytes-value jubjub-scalar bs = just (val-jubjub-scalar (jubjubScalarFromBytes bs))
from-bytes-value secp256k1-base bs = just (val-secp256k1-base (secp256k1BaseFromBytes bs))
from-bytes-value secp256k1-scalar bs = just (val-secp256k1-scalar (secp256k1ScalarFromBytes bs))
from-bytes-value secp256r1-base bs = just (val-secp256r1-base (secp256r1BaseFromBytes bs))
from-bytes-value secp256r1-scalar bs = just (val-secp256r1-scalar (secp256r1ScalarFromBytes bs))
from-bytes-value curve25519-base bs = just (val-curve25519-base (curve25519BaseFromBytes bs))
from-bytes-value curve25519-scalar bs = just (val-curve25519-scalar (curve25519ScalarFromBytes bs))
from-bytes-value jubjub-point bs =
  as-vector 32 bs >>= λ raw →
  jubjubPointFromBytes raw >>= λ point →
  guardD (bs ≟B toList (jubjubPointToBytes point)) (just (val-jubjub-point point))
from-bytes-value secp256k1-point bs =
  map-maybe val-secp256k1-point
    (sec1-point _≟K1_ idK1 secp256k1PointToBytes secp256k1PointFromBytes bs)
from-bytes-value secp256r1-point bs =
  map-maybe val-secp256r1-point
    (sec1-point _≟P_ idP secp256r1PointToBytes secp256r1PointFromBytes bs)
from-bytes-value curve25519-point bs =
  as-vector 32 bs >>= λ raw →
  curve25519PointFromBytes raw >>= λ point →
  guardD (bs ≟B toList (curve25519PointToBytes point)) (just (val-curve25519-point point))
from-bytes-value _ _ = nothing

bytes32-from-parts : IrValue → IrValue → Maybe (List Byte)
bytes32-from-parts low high =
  to-bytes-value low >>= λ lo →
  to-bytes-value high >>= λ hi →
  guardD (length lo ≟ 32) (guardD (length hi ≟ 32)
    (guardD (drop 31 lo ≟B (F.zero ∷ []))
      (guardD (drop 1 hi ≟B replicate 31 F.zero)
        (just (take 31 lo ++ take 1 hi)))))

write : Identifier → IrValue → Maybe (List (Identifier × IrValue))
write id v = just ((id , v) ∷ [])

-- Pair the outputs with their values, checking the instruction's arity.
writes : List Identifier → List IrValue → Maybe (List (Identifier × IrValue))
writes [] [] = just []
writes (id ∷ ids) (v ∷ vs) =
  writes ids vs >>= λ ws → just ((id , v) ∷ ws)
writes _ _ = nothing

-- The circuit uses canonical bit decompositions through FR-BITS.  The
-- VM has additional opcode-specific bounds on the requested bit count.
bounded-compute : Mem → Instruction → Maybe (List (Identifier × IrValue))
bounded-compute m (constrain-bits val bits) =
  resolveᶠ m val >>= λ x →
  guardD (valFr x <? 2 ^ bits) (just [])
bounded-compute m (div-mod-power-of-two val bits outs) =
  resolveᶠ m val >>= λ x →
  let L = to-le-bits x in
  writes outs (val-native (from-le-bits (drop bits L))
            ∷ val-native (from-le-bits (take bits L)) ∷ [])
bounded-compute m (reconstitute-field divisor modulus bits output) =
  resolveᶠ m divisor >>= λ d →
  resolveᶠ m modulus >>= λ mo →
  guardD (valFr mo <? 2 ^ bits)
    (guardD (valFr d <? 2 ^ (FR-BITS ∸ bits))
      (guardD (valFr mo + 2 ^ bits * valFr d <? FR-ORDER)
        (write output (val-native ((pow2ᶠ bits *ᶠ d) +ᶠ mo)))))
bounded-compute _ _ = nothing

preprocess-bit-bounds : Instruction → Bool
preprocess-bit-bounds (constrain-bits _ bits) = isYes (bits <? FR-BITS)
preprocess-bit-bounds (div-mod-power-of-two _ bits _) = isYes (bits ≤? 248)
preprocess-bit-bounds (reconstitute-field _ _ bits _) =
  isYes (bits ≤? 248) ∧ isYes (bits <? FR-BITS) ∧ isYes (FR-BITS ∸ bits <? FR-BITS)
preprocess-bit-bounds _ = false

preprocess-bounded : Mem → Instruction → Maybe (List (Identifier × IrValue))
preprocess-bounded m i =
  if preprocess-bit-bounds i then bounded-compute m i else nothing

copy-value : IrValue → Maybe IrValue
copy-value = λ
  { (val-accumulator _) → nothing
  ; v → just v }

ec-mul-value : IrValue → IrValue → Maybe IrValue
ec-mul-value pv sv =
  case (pv , sv) of λ
  { (val-jubjub-point p , val-jubjub-scalar s) →
      just (val-jubjub-point (s ·J p))
  ; (val-secp256k1-point p , val-secp256k1-scalar s) →
      just (val-secp256k1-point (s ·K1 p))
  ; (val-secp256r1-point p , val-secp256r1-scalar s) →
      just (val-secp256r1-point (s ·P p))
  ; (val-curve25519-point p , val-curve25519-scalar s) →
      just (val-curve25519-point (s ·C p))
  ; _ → nothing }

ec-mul-generator-value : IrValue → Maybe IrValue
ec-mul-generator-value sv =
  case sv of λ
  { (val-jubjub-scalar s) →
      just (val-jubjub-point (s ·J genJ))
  ; (val-secp256k1-scalar s) →
      just (val-secp256k1-point (s ·K1 genK1))
  ; (val-secp256r1-scalar s) →
      just (val-secp256r1-point (s ·P genP))
  ; (val-curve25519-scalar s) →
      just (val-curve25519-point (s ·C genC))
  ; _ → nothing }

into-coordinates-value : IrValue → Maybe (IrValue × IrValue)
into-coordinates-value pv =
  case pv of λ
  { (val-jubjub-point p) →
      let (x , y) = coordsJ p in
      just (val-native x , val-native y)
  ; (val-secp256k1-point p) →
      -- Errors on the Weierstrass identity (`coordsK1` is `nothing`
      -- exactly there).
      coordsK1 p >>= λ (x , y) →
      just (val-secp256k1-base x , val-secp256k1-base y)
  ; (val-secp256r1-point p) →
      -- Errors on the Weierstrass identity (`coordsP` is `nothing`
      -- exactly there).
      coordsP p >>= λ (x , y) →
      just (val-secp256r1-base x , val-secp256r1-base y)
  ; (val-curve25519-point p) →
      -- Total: the Edwards identity has real affine coordinates, so
      -- (unlike the Weierstrass curves above) `coordsC` never fails.
      let (x , y) = coordsC p in
      just (val-curve25519-base x , val-curve25519-base y)
  ; _ → nothing }

from-coordinates-value : IrValue → IrValue → Maybe IrValue
from-coordinates-value xv yv =
  case (xv , yv) of λ
  { (val-native x , val-native y) →
      fromCoordsJ x y >>= λ p →
      just (val-jubjub-point p)
  ; (val-secp256k1-base x , val-secp256k1-base y) →
      fromCoordsK1 x y >>= λ p →
      just (val-secp256k1-point p)
  ; (val-secp256r1-base x , val-secp256r1-base y) →
      fromCoordsP x y >>= λ p →
      just (val-secp256r1-point p)
  ; (val-curve25519-base x , val-curve25519-base y) →
      fromCoordsC x y >>= λ p →
      just (val-curve25519-point p)
  ; _ → nothing }

add-value : IrValue → IrValue → Maybe IrValue
add-value av bv =
  case (av , bv) of λ
  { (val-native x , val-native y) →
      just (val-native (x +ᶠ y))
  ; (val-jubjub-scalar x , val-jubjub-scalar y) →
      just (val-jubjub-scalar (x +Jˢ y))
  ; (val-jubjub-point p , val-jubjub-point q) →
      just (val-jubjub-point (p +J q))
  ; (val-secp256k1-point p , val-secp256k1-point q) →
      just (val-secp256k1-point (p +K1 q))
  ; (val-secp256k1-base x , val-secp256k1-base y) →
      just (val-secp256k1-base (x +K1ᵇ y))
  ; (val-secp256k1-scalar x , val-secp256k1-scalar y) →
      just (val-secp256k1-scalar (x +K1ˢ y))
  ; (val-secp256r1-point p , val-secp256r1-point q) →
      just (val-secp256r1-point (p +P q))
  ; (val-secp256r1-base x , val-secp256r1-base y) →
      just (val-secp256r1-base (x +Pᵇ y))
  ; (val-secp256r1-scalar x , val-secp256r1-scalar y) →
      just (val-secp256r1-scalar (x +Pˢ y))
  ; (val-curve25519-point p , val-curve25519-point q) →
      just (val-curve25519-point (p +C q))
  ; (val-curve25519-base x , val-curve25519-base y) →
      just (val-curve25519-base (x +Cᵇ y))
  ; (val-curve25519-scalar x , val-curve25519-scalar y) →
      just (val-curve25519-scalar (x +Cˢ y))
  ; _ → nothing }

mul-value : IrValue → IrValue → Maybe IrValue
mul-value av bv =
  case (av , bv) of λ
  { (val-native x , val-native y) →
      just (val-native (x *ᶠ y))
  ; (val-jubjub-scalar x , val-jubjub-scalar y) →
      just (val-jubjub-scalar (x *Jˢ y))
  ; (val-secp256k1-base x , val-secp256k1-base y) →
      just (val-secp256k1-base (x *K1ᵇ y))
  ; (val-secp256k1-scalar x , val-secp256k1-scalar y) →
      just (val-secp256k1-scalar (x *K1ˢ y))
  ; (val-secp256r1-base x , val-secp256r1-base y) →
      just (val-secp256r1-base (x *Pᵇ y))
  ; (val-secp256r1-scalar x , val-secp256r1-scalar y) →
      just (val-secp256r1-scalar (x *Pˢ y))
  ; (val-curve25519-base x , val-curve25519-base y) →
      just (val-curve25519-base (x *Cᵇ y))
  ; (val-curve25519-scalar x , val-curve25519-scalar y) →
      just (val-curve25519-scalar (x *Cˢ y))
  ; _ → nothing }

neg-value : IrValue → Maybe IrValue
neg-value av =
  case av of λ
  { (val-native x)       → just (val-native (-ᶠ x))
  ; (val-bool b)         → just (val-bool (bnot b))
  ; (val-jubjub-scalar x) → just (val-jubjub-scalar (-Jˢ x))
  ; (val-jubjub-point p) → just (val-jubjub-point (negJ p))
  ; (val-secp256k1-point p)   → just (val-secp256k1-point (negK1 p))
  ; (val-secp256k1-base x)    → just (val-secp256k1-base (-K1ᵇ x))
  ; (val-secp256k1-scalar x)  → just (val-secp256k1-scalar (-K1ˢ x))
  ; (val-secp256r1-point p) →
      just (val-secp256r1-point (negP p))
  ; (val-secp256r1-base x) →
      just (val-secp256r1-base (-Pᵇ x))
  ; (val-secp256r1-scalar x) →
      just (val-secp256r1-scalar (-Pˢ x))
  ; (val-curve25519-point p) →
      just (val-curve25519-point (negC p))
  ; (val-curve25519-base x) →
      just (val-curve25519-base (-Cᵇ x))
  ; (val-curve25519-scalar x) →
      just (val-curve25519-scalar (-Cˢ x))
  ; _ → nothing }

inv-value : IrValue → Maybe IrValue
inv-value av =
  case av of λ
  { (val-native x) →
      invᶠ x >>= λ xi → just (val-native xi)
  ; (val-jubjub-scalar x) →
      invJˢ x >>= λ xi → just (val-jubjub-scalar xi)
  ; (val-secp256k1-base x) →
      invK1ᵇ x >>= λ xi → just (val-secp256k1-base xi)
  ; (val-secp256k1-scalar x) →
      invK1ˢ x >>= λ xi → just (val-secp256k1-scalar xi)
  ; (val-secp256r1-base x) →
      invPᵇ x >>= λ xi → just (val-secp256r1-base xi)
  ; (val-secp256r1-scalar x) →
      invPˢ x >>= λ xi → just (val-secp256r1-scalar xi)
  ; (val-curve25519-base x) →
      invCᵇ x >>= λ xi → just (val-curve25519-base xi)
  ; (val-curve25519-scalar x) →
      invCˢ x >>= λ xi → just (val-curve25519-scalar xi)
  ; _ → nothing }

compute : Mem → Instruction → Maybe (List (Identifier × IrValue))
compute m = go
  where
  gate : (Bool → Bool → Bool) → Bool → List Operand → Identifier →
         Maybe (List (Identifier × IrValue))
  gate f unit [] output = nothing
  gate f unit ops output =
    resolve-typed-bools m ops >>= λ bs →
    write output (val-bool (foldr f unit bs))

  reverse-value : Operand → Identifier → Maybe (List (Identifier × IrValue))
  reverse-value input output =
    resolve-bytes m input >>= λ bs → write output (val-bytes (reverse-list bs))

  go : Instruction → Maybe (List (Identifier × IrValue))
  go (encode input outs) =
    resolve m input >>= λ v →
    writes outs (map val-native (encodeᵉ v))

  go (assert cond) =
    resolve𝔹 m cond >>= λ b → if b then just [] else nothing

  go (cond-select bit a b output) =
    resolve𝔹 m bit >>= λ bv →
    resolve m a    >>= λ av →
    resolve m b    >>= λ bvl →
    guardD (typeof av ≟T typeof bvl)
      (write output (if bv then av else bvl))

  go i@(constrain-bits _ _) = preprocess-bounded m i

  go (constrain-eq a b) =
    resolve m a >>= λ av →
    resolve m b >>= λ bv →
    constrainEq? av bv >>= λ eq → if eq then just [] else nothing

  go (constrain-to-boolean val) =
    resolve𝔹 m val >>= λ _ → just []

  go (copy val output) =
    (resolve m val >>= copy-value) >>= write output

  go (ec-mul a scalar output) =
    resolve m a      >>= λ pv →
    resolve m scalar >>= λ sv →
    ec-mul-value pv sv >>= write output

  go (ec-mul-generator scalar output) =
    resolve m scalar >>= λ sv →
    ec-mul-generator-value sv >>= write output

  go (hash-to-curve inputs output) =
    resolve-all-Fr m inputs >>= λ frs →
    write output (val-jubjub-point (hash-to-curve-fn frs))

  go (into-coordinates point (xid , yid)) =
    resolve m point >>= λ pv →
    into-coordinates-value pv >>= λ (x , y) →
    just ((xid , x) ∷ (yid , y) ∷ [])

  go (from-coordinates (xop , yop) output) =
    resolve m xop >>= λ xv →
    resolve m yop >>= λ yv →
    from-coordinates-value xv yv >>= write output

  go (into-bytes32 input output) =
    resolve m input >>= to-bytes-value >>= λ bs →
    guardD (length bs ≟ 32) (write output (val-bytes bs))

  go (from-bytes32 input val-t output) =
    resolve-bytes m input >>= λ bs →
    guardD (length bs ≟ 32) (from-bytes-value val-t bs >>= write output)

  go (reverse-bytes input output) =
    reverse-value input output

  go (bytes32-into-low-high input (lo , hi)) =
    resolve-bytes m input >>= λ bs →
    guardD (length bs ≟ 32)
      (writes (lo ∷ hi ∷ []) (map val-native (pack-bytes bs)))

  go (bytes32-from-low-high (lo , hi) output) =
    resolve m lo >>= λ l →
    resolve m hi >>= λ h →
    bytes32-from-parts l h >>= λ bs →
    write output (val-bytes bs)

  go (slice input start len output) =
    resolve-bytes m input >>= λ bs →
    guardD (0 <? len)
      (guardD (start + len ≤? length bs)
        (write output (val-bytes (take len (drop start bs)))))

  go (nth input index output) =
    resolve-bytes m input >>= λ bs →
    at bs index >>= λ b → write output (val-byte b)

  go (concat inputs output) =
    resolve-concat m inputs >>= λ bs →
    if valid-bytes-length (length bs) then write output (val-bytes bs) else nothing

  go (reverse input output) =
    reverse-value input output

  go (load-constant val-t encoding output) =
    decode val-t encoding >>= write output

  go (sha512 alignment inputs output) =
    resolve-all-Fr m inputs >>= λ frs →
    sha512-fn alignment frs >>= λ hash →
    write output (val-bytes (toList hash))

  go (and inputs output) = gate _∧_ true inputs output
  go (or inputs output) = gate _∨_ false inputs output
  go (xor inputs output) = gate _xor_ false inputs output

  go (to-bytes input output) =
    resolve m input >>= to-bytes-value >>= λ bs → write output (val-bytes bs)

  go (from-bytes input val-t output) =
    resolve-bytes m input >>= from-bytes-value val-t >>= write output

  go (bytes-into-natives input outs) =
    resolve-bytes m input >>= λ bs →
    writes outs (map val-native (pack-bytes bs))

  go (bytes-from-natives inputs len output) =
    resolve-all-Fr m inputs >>= λ fs →
    decode (bytes len) fs >>= write output

  go i@(div-mod-power-of-two _ _ _) = preprocess-bounded m i
  go i@(reconstitute-field _ _ _ _) = preprocess-bounded m i

  go (transient-hash inputs output) =
    resolve-all-Fr m inputs >>= λ frs →
    write output (val-native (transient-hash-fn frs))

  go (persistent-hash alignment inputs output) =
    resolve-all-Fr m inputs >>= λ frs →
    persistent-hash-fn alignment frs >>= λ h →
    write output (val-bytes32 h)

  go (keccak256 alignment inputs output) =
    resolve-all-Fr m inputs >>= λ frs →
    keccak-fn alignment frs >>= λ h →
    write output (val-bytes32 h)

  go (test-eq a b output) =
    resolve m a  >>= λ av →
    resolve m b  >>= λ bv →
    valEq? av bv >>= λ eq →
    write output (val-native (χ eq))

  go (add a b output) =
    resolve m a >>= λ av →
    resolve m b >>= λ bv →
    add-value av bv >>= write output

  go (mul a b output) =
    resolve m a >>= λ av →
    resolve m b >>= λ bv →
    mul-value av bv >>= write output

  go (neg a output) =
    resolve m a >>= λ av →
    neg-value av >>= write output

  go (inv a output) =
    resolve m a >>= λ av →
    inv-value av >>= write output

  go (not a output) =
    resolve𝔹 m a >>= λ b →
    write output (val-native (χ (bnot b)))

  go (less-than a b bits output) =
    resolveᶠ m a >>= λ x →
    resolveᶠ m b >>= λ y →
    guardD (bits <? FR-BITS)
      (guardD (valFr x <? 2 ^ bits)
        (guardD (valFr y <? 2 ^ bits)
          (write output (val-native (χ (isYes (valFr x <? valFr y)))))))

  go (jubjub-scalar-from-native a output) =
    resolveᶠ m a >>= λ x →
    write output (val-jubjub-scalar (native→jubjubScalar x))

  -- These instructions are interpreted by the stateful caller.
  go (impact _ _) = nothing
  go (public-input _ _ _) = nothing
  go (private-input _ _ _) = nothing
  go (circuit-output _) = nothing
  go (inner-proof _ _) = nothing
  go (prepare-verification _ _ _ _ _) = nothing
  go (accumulate _ _) = nothing
  go (verify-accumulator _) = nothing
