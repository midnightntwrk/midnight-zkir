{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.Producer (⋯ : _) (open Assumptions ⋯) where

open import zkir-v4.Types ⋯
open import zkir-v4.Syntax ⋯
open import zkir-v4.Validation ⋯ using (validate)
open import Data.Bool.Base as B using (Bool; true; false; _∧_; _∨_; T)
open import Data.Bool.ListAction using (all; any)
open import Data.Bool.Properties using (T?)
open import Data.List.Base as L using (List; []; _∷_; _++_; length; map)
open import Data.Maybe.Base as M using (Maybe; just; nothing; _>>=_)
open import Data.Nat.Base using (ℕ; _+_; _≤ᵇ_; _<ᵇ_)
import Data.Nat.Properties as N
open import Data.Product.Base using (_×_; _,_)
import Data.String.Properties as Strings
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (does)

-- Typing for producers.  The Rust chip-selection pass infers result types
-- under the producer's invariant.  This check also validates operands and
-- single assignment, including the names of all simultaneous outputs.
Env = List TypedIdentifier

infixl 1 _>>_
_>>_ : ∀ {A B : Set} → Maybe A → Maybe B → Maybe B
x >> y = x >>= λ _ → y

demand : Bool → Maybe ⊤
demand true = just tt
demand false = nothing

equal : IrType → IrType → Bool
equal a b = does (a ≟T b)

type-of : Env → Identifier → Maybe IrType
type-of [] id = nothing
type-of ((x ⦂ t) ∷ xs) id with x Strings.≟ id
... | yes _ = just t
... | no _ = type-of xs id

fresh : Env → TypedIdentifier → Maybe Env
fresh Γ (id ⦂ t) with type-of Γ id
... | just _ = nothing
... | nothing = demand (valid-type t) >> just ((id ⦂ t) ∷ Γ)

check-list : ∀ {A B : Set} → (A → Maybe B) → List A → Maybe (List B)
check-list f [] = just []
check-list f (x ∷ xs) = do
  b ← f x
  bs ← check-list f xs
  just (b ∷ bs)

fold-check : ∀ {A B : Set} → (B → A → Maybe B) → B → List A → Maybe B
fold-check f b [] = just b
fold-check f b (x ∷ xs) = f b x >>= λ b′ → fold-check f b′ xs

field-type : IrType → Bool
field-type native = true
field-type jubjub-scalar = true
field-type secp256k1-base = true
field-type secp256k1-scalar = true
field-type secp256r1-base = true
field-type secp256r1-scalar = true
field-type curve25519-base = true
field-type curve25519-scalar = true
field-type _ = false

-- First component is the scalar type.  Second is the coordinate type.
curve : IrType → Maybe (IrType × IrType)
curve jubjub-point = just (jubjub-scalar , native)
curve secp256k1-point = just (secp256k1-scalar , secp256k1-base)
curve secp256r1-point = just (secp256r1-scalar , secp256r1-base)
curve curve25519-point = just (curve25519-scalar , curve25519-base)
curve _ = nothing

from-scalar : IrType → Maybe IrType
from-scalar jubjub-scalar = just jubjub-point
from-scalar secp256k1-scalar = just secp256k1-point
from-scalar secp256r1-scalar = just secp256r1-point
from-scalar curve25519-scalar = just curve25519-point
from-scalar _ = nothing

from-base : IrType → Maybe IrType
from-base native = just jubjub-point
from-base secp256k1-base = just secp256k1-point
from-base secp256r1-base = just secp256r1-point
from-base curve25519-base = just curve25519-point
from-base _ = nothing

arithmetic : IrType → Bool
arithmetic t = field-type t ∨ M.is-just (curve t)

selectable : IrType → Bool
selectable (bytes _) = false
selectable accumulator = false
selectable _ = true

width : IrType → Maybe ℕ
width (bytes n) = just n
width _ = nothing

concat-width : IrType → Maybe ℕ
concat-width byte = just 1
concat-width t = width t

repr-width : IrType → Maybe ℕ
repr-width secp256k1-point = just 33
repr-width secp256r1-point = just 33
repr-width t = demand (arithmetic t) >> just 32

from-width : ℕ → IrType → Bool
from-width n t with repr-width t
... | nothing = false
... | just w = field-type t ∨ does (n N.≟ w)

eq-types : List IrType → List IrType → Bool
eq-types [] [] = true
eq-types (t ∷ ts) (u ∷ us) = equal t u ∧ eq-types ts us
eq-types _ _ = false

-- Number of native operands consumed by the RC1 FAB synthesis walk.
alignment-width : Alignment → Maybe ℕ
alignment-width [] = just 0
alignment-width (field-atom ∷ rest) = M.map (1 +_) (alignment-width rest)
alignment-width (bytes-atom n ∷ rest) = M.map (bytes-encoded-len n +_) (alignment-width rest)
alignment-width (compress-atom ∷ _) = nothing
alignment-width (option _ ∷ _) = nothing

-- Returns the bindings to be added by one instruction.
module _ (signature : List IrType) (Γ : Env) where
  ty : Operand → Maybe IrType
  ty (imm _) = just native
  ty (var x) = type-of Γ x

  expect : IrType → Operand → Maybe ⊤
  expect t op = ty op >>= λ u → demand (equal t u)

  expect-all : IrType → List Operand → Maybe ⊤
  expect-all t os = check-list (expect t) os >> just tt

  aligned-inputs : Alignment → List Operand → Maybe ⊤
  aligned-inputs alignment ops = do
    n ← alignment-width alignment
    demand (does (length ops N.≟ n))
    expect-all native ops

  guard-ty : Maybe Operand → Maybe ⊤
  guard-ty nothing = just tt
  guard-ty (just op) = expect native op

  one : Identifier → IrType → Maybe Env
  one x t = just ((x ⦂ t) ∷ [])

  unary : (IrType → Bool) → Operand → Identifier → Maybe Env
  unary ok x o = ty x >>= λ t → demand (ok t) >> one o t

  binary : (IrType → Bool) → Operand → Operand → Identifier → Maybe Env
  binary ok x y o = ty x >>= λ t → expect t y >> demand (ok t) >> one o t

  bools : List Operand → Identifier → Maybe Env
  bools [] o = nothing
  bools xs o = expect-all bool xs >> one o bool

  natives : ℕ → List Identifier → Maybe Env
  natives n xs = demand (does (length xs N.≟ n)) >> just (map (_⦂ native) xs)

  bytelen : Operand → Maybe ℕ
  bytelen x = ty x >>= width

  transcript : Maybe Operand → IrType → Identifier → Maybe Env
  transcript g t o = guard-ty g >> one o t

  bindings : Instruction → Maybe Env
  bindings (encode x os) = ty x >>= λ t → natives (encoded-len t) os
  bindings (assert x) = expect native x >> just []
  bindings (cond-select g a b o) = expect native g >> binary selectable a b o
  bindings (constrain-bits x n) = expect native x >> demand (n <ᵇ FR-BITS) >> just []
  bindings (constrain-eq x y) = do
    t ← ty x
    expect t y
    demand (B.not (equal t accumulator))
    just []
  bindings (constrain-to-boolean x) = expect native x >> just []
  bindings (copy x o) = unary (λ t → B.not (equal t accumulator)) x o
  bindings (impact g xs) = expect native g >> expect-all native xs >> just []
  bindings (ec-mul p s o) = do
    t ← ty p
    (scalar , _) ← curve t
    expect scalar s
    one o t
  bindings (ec-mul-generator s o) = ty s >>= from-scalar >>= one o
  bindings (hash-to-curve xs o) = expect-all native xs >> one o jubjub-point
  bindings (into-coordinates p (x , y)) = do
    t ← ty p
    (_ , coord) ← curve t
    just ((x ⦂ coord) ∷ (y ⦂ coord) ∷ [])
  bindings (from-coordinates (x , y) o) = do
    t ← ty x
    expect t y
    from-base t >>= one o
  bindings (into-bytes32 x o) = do
    n ← ty x >>= repr-width
    demand (does (n N.≟ 32))
    one o bytes32
  bindings (from-bytes32 x t o) = expect bytes32 x >> demand (from-width 32 t) >> one o t
  bindings (reverse-bytes x o) = bytelen x >>= λ n → one o (bytes n)
  bindings (bytes32-into-low-high x (lo , hi)) = expect bytes32 x >> natives 2 (lo ∷ hi ∷ [])
  bindings (bytes32-from-low-high (lo , hi) o) = expect native lo >> expect native hi >> one o bytes32
  bindings (div-mod-power-of-two x n os) = expect native x >> demand (n ≤ᵇ 248) >> natives 2 os
  bindings (reconstitute-field d m n o) =
    expect native d >> expect native m >> demand ((0 <ᵇ n) ∧ (n ≤ᵇ 248)) >> one o native
  bindings (transient-hash xs o) = expect-all native xs >> one o native
  bindings (persistent-hash a xs o) = aligned-inputs a xs >> one o bytes32
  bindings (keccak256 a xs o) = aligned-inputs a xs >> one o bytes32
  bindings (test-eq x y o) = do
    t ← ty x
    expect t y
    demand (B.not (equal t accumulator))
    one o native
  bindings (add x y o) = binary arithmetic x y o
  bindings (mul x y o) = binary field-type x y o
  bindings (neg x o) = unary (λ t → arithmetic t ∨ equal t bool) x o
  bindings (inv x o) = unary field-type x o
  bindings (not x o) = expect native x >> one o native
  bindings (less-than x y n o) = expect native x >> expect native y >> demand (n <ᵇ FR-BITS) >> one o native
  bindings (jubjub-scalar-from-native x o) = expect native x >> one o jubjub-scalar
  bindings (public-input g t o) = transcript g t o
  bindings (private-input g t o) = transcript g t o
  bindings (circuit-output xs) = check-list ty xs >>= λ ts → demand (eq-types ts signature) >> just []
  bindings (slice x start n o) = do
    w ← bytelen x
    demand (valid-bytes-length n ∧ ((start + n) ≤ᵇ w))
    one o (bytes n)
  bindings (nth x k o) = bytelen x >>= λ w → demand (k <ᵇ w) >> one o byte
  bindings (concat xs o) = do
    ws ← check-list (λ x → ty x >>= concat-width) xs
    let n = L.foldr _+_ 0 ws
    demand (valid-bytes-length n)
    one o (bytes n)
  bindings (reverse x o) = bytelen x >>= λ n → one o (bytes n)
  bindings (load-constant t raw o) = demand (does (length raw N.≟ encoded-len t)) >> one o t
  bindings (sha512 a xs o) = aligned-inputs a xs >> one o (bytes 64)
  bindings (and xs o) = bools xs o
  bindings (or xs o) = bools xs o
  bindings (xor xs o) = bools xs o
  bindings (to-bytes x o) = ty x >>= repr-width >>= λ n → one o (bytes n)
  bindings (from-bytes x t o) = bytelen x >>= λ n → demand (from-width n t) >> one o t
  bindings (bytes-into-natives x os) = bytelen x >>= λ n → natives (bytes-encoded-len n) os
  bindings (bytes-from-natives xs n o) = do
    demand (valid-bytes-length n ∧ does (length xs N.≟ bytes-encoded-len n))
    expect-all native xs
    one o (bytes n)
  bindings (inner-proof g _) = expect native g >> just []
  bindings (prepare-verification g _ xs _ o) = expect native g >> expect-all native xs >> one o accumulator
  bindings (accumulate xs o) = demand (2 ≤ᵇ length xs) >> expect-all accumulator xs >> one o accumulator
  bindings (verify-accumulator x) = expect accumulator x >> just []

producer-step : List IrType → Env → Instruction → Maybe Env
producer-step signature Γ i = bindings signature Γ i >>= fold-check fresh Γ

infer : IrSource → Maybe Env
infer s = do
  demand (all valid-type (IrSource.outputs s))
  Γ ← fold-check fresh [] (IrSource.inputs s)
  fold-check (producer-step (IrSource.outputs s)) Γ (IrSource.instructions s)

-- A producer ends a value-returning source with one Output.  The
-- executable VM accepts additional programs and appends every Output.
output-placement : List IrType → List Instruction → Bool
output-placement [] [] = true
output-placement (_ ∷ _) [] = false
output-placement _ (circuit-output _ ∷ []) = true
output-placement _ (circuit-output _ ∷ _ ∷ _) = false
output-placement ts (_ ∷ is) = output-placement ts is

admissible : IrSource → Bool
admissible s = validate s ∧ M.is-just (infer s) ∧ output-placement (IrSource.outputs s) (IrSource.instructions s)

Producer : IrSource → Set
Producer s = T (admissible s)

producer? : (s : IrSource) → Dec (Producer s)
producer? s = T? (admissible s)

-- Architecture selected for a well-typed source.  The final environment
-- contains every declared and intermediate type under single assignment.
data Chip : Set where
  jubjub secp256k1 p256 curve25519 bls12-381 poseidon sha2-256 sha2-512 keccak-256 : Chip

private
  uses-type : Chip → IrType → Bool
  uses-type jubjub jubjub-scalar = true
  uses-type jubjub jubjub-point = true
  uses-type secp256k1 secp256k1-point = true
  uses-type secp256k1 secp256k1-base = true
  uses-type secp256k1 secp256k1-scalar = true
  uses-type p256 secp256r1-point = true
  uses-type p256 secp256r1-base = true
  uses-type p256 secp256r1-scalar = true
  uses-type curve25519 curve25519-point = true
  uses-type curve25519 curve25519-base = true
  uses-type curve25519 curve25519-scalar = true
  uses-type bls12-381 accumulator = true
  uses-type poseidon accumulator = true
  uses-type _ _ = false

  uses-instruction : Chip → Instruction → Bool
  uses-instruction poseidon (transient-hash _ _) = true
  uses-instruction poseidon (hash-to-curve _ _) = true
  uses-instruction sha2-256 (persistent-hash _ _ _) = true
  uses-instruction sha2-512 (sha512 _ _ _) = true
  uses-instruction keccak-256 (keccak256 _ _ _) = true
  uses-instruction _ _ = false

  uses-commitment : Chip → Bool → Bool
  uses-commitment poseidon flag = flag
  uses-commitment _ _ = false

record Architecture : Set where
  field
    enabled : Chip → Bool
    range-check-groups : ℕ
    -- Nothing selects the backend's lane width for the circuit domain.
    range-check-bit-len : Maybe ℕ

architecture : IrSource → Maybe Architecture
architecture s = do
  Γ ← infer s
  just record
    { enabled = λ chip →
        uses-commitment chip (IrSource.do-communications-commitment s)
        ∨ any (λ ti → uses-type chip (TypedIdentifier.val-t ti)) Γ
        ∨ any (uses-instruction chip) (IrSource.instructions s)
    ; range-check-groups = 1
    ; range-check-bit-len = nothing }

-- ZKIR selects the same range-check configuration for every inferred source.
range-check-configuration : ∀ s {a} → architecture s ≡ just a →
  Architecture.range-check-groups a ≡ 1 × Architecture.range-check-bit-len a ≡ nothing
range-check-configuration s ok with infer s
... | nothing with () ← ok
... | just _ with refl ← ok = refl , refl
