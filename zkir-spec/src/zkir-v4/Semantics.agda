{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

-- Off-circuit execution.  The interpreter keeps typed values, proof bytes,
-- statement fields and exposed accumulators in separate stores.
module zkir-v4.Semantics (⋯ : _) (open Assumptions ⋯) where

open import zkir-v4.Types ⋯
open import zkir-v4.Syntax ⋯
open import zkir-v4.Encoding ⋯ using (decode; encode-accumulator) renaming (encode to encodeᵉ)
open import zkir-v4.Operations ⋯ public
open import zkir-v4.Validation ⋯ using (validate; resolve-vk)
open import zkir-v4.ProofSlots using (keep)

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; _+_; _≟_)
open import Data.List using (List; []; _∷_; _++_; length; take; drop; map; concatMap)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Product using (_×_; _,_)
open import Function using (case_of_)

record ProofPreimage : Set where
  field
    inputs                 : List Fr
    binding-input          : Fr
    comm-commitment        : Maybe (Fr × Fr)
    pub-transcript-inputs  : List Fr
    pub-transcript-outputs : List Fr
    priv-transcript        : List Fr
    inner-proofs           : List (List Byte)

record State : Set where
  field
    mem             : Mem
    pis             : List Fr
    acc-pis         : List Fr
    exposed         : List Accumulator
    pi-skips        : List (Maybe ℕ)
    pti-idx         : ℕ
    pto-rem         : List Fr
    priv-rem        : List Fr
    proofs          : ProofStore
    proof-rem       : List (List Byte)
    inner-witnesses : List (List Byte)
    outs            : List IrValue

-- The statement begins with the binding input and optional commitment.
-- Proof-carried accumulator fields are prepended to it for verification.
full-public-inputs : State → List Fr
full-public-inputs st = State.acc-pis st ++ State.pis st

out1 : State → Identifier → IrValue → State
out1 st id v = record st { mem = ins id v (State.mem st) }

collectOutputs : Mem → List IrType → List Operand → Maybe (List IrValue)
collectOutputs m []       []         = just []
collectOutputs m (t ∷ ts) (op ∷ ops) =
  resolve m op >>= λ v →
  guardD (typeof v ≟T t)
    (collectOutputs m ts ops >>= λ vs → just (v ∷ vs))
collectOutputs m _        _          = nothing

-- Decode from left to right.  Late writes have the same precedence as
-- Rust's store if the source repeats a name.
decode-inputs-from : Mem → List TypedIdentifier → List Fr → Maybe Mem
decode-inputs-from m [] [] = just m
decode-inputs-from m [] (_ ∷ _) = nothing
decode-inputs-from m (ti ∷ tis) raw =
  let t = TypedIdentifier.val-t ti in
  decode t (take (encoded-len t) raw) >>= λ v →
  decode-inputs-from (ins (TypedIdentifier.name ti) v m) tis (drop (encoded-len t) raw)

decode-inputs : List TypedIdentifier → List Fr → Maybe Mem
decode-inputs = decode-inputs-from ∅

-- The guard suppresses key parsing and proof preparation.  Name lookup
-- and instance operand resolution still happen on either branch.
prepare-result : IrSource → State → Operand → List Byte → List Operand → Identifier →
                 Maybe Accumulator
prepare-result S st guard vk-hash instances proof =
  let m = State.mem st in
  resolve𝔹 m guard >>= λ g →
  resolve-all-Fr m instances >>= λ values →
  State.proofs st proof >>= λ blob →
  resolve-vk vk-hash (IrSource.inner-vks S) >>= λ key →
  if g then
    (if key-well-formed key then prepare-active key values blob else nothing)
  else just trivial-accumulator

fold-result : Mem → List Operand → Maybe Accumulator
fold-result m inputs =
  resolve-accs m inputs >>= λ accs →
  case accs of λ
    { (_ ∷ _ ∷ _) → fold-accumulators accs
    ; _ → nothing }

step-with-inputs : List Fr → IrSource → State → Instruction → Maybe State
step-with-inputs pti S st (impact guard inputs) =
  resolve𝔹 (State.mem st) guard >>= λ g →
  let n = length inputs in
  if g
  then (resolve-all-Fr (State.mem st) inputs >>= λ vals →
        guardD (take n (drop (State.pti-idx st) pti)
                  ≟LFr vals)
          (just (record st { pis      = State.pis st ++ vals
                           ; pi-skips = State.pi-skips st ++ (nothing ∷ [])
                           ; pti-idx  = State.pti-idx st + n })))
  else just (record st { pis      = State.pis st ++ map (λ _ → 0ᶠ) inputs
                       ; pi-skips = State.pi-skips st ++ (just n ∷ []) })
step-with-inputs pti S st (public-input guard val-t output) =
  eval-guard (State.mem st) guard >>= λ g →
  if g
  then (let n = encoded-len val-t in
        decode val-t (take n (State.pto-rem st)) >>= λ v →
        just (record (out1 st output v) { pto-rem = drop n (State.pto-rem st) }))
  else just (out1 st output (default-val val-t))
step-with-inputs pti S st (private-input guard val-t output) =
  eval-guard (State.mem st) guard >>= λ g →
  if g
  then (let n = encoded-len val-t in
        decode val-t (take n (State.priv-rem st)) >>= λ v →
        just (record (out1 st output v) { priv-rem = drop n (State.priv-rem st) }))
  else just (out1 st output (default-val val-t))
step-with-inputs pti S st (inner-proof guard output) with State.proof-rem st
... | [] = nothing
... | raw ∷ remaining =
  resolve𝔹 (State.mem st) guard >>= λ g →
  let blob = keep g raw in
  just (record st { proofs = insert-proof output blob (State.proofs st)
                  ; proof-rem = remaining
                  ; inner-witnesses = State.inner-witnesses st ++ (blob ∷ []) })
step-with-inputs pti S st (prepare-verification guard vk-hash instances proof output) =
  prepare-result S st guard vk-hash instances proof >>= λ acc →
  just (out1 st output (val-accumulator acc))
step-with-inputs pti S st (accumulate inputs output) =
  fold-result (State.mem st) inputs >>= λ acc →
  just (out1 st output (val-accumulator acc))
step-with-inputs pti S st (verify-accumulator input) =
  resolve-acc (State.mem st) input >>= λ acc →
  just (record st { acc-pis = State.acc-pis st ++ encode-accumulator acc
                  ; exposed = State.exposed st ++ (acc ∷ []) })
step-with-inputs pti S st (circuit-output vals) =
  collectOutputs (State.mem st) (IrSource.outputs S) vals >>= λ vs →
  just (record st { outs = State.outs st ++ vs })
step-with-inputs pti S st i =
  compute (State.mem st) i >>= λ ws →
  just (record st { mem = apply-writes (State.mem st) ws })

step : ProofPreimage → IrSource → State → Instruction → Maybe State
step P = step-with-inputs (ProofPreimage.pub-transcript-inputs P)

run : ProofPreimage → IrSource → State → List Instruction → Maybe State
run P S st []       = just st
run P S st (i ∷ is) = step P S st i >>= λ st′ → run P S st′ is

init : IrSource → ProofPreimage → Maybe State
init S P =
  decode-inputs (IrSource.inputs S) (ProofPreimage.inputs P) >>= λ m →
  let mk = λ pis → record { mem = m
                          ; pis = pis
                          ; acc-pis = []
                          ; exposed = []
                          ; pi-skips = []
                          ; pti-idx = 0
                          ; pto-rem = ProofPreimage.pub-transcript-outputs P
                          ; priv-rem = ProofPreimage.priv-transcript P
                          ; proofs = λ _ → nothing
                          ; proof-rem = ProofPreimage.inner-proofs P
                          ; inner-witnesses = []
                          ; outs = [] }
  in if IrSource.do-communications-commitment S
     then (case ProofPreimage.comm-commitment P of λ
            { (just (c , _)) → just (mk (ProofPreimage.binding-input P ∷ c ∷ []))
            ; nothing → nothing })
     else just (mk (ProofPreimage.binding-input P ∷ []))

check-commit : IrSource → ProofPreimage → State → Maybe State
check-commit S P st with IrSource.do-communications-commitment S
... | false = just st
... | true =
  ProofPreimage.comm-commitment P >>= λ (c , r) →
  guardD (c ≟ᶠ transient-commit
                (ProofPreimage.inputs P ++ concatMap encodeᵉ (State.outs st)) r)
    (just st)

finish : IrSource → ProofPreimage → State → Maybe State
finish S P st with State.pto-rem st | State.priv-rem st | State.proof-rem st
... | [] | [] | [] =
  guardD (State.pti-idx st ≟ length (ProofPreimage.pub-transcript-inputs P))
    (check-commit S P st)
... | _ | _ | _ = nothing

preprocess : IrSource → ProofPreimage → Maybe State
preprocess S P with validate S
... | false = nothing
... | true =
  init S P >>= λ st₀ →
  run P S st₀ (IrSource.instructions S) >>= finish S P
