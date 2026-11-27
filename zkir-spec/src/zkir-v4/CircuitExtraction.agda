{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.CircuitExtraction (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Circuit ⋯
open import zkir-v4.Encoding ⋯ using () renaming (encode to encode-value)
open import zkir-v4.Operations ⋯ using (eval-guard; resolve𝔹; resolve-all-Fr)
open import zkir-v4.Semantics ⋯ using (ProofPreimage)
open import zkir-v4.Syntax ⋯
open import zkir-v4.ProofSlots using (keep)

open import Data.Bool using (if_then_else_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)

-- One fragment records the data consumed by a prefix of instructions.
-- Appending fragments preserves the stream order for each stream.
record Fragment : Set where
  constructor fragment
  field
    impacts       : List Fr
    public-reads  : List Fr
    private-reads : List Fr
    proofs        : List (List Byte)

empty : Fragment
empty = fragment [] [] [] []

append : Fragment → Fragment → Fragment
append (fragment as bs cs ds) (fragment es fs gs hs) =
  fragment (as ++ es) (bs ++ fs) (cs ++ gs) (ds ++ hs)

-- Read each event from the circuit cells in scope at that instruction.
-- A skipped proof read still records a slot.  Its canonical bytes are
-- empty, irrespective of the bytes supplied to synthesis.
event : CircuitState → CircuitState → Instruction → Maybe Fragment
event before after (impact g ops) =
  resolve𝔹 (CircuitState.mem before) g >>= λ active →
  if active
  then (resolve-all-Fr (CircuitState.mem before) ops >>= λ values →
        just (record empty { impacts = values }))
  else just empty
event before after (public-input g _ id) =
  eval-guard (CircuitState.mem before) g >>= λ active →
  if active
  then (CircuitState.mem after id >>= λ value →
        just (record empty { public-reads = encode-value value }))
  else just empty
event before after (private-input g _ id) =
  eval-guard (CircuitState.mem before) g >>= λ active →
  if active
  then (CircuitState.mem after id >>= λ value →
        just (record empty { private-reads = encode-value value }))
  else just empty
event before after (inner-proof g id) =
  resolve𝔹 (CircuitState.mem before) g >>= λ active →
  CircuitState.proofs after id >>= λ bytes →
  just (record empty { proofs = keep active bytes ∷ [] })
event _ _ _ = just empty

gather : IrSource → CircuitWitness → CircuitState → List Instruction → Maybe Fragment
gather src w st [] = just empty
gather src w st (i ∷ is) =
  stepᶜ src w st (lower i) >>= λ next →
  event st next i >>= λ first →
  gather src w next is >>= λ rest →
  just (append first rest)

extract : IrSource → CircuitWitness → Maybe ProofPreimage
extract src w =
  check-circuit src w >>= λ _ →
  initᶜ src w >>= λ start →
  gather src w start (IrSource.instructions src) >>= λ stream →
  just (record
    { inputs = encode-inputs (CircuitState.mem start) (IrSource.inputs src)
    ; binding-input = CircuitWitness.binding-input w
    ; comm-commitment = if IrSource.do-communications-commitment src
                         then CircuitWitness.comm-commitment w else nothing
    ; pub-transcript-inputs = Fragment.impacts stream
    ; pub-transcript-outputs = Fragment.public-reads stream
    ; priv-transcript = Fragment.private-reads stream
    ; inner-proofs = Fragment.proofs stream
    })
