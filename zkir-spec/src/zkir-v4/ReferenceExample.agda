{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.ReferenceExample (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Types ⋯
open import zkir-v4.Syntax ⋯
open import zkir-v4.Semantics ⋯
open import zkir-v4.Encoding ⋯ using (decode) renaming (encode to fields)
open import zkir-v4.EncodingProperties ⋯ using (EncodingLaws; encode-decode)
open import Data.Bool using (false; true)
open import Data.Fin.Base as Fin using ()
open import Data.Nat as Nat using (ℕ)
open import Data.Nat.Properties using (m≤m+n)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)

-- The byte example in §7.1 of the reference.  Binding is symbolic so
-- the same reduction checks the fixture's value 99 and all other values.
module Packing (laws : EncodingLaws) (binding : Fr) where
  private
    zeros : List Byte
    zeros = replicate 31 Fin.zero
    last-byte : Byte
    last-byte = Fin.fromℕ< (m≤m+n 43 213)
    bytes32-value = val-bytes (zeros ++ last-byte ∷ [])
    raw = fields bytes32-value

  source : IrSource
  source = mk-ir-source V0 [] (bytes 32 ∷ []) false
    (load-constant (bytes 31) (fields (val-bytes zeros)) "%prefix" ∷
     load-constant byte (fields (val-byte last-byte)) "%last" ∷
     concat (var "%prefix" ∷ var "%last" ∷ []) "%bytes" ∷
     bytes-into-natives (var "%bytes") ("%lo" ∷ "%hi" ∷ []) ∷
     bytes-from-natives (var "%lo" ∷ var "%hi" ∷ []) 32 "%roundtrip" ∷
     constrain-eq (var "%bytes") (var "%roundtrip") ∷
     impact (imm 1ᶠ) (var "%lo" ∷ var "%hi" ∷ []) ∷
     circuit-output (var "%roundtrip" ∷ []) ∷ []) []

  preimage : ProofPreimage
  preimage = record
    { inputs = [] ; binding-input = binding ; comm-commitment = nothing
    ; pub-transcript-inputs = raw ; pub-transcript-outputs = []
    ; priv-transcript = [] ; inner-proofs = [] }

  private
    observe : State → List IrValue × List Fr × List (Maybe ℕ)
    observe st = State.outs st , full-public-inputs st , State.pi-skips st

  example : map observe (preprocess source preimage)
          ≡ just ((bytes32-value ∷ []) , (binding ∷ raw) , (nothing ∷ []))
  example rewrite encode-decode laws (val-bytes zeros) refl
                | encode-decode laws (val-byte last-byte) refl
                | encode-decode laws bytes32-value refl
    with 1ᶠ ≟ᶠ 0ᶠ
  ... | yes bad with () ← 1ᶠ≢0ᶠ bad
  ... | no _ with 1ᶠ ≟ᶠ 1ᶠ
  ...   | no bad with () ← bad refl
  ...   | yes _ with raw ≟LFr raw
  ...     | no bad with () ← bad refl
  ...     | yes _ = refl
