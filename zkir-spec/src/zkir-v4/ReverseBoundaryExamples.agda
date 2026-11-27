{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.ReverseBoundaryExamples (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Types ⋯
open import zkir-v4.Syntax ⋯
open import zkir-v4.Circuit ⋯
open import zkir-v4.CircuitBridge ⋯ using (view; write-agreed)
open import zkir-v4.CircuitEvents ⋯ using (inserted-value; inserted-proof)
open import zkir-v4.Semantics ⋯ using (State; step; ins)
open import Data.Bool using (true)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing; map)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)

-- A disabled public read installs zero in the interpreter.  The lowered
-- circuit checks the supplied Native cell and accepts one at the same name.
disabled-read : ∀ src p st slots id →
  let i = public-input (just (imm 0ᶠ)) native id
      w = mk-witness (λ _ → just (val-native 1ᶠ)) [] 0ᶠ nothing []
  in (map (λ after → State.mem after id) (step p src st i) ≡ just (just (val-native 0ᶠ)))
   × (map (λ after → CircuitState.mem after id) (stepᶜ src w (view st slots) (lower i))
      ≡ just (just (val-native 1ᶠ)))
disabled-read src p st slots id = interp , circuit
  where
  i = public-input (just (imm 0ᶠ)) native id
  w = mk-witness (λ _ → just (val-native 1ᶠ)) [] 0ᶠ nothing []

  interp : map (λ after → State.mem after id) (step p src st i) ≡ just (just (val-native 0ᶠ))
  interp with 0ᶠ ≟ᶠ 0ᶠ
  ... | yes _ rewrite inserted-value id (val-native 0ᶠ) (State.mem st) = refl
  ... | no different with () ← different refl

  circuit-step : stepᶜ src w (view st slots) (lower i)
               ≡ just (record (view st slots) { mem = ins id (val-native 1ᶠ) (State.mem st) })
  circuit-step = write-agreed true w (view st slots) ((id , val-native 1ᶠ) ∷ []) (inj₂ refl , tt)

  circuit : map (λ after → CircuitState.mem after id) (stepᶜ src w (view st slots) (lower i))
          ≡ just (just (val-native 1ᶠ))
  circuit rewrite circuit-step | inserted-value id (val-native 1ᶠ) (State.mem st) = refl

-- Both steps consume a disabled proof slot.  The circuit retains its raw
-- bytes in proof memory, while preprocessing stores the empty list.
disabled-slot : ∀ src p w st id first (rest : List Byte) tail →
  let i = inner-proof (imm 0ᶠ) id
      before = record st { proof-rem = (first ∷ rest) ∷ tail }
  in (map (λ after → State.proofs after id) (step p src before i) ≡ just (just []))
   × (map (λ after → CircuitState.proofs after id)
       (stepᶜ src w (view before ((first ∷ rest) ∷ tail)) (lower i))
      ≡ just (just (first ∷ rest)))
disabled-slot src p w st id first rest tail
  with 0ᶠ ≟ᶠ 0ᶠ
... | yes _ rewrite inserted-proof id [] (State.proofs st)
                  | inserted-proof id (first ∷ rest) (State.proofs st) = refl , refl
... | no different with () ← different refl
