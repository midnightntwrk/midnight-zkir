{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.CommitmentInputs (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Types ⋯ using (IrValue; val-accumulator)
open import zkir-v4.Syntax ⋯ using (IrSource; Identifier; TypedIdentifier)
open import zkir-v4.Semantics ⋯
open import zkir-v4.Circuit ⋯ using (CircuitWitness; declared-value; encode-inputs)
open import zkir-v4.CircuitInputs ⋯ using (InitialInputsAgree; Matches; initial-inputs-encode)
open import zkir-v4.CircuitProof ⋯ using (honest-witness)
open import zkir-v4.EncodingProperties ⋯ using (EncodingLaws)
open import zkir-v4.InputProperties ⋯
open import zkir-v4.RunShape ⋯

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All)
  renaming ([] to []∀; _∷_ to _∷∀_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; ∃)
open import Data.String using () renaming (_≟_ to _≟str_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import Relation.Nullary using (yes; no)

-- The communications gadget encodes the declared names from the terminal
-- memory.  Frame evidence refers to those cells alone.
InputFrame : List TypedIdentifier → Mem → Mem → Set
InputFrame ds start final = All (λ ti → final (TypedIdentifier.name ti) ≡
                                        start (TypedIdentifier.name ti)) ds

encode-inputs-frame : ∀ ds start final → InputFrame ds start final
                    → encode-inputs final ds ≡ encode-inputs start ds
encode-inputs-frame [] start final []∀ = refl
encode-inputs-frame (ti ∷ ds) start final (head ∷∀ tail)
  rewrite head with start (TypedIdentifier.name ti)
... | nothing = encode-inputs-frame ds start final tail
... | just _ rewrite encode-inputs-frame ds start final tail = refl

terminal-inputs-encode : EncodingLaws → ∀ src p w start final
                        → InitialInputsAgree src p w
                        → init src p ≡ just start
                        → InputFrame (IrSource.inputs src) (State.mem start) (State.mem final)
                        → encode-inputs (State.mem final) (IrSource.inputs src) ≡ ProofPreimage.inputs p
terminal-inputs-encode laws src p w start final matched initialized frames =
  trans (encode-inputs-frame (IrSource.inputs src) (State.mem start) (State.mem final) frames)
        (initial-inputs-encode laws src p w matched initialized)

-- Execution can overwrite cells but never removes their names.
Defined : Mem → Identifier → Set
Defined m id = ∃ λ v → m id ≡ just v

PreservesNames : Mem → Mem → Set
PreservesNames start final = ∀ id → Defined start id → Defined final id

private
  insert-defines : ∀ id v m → Defined (ins id v m) id
  insert-defines id v m with id ≟str id
  ... | yes _ = v , refl
  ... | no bad with () ← bad refl

  insert-preserves : ∀ out v m → PreservesNames m (ins out v m)
  insert-preserves out v m id found with id ≟str out
  ... | yes _ = v , refl
  ... | no _ = found

  writes-preserve : ∀ m ws → PreservesNames m (apply-writes m ws)
  writes-preserve m [] id found = found
  writes-preserve m ((out , v) ∷ ws) id found =
    writes-preserve (ins out v m) ws id (insert-preserves out v m id found)

  declared-preserve : ∀ m {ds} (vs : DeclaredValues ds)
                      → PreservesNames m (install-declared m vs)
  declared-preserve m []ᵈ id found = found
  declared-preserve m (_∷ᵈ_ {ti = ti} v (_ , _ , vs)) id found =
    declared-preserve (ins out v m) vs id (insert-preserves out v m id found)
    where out = TypedIdentifier.name ti

  declared-defined : ∀ m {ds} (vs : DeclaredValues ds)
                   → All (λ ti → Defined (install-declared m vs) (TypedIdentifier.name ti)) ds
  declared-defined m []ᵈ = []∀
  declared-defined m (_∷ᵈ_ {ti = ti} v (_ , _ , vs)) =
    declared-preserve (ins out v m) vs out (insert-defines out v m)
    ∷∀ declared-defined (ins out v m) vs
    where out = TypedIdentifier.name ti

  decoded-present : ∀ ds raw m → decode-inputs ds raw ≡ just m
                    → All (λ ti → Defined m (TypedIdentifier.name ti)) ds
  decoded-present ds raw m eq with decode-inputs-sound ds raw eq
  ... | vs , _ , installed =
    subst (λ memory → All (λ ti → Defined memory (TypedIdentifier.name ti)) ds)
      installed (declared-defined ∅ vs)

  initial-present : ∀ src p st → init src p ≡ just st
                    → All (λ ti → Defined (State.mem st) (TypedIdentifier.name ti)) (IrSource.inputs src)
  initial-present src p st ok with decode-inputs (IrSource.inputs src) (ProofPreimage.inputs p) in decoded
  ... | nothing with () ← ok
  initial-present src p st ok | just m with IrSource.do-communications-commitment src
  ... | false with refl ← just-injective ok = decoded-present _ _ m decoded
  initial-present src p st ok | just m | true with ProofPreimage.comm-commitment p
  ... | nothing with () ← ok
  initial-present src p st ok | just m | true | just (_ , _)
    with refl ← just-injective ok = decoded-present _ _ m decoded

  step-preserves : ∀ {p src w st retained i after rest}
                   → ReadyStep p src w st retained i after rest
                   → PreservesNames (State.mem st) (State.mem after)
  step-preserves {st = st} (common {writes = ws} _ _ _) = writes-preserve (State.mem st) ws
  step-preserves {st = st} (bit-constraint {writes = ws} _ _ _) = writes-preserve (State.mem st) ws
  step-preserves {st = st} (division {writes = ws} _ _ _) = writes-preserve (State.mem st) ws
  step-preserves {st = st} (reconstitution {writes = ws} _ _ _) = writes-preserve (State.mem st) ws
  step-preserves {st = st} (special {writes = ws} _ _ _) = writes-preserve (State.mem st) ws
  step-preserves {st = st} (public-read {id = id} {active = false} {v = v} _ _ _ _) =
    insert-preserves id v (State.mem st)
  step-preserves {st = st} (public-read {id = id} {active = true} {v = v} _ _ _ _) =
    insert-preserves id v (State.mem st)
  step-preserves {st = st} (private-read {id = id} {active = false} {v = v} _ _ _ _) =
    insert-preserves id v (State.mem st)
  step-preserves {st = st} (private-read {id = id} {active = true} {v = v} _ _ _ _) =
    insert-preserves id v (State.mem st)
  step-preserves (impact-step {active = false} _ _ _) _ found = found
  step-preserves (impact-step {active = true} _ _ _) _ found = found
  step-preserves (proof-slot _ _) _ found = found
  step-preserves {st = st} (prepare-step {out = out} {acc = acc} _ _ _ _ _ _ _) =
    insert-preserves out (val-accumulator acc) (State.mem st)
  step-preserves {st = st} (fold-step {out = out} {acc = acc} _ _ _) =
    insert-preserves out (val-accumulator acc) (State.mem st)
  step-preserves (expose-step _) _ found = found
  step-preserves (output-step _) _ found = found

ready-preserves-names : ∀ {p src w st retained is final rest}
                        → ReadyRun p src w st retained is final rest
                        → PreservesNames (State.mem st) (State.mem final)
ready-preserves-names empty _ found = found
ready-preserves-names (instr head tail) id found =
  ready-preserves-names tail id (step-preserves head id found)

private
  all-preserved : ∀ ds {m m′} → PreservesNames m m′
                → All (λ ti → Defined m (TypedIdentifier.name ti)) ds
                → All (λ ti → Defined m′ (TypedIdentifier.name ti)) ds
  all-preserved [] _ []∀ = []∀
  all-preserved (ti ∷ ds) keeps (found ∷∀ rest) =
    keeps (TypedIdentifier.name ti) found ∷∀ all-preserved ds keeps rest

  encoded-matches : ∀ p final {ds} (vs : DeclaredValues ds)
                    → Matches (honest-witness p final) vs
                    → All (λ ti → Defined (State.mem final) (TypedIdentifier.name ti)) ds
                    → encode-inputs (State.mem final) ds ≡ declared-raw vs
  encoded-matches p final []ᵈ tt []∀ = refl
  encoded-matches p final (_∷ᵈ_ {ti = ti} v (_ , _ , vs)) (found , rest) ((stored , eq) ∷∀ present)
    rewrite eq | found | encoded-matches p final vs rest present = refl

-- For the honest witness, the initial matching property refers directly
-- to terminal memory.  A successful run keeps the declared names present,
-- so the default for a missing witness cell is never used at that name.
honest-terminal-inputs : ∀ src p start final retained rest
                       → InitialInputsAgree src p (honest-witness p final)
                       → init src p ≡ just start
                       → ReadyRun p src (honest-witness p final) start retained
                                  (IrSource.instructions src) final rest
                       → encode-inputs (State.mem final) (IrSource.inputs src) ≡ ProofPreimage.inputs p
honest-terminal-inputs src p start final retained rest (vs , raw , matches) initialized ready =
  trans (encoded-matches p final vs matches
    (all-preserved (IrSource.inputs src) (ready-preserves-names ready)
      (initial-present src p start initialized))) raw
