{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.CircuitInputs (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Circuit ⋯
open import zkir-v4.CircuitBridge ⋯ using (view)
open import zkir-v4.EncodingProperties ⋯ using (EncodingLaws)
open import zkir-v4.InputProperties ⋯
open import zkir-v4.Operations ⋯ using (Mem; ∅; ins)
open import zkir-v4.Semantics ⋯ using (State; ProofPreimage; decode-inputs; init)
open import zkir-v4.Syntax ⋯ using (IrSource; Identifier; TypedIdentifier)
open import zkir-v4.Types ⋯ using (IrValue; typeof; valid-type; _≟T_)

open import Data.Bool using (true; false; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All)
  renaming ([] to []∀; _∷_ to _∷∀_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_)
open import Data.String using () renaming (_≟_ to _≟str_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Relation.Nullary using (yes; no)

-- Agreement retains declaration order from decoding. It also handles a
-- repeated name precisely: each occurrence must see the same circuit
-- witness value.
Matches : CircuitWitness → ∀ {declarations} → DeclaredValues declarations → Set
Matches w []ᵈ = ⊤
Matches w (_∷ᵈ_ {ti = ti} v (_ , _ , rest)) =
  (declared-value w (TypedIdentifier.name ti) ≡ v) × Matches w rest

InitialInputsAgree : IrSource → ProofPreimage → CircuitWitness → Set
InitialInputsAgree src p w =
  Σ (DeclaredValues (IrSource.inputs src)) λ values →
    (declared-raw values ≡ ProofPreimage.inputs p) × Matches w values

private
  assign-value-matches : ∀ w ti v
    → declared-value w (TypedIdentifier.name ti) ≡ v
    → typeof v ≡ TypedIdentifier.val-t ti
    → assign-value (TypedIdentifier.val-t ti) (declared-value w (TypedIdentifier.name ti)) ≡ just v
  assign-value-matches w ti v refl typed with typeof v ≟T TypedIdentifier.val-t ti
  ... | yes _ = refl
  ... | no mismatch = ⊥-elim (mismatch typed)

  declare-matches : ∀ w m {ds} (values : DeclaredValues ds) → Matches w values
    → declare w m ds ≡ just (install-declared m values)
  declare-matches w m []ᵈ tt = refl
  declare-matches w m (_∷ᵈ_ {ti = ti} v (typed , _ , rest)) (matches , rest-match)
    rewrite assign-value-matches w ti v matches typed =
    declare-matches w (ins (TypedIdentifier.name ti) v m) rest rest-match

  forward-decoded : ∀ src p w memory {start}
    → decode-inputs (IrSource.inputs src) (ProofPreimage.inputs p) ≡ just memory
    → declare w ∅ (IrSource.inputs src) ≡ just memory
    → CircuitWitness.binding-input w ≡ ProofPreimage.binding-input p
    → CircuitWitness.comm-commitment w ≡ ProofPreimage.comm-commitment p
    → init src p ≡ just start
    → initᶜ src w ≡ just (view start (CircuitWitness.inner-proofs w))
  forward-decoded src p (mk-witness _ _ _ _ slots) memory decoded declared refl refl ok
    rewrite decoded | declared with IrSource.do-communications-commitment src
                                  | ProofPreimage.comm-commitment p
  ... | false | _ = cong (λ st → just (view st slots)) (just-injective ok)
  ... | true | just (_ , _) = cong (λ st → just (view st slots)) (just-injective ok)
  ... | true | nothing with ok
  ...   | ()

init-forward-decoded : ∀ src p w {start} (values : DeclaredValues (IrSource.inputs src))
  → decode-inputs (IrSource.inputs src) (ProofPreimage.inputs p) ≡ just (State.mem start)
  → install-declared ∅ values ≡ State.mem start
  → Matches w values
  → CircuitWitness.binding-input w ≡ ProofPreimage.binding-input p
  → CircuitWitness.comm-commitment w ≡ ProofPreimage.comm-commitment p
  → init src p ≡ just start
  → initᶜ src w ≡ just (view start (CircuitWitness.inner-proofs w))
init-forward-decoded src p w {start} values decoded installed matches binding commitment initialized =
  forward-decoded src p w (State.mem start) decoded
    (trans (declare-matches w ∅ values matches) (cong just installed)) binding commitment initialized

-- The declared input assignments must agree in declaration order with the
-- preimage. The binding and commitment cells carry the preimage fields.
init-forward : EncodingLaws → ∀ src p w {start}
  → InitialInputsAgree src p w
  → CircuitWitness.binding-input w ≡ ProofPreimage.binding-input p
  → CircuitWitness.comm-commitment w ≡ ProofPreimage.comm-commitment p
  → init src p ≡ just start
  → initᶜ src w ≡ just (view start (CircuitWitness.inner-proofs w))
init-forward laws src p w (values , raw , matched) binding comm ok =
  forward-decoded src p w (install-declared ∅ values)
    (trans (cong (decode-inputs (IrSource.inputs src)) (sym raw))
           (decode-inputs-round laws values))
    (declare-matches w ∅ values matched) binding comm ok

ValidDeclarations : List TypedIdentifier → Set
ValidDeclarations = All (λ ti → valid-type (TypedIdentifier.val-t ti) ≡ true)

private
  declare-values : ∀ w m ds {out} → ValidDeclarations ds
    → declare w m ds ≡ just out
    → Σ (DeclaredValues ds) λ values → (install-declared m values ≡ out) × Matches w values
  declare-values w m [] []∀ eq = []ᵈ , just-injective eq , tt
  declare-values w m (ti ∷ ds) (admissible ∷∀ rest-valid) eq
    with typeof (declared-value w (TypedIdentifier.name ti)) ≟T TypedIdentifier.val-t ti
  ... | no _ with eq
  ...   | ()
  declare-values w m (ti ∷ ds) (admissible ∷∀ rest-valid) eq | yes typed
    with declare-values w (ins (TypedIdentifier.name ti) (declared-value w (TypedIdentifier.name ti)) m)
                        ds rest-valid eq
  ... | rest , out-ok , rest-match =
    (declared-value w (TypedIdentifier.name ti) ∷ᵈ
      (typed , trans (cong valid-type typed) admissible , rest)) , out-ok , refl , rest-match

  insert-keeps-match : ∀ w m id value key
    → declared-value w id ≡ value
    → m key ≡ just (declared-value w key)
    → ins id value m key ≡ just (declared-value w key)
  insert-keeps-match w m id value key value-ok found with key ≟str id
  ... | yes refl = cong just (sym value-ok)
  ... | no _ = found

  freshly-inserted : ∀ m id v → ins id v m id ≡ just v
  freshly-inserted m id v with id ≟str id
  ... | yes _ = refl
  ... | no ne = ⊥-elim (ne refl)

  install-keeps-match : ∀ w m key {ds} (values : DeclaredValues ds)
    → Matches w values
    → m key ≡ just (declared-value w key)
    → install-declared m values key ≡ just (declared-value w key)
  install-keeps-match w m key []ᵈ tt ok = ok
  install-keeps-match w m key (_∷ᵈ_ {ti = ti} v (_ , _ , rest)) (matches , rest-match) ok =
    install-keeps-match w (ins id v m) key rest rest-match
                        (insert-keeps-match w m id v key matches ok)
    where id = TypedIdentifier.name ti

  Stored : Mem → ∀ {ds} → DeclaredValues ds → Set
  Stored m []ᵈ = ⊤
  Stored m (_∷ᵈ_ {ti = ti} v (_ , _ , rest)) =
    (m (TypedIdentifier.name ti) ≡ just v) × Stored m rest

  install-stored : ∀ w m {ds} (values : DeclaredValues ds) → Matches w values
    → Stored (install-declared m values) values
  install-stored w m []ᵈ tt = tt
  install-stored w m (_∷ᵈ_ {ti = ti} v (_ , _ , rest)) (matches , rest-match) =
    trans (install-keeps-match w (ins id v m) id rest rest-match
           (trans (freshly-inserted m id v) (cong just (sym matches))))
          (cong just matches) ,
    install-stored w (ins id v m) rest rest-match
    where id = TypedIdentifier.name ti

  encode-stored : ∀ m {ds} (values : DeclaredValues ds) → Stored m values
    → encode-inputs m ds ≡ declared-raw values
  encode-stored m []ᵈ tt = refl
  encode-stored m (_∷ᵈ_ {ti = ti} v (_ , _ , rest)) (found , rest-found)
    rewrite found | encode-stored m rest rest-found = refl

encode-installed-inputs : ∀ w {ds m} (values : DeclaredValues ds)
  → install-declared ∅ values ≡ m → Matches w values
  → encode-inputs m ds ≡ declared-raw values
encode-installed-inputs w values refl matches =
  encode-stored (install-declared ∅ values) values (install-stored w ∅ values matches)

-- Reads the cells produced by circuit initialization in declaration order.
-- Repeated names still agree with the witness, which gives one value per name.
declare-decode : EncodingLaws → ∀ w ds {memory} → ValidDeclarations ds
  → declare w ∅ ds ≡ just memory
  → decode-inputs ds (encode-inputs memory ds) ≡ just memory
declare-decode laws w ds {memory} valid ok with declare-values w ∅ ds valid ok
... | values , refl , matches
  rewrite encode-installed-inputs w values refl matches =
  decode-inputs-round laws values

-- Reassemble the fields that initialization uses. Replay of the instructions
-- determines the other streams, which initialization keeps without consuming.
replay-inputs : IrSource → CircuitWitness → CircuitState → ProofPreimage → ProofPreimage
replay-inputs src w st p = record p
  { inputs = encode-inputs (CircuitState.mem st) (IrSource.inputs src)
  ; binding-input = CircuitWitness.binding-input w
  ; comm-commitment =
      if IrSource.do-communications-commitment src
      then CircuitWitness.comm-commitment w else nothing
  }

private
  restore-start : ProofPreimage → CircuitState → State
  restore-start p st = record
    { mem = CircuitState.mem st
    ; pis = CircuitState.pis st
    ; acc-pis = []
    ; exposed = []
    ; pi-skips = []
    ; pti-idx = 0
    ; pto-rem = ProofPreimage.pub-transcript-outputs p
    ; priv-rem = ProofPreimage.priv-transcript p
    ; proofs = λ _ → nothing
    ; proof-rem = ProofPreimage.inner-proofs p
    ; inner-witnesses = []
    ; outs = []
    }

init-backward : EncodingLaws → ∀ src w {start} p
  → ValidDeclarations (IrSource.inputs src)
  → initᶜ src w ≡ just start
  → Σ State λ decoded →
      (init src (replay-inputs src w start p) ≡ just decoded) ×
      (view decoded (CircuitWitness.inner-proofs w) ≡ start)
init-backward laws src w {start} p valid ok
  with declare w ∅ (IrSource.inputs src) in declared
     | IrSource.do-communications-commitment src
     | CircuitWitness.comm-commitment w
... | nothing | _ | _ with ok
...   | ()
init-backward laws src w {start} p valid ok | just memory | false | _
  with just-injective ok
... | refl rewrite declare-decode laws w (IrSource.inputs src) valid declared =
  restore-start p start , refl , refl
init-backward laws src w {start} p valid ok | just memory | true | nothing with ok
... | ()
init-backward laws src w {start} p valid ok | just memory | true | just (c , r)
  with just-injective ok
... | refl rewrite declare-decode laws w (IrSource.inputs src) valid declared =
  restore-start p start , refl , refl

private
  init-memory : ∀ src p memory {start}
    → decode-inputs (IrSource.inputs src) (ProofPreimage.inputs p) ≡ just memory
    → init src p ≡ just start
    → State.mem start ≡ memory
  init-memory src p memory decoded ok rewrite decoded
    with IrSource.do-communications-commitment src | ProofPreimage.comm-commitment p
  ... | false | _ = cong State.mem (sym (just-injective ok))
  ... | true | just (_ , _) = cong State.mem (sym (just-injective ok))
  ... | true | nothing with ok
  ...   | ()

-- The aligned witness values re-encode to the original input stream.
-- This uses the initial memory. Commitments read the final memory, whose
-- declarations must agree with the initial ones for an honest run.
initial-inputs-encode : EncodingLaws → ∀ src p w {start}
  → InitialInputsAgree src p w
  → init src p ≡ just start
  → encode-inputs (State.mem start) (IrSource.inputs src) ≡ ProofPreimage.inputs p
initial-inputs-encode laws src p w (values , raw , matches) initialized =
  trans (encode-installed-inputs w values (sym initial-memory) matches) raw
  where
  initial-memory = init-memory src p (install-declared ∅ values)
    (trans (cong (decode-inputs (IrSource.inputs src)) (sym raw))
           (decode-inputs-round laws values))
    initialized
