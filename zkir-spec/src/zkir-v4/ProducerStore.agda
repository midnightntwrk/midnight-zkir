{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.ProducerStore (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Types ⋯
open import zkir-v4.Syntax ⋯
open import zkir-v4.Producer ⋯
import zkir-v4.Validation
open import zkir-v4.Operations ⋯ using (Mem; ∅; ins; resolve; apply-writes)
open import zkir-v4.Semantics ⋯ using (State; ProofPreimage; init; decode-inputs)
open import zkir-v4.InputProperties ⋯
open import Data.Bool using (true; false)
open import Data.Bool.ListAction using (all)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All)
  renaming ([] to []∀; _∷_ to _∷∀_)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; ∃; proj₁; proj₂)
import Data.String.Properties as Strings
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (yes; no)

bind-success : ∀ {A B : Set} (a : Maybe A) (f : A → Maybe B) {b}
  → (a >>= f) ≡ just b → ∃ λ x → (a ≡ just x) × (f x ≡ just b)
bind-success nothing _ ()
bind-success (just x) _ ok = x , refl , ok

demand-success : ∀ {b} → demand b ≡ just tt → b ≡ true
demand-success {true} _ = refl
demand-success {false} ()

fresh-success : ∀ Γ id t {Γ′} → fresh Γ (id ⦂ t) ≡ just Γ′
  → (Γ′ ≡ (id ⦂ t) ∷ Γ) × (type-of Γ id ≡ nothing) × (valid-type t ≡ true)
fresh-success Γ id t ok with type-of Γ id in found
... | just _ with () ← ok
fresh-success Γ id t ok | nothing with valid-type t
... | false with () ← ok
... | true = sym (just-injective ok) , refl , refl

fold-cons : ∀ {A B : Set} (f : B → A → Maybe B) b a as {out}
  → fold-check f b (a ∷ as) ≡ just out
  → ∃ λ b′ → (f b a ≡ just b′) × (fold-check f b′ as ≡ just out)
fold-cons f b a as = bind-success (f b a) (λ b′ → fold-check f b′ as)

infer-success : ∀ s → Producer s →
  ∃ λ Γ → ∃ λ final → (fold-check fresh [] (IrSource.inputs s) ≡ just Γ) ×
    (fold-check (producer-step (IrSource.outputs s)) Γ (IrSource.instructions s) ≡ just final)
infer-success s producer with zkir-v4.Validation.validate ⋯ s
... | false with () ← producer
infer-success s producer | true with infer s in inferred
... | nothing with () ← producer
... | just final
  with bind-success (demand (all valid-type (IrSource.outputs s))) _ inferred
... | tt , _ , checked
  with bind-success (fold-check fresh [] (IrSource.inputs s)) _ checked
... | Γ , ins-ok , code-ok = Γ , final , ins-ok , code-ok

StoreTyped : Env → Mem → Set
StoreTyped Γ m = ∀ id t → type-of Γ id ≡ just t →
  ∃ λ v → (m id ≡ just v) × (typeof v ≡ t)

typed-operand : ∀ {signature Γ m op t} → StoreTyped Γ m → ty signature Γ op ≡ just t →
  ∃ λ v → (resolve m op ≡ just v) × (typeof v ≡ t)
typed-operand {op = imm x} _ found = val-native x , refl , just-injective found
typed-operand {op = var id} typed found = typed id _ found

Extends : Env → Mem → Mem → Set
Extends Γ before after = ∀ id t → type-of Γ id ≡ just t → after id ≡ before id

writes-types : List (Identifier × IrValue) → Env
writes-types = map λ (id , v) → id ⦂ typeof v

type-inserted : ∀ Γ id t → type-of ((id ⦂ t) ∷ Γ) id ≡ just t
type-inserted Γ id t with id Strings.≟ id
... | yes _ = refl
... | no ne = ⊥-elim (ne refl)

lookup-inserted : ∀ m id v → ins id v m id ≡ just v
lookup-inserted m id v with id Strings.≟ id
... | yes _ = refl
... | no ne = ⊥-elim (ne refl)

type-preserved : ∀ Γ out u id t
  → type-of Γ out ≡ nothing → type-of Γ id ≡ just t
  → type-of ((out ⦂ u) ∷ Γ) id ≡ just t
type-preserved Γ out u id t fresh-id found with out Strings.≟ id
... | yes refl rewrite fresh-id with () ← found
... | no _ = found

lookup-preserved : ∀ Γ m out v → type-of Γ out ≡ nothing
  → Extends Γ m (ins out v m)
lookup-preserved Γ m out v fresh-id id t found with id Strings.≟ out
... | yes refl rewrite fresh-id with () ← found
... | no _ = refl

insert-typed : ∀ {Γ m id t v} → StoreTyped Γ m → typeof v ≡ t →
  StoreTyped ((id ⦂ t) ∷ Γ) (ins id v m)
insert-typed {Γ} {m} {out} {t} {v} typed vt id u found with id Strings.≟ out | out Strings.≟ id
... | yes refl | yes _ = v , refl , trans vt (just-injective found)
... | yes refl | no ne = ⊥-elim (ne refl)
... | no ne | yes refl = ⊥-elim (ne refl)
... | no _ | no _ = typed id u found

record WriteFrame (Γ Γ′ : Env) (m m′ : Mem) (ws : List (Identifier × IrValue)) : Set where
  field
    typed-after : StoreTyped Γ′ m′
    extends : Extends Γ m m′
    keeps-types : ∀ id t → type-of Γ id ≡ just t → type-of Γ′ id ≡ just t
    written : All (λ { (id , v) → (m′ id ≡ just v) × (type-of Γ′ id ≡ just (typeof v)) }) ws

write-frame : ∀ Γ m ws {Γ′} → StoreTyped Γ m
  → fold-check fresh Γ (writes-types ws) ≡ just Γ′
  → WriteFrame Γ Γ′ m (apply-writes m ws) ws
write-frame Γ m [] typed refl = record
  { typed-after = typed
  ; extends = λ _ _ _ → refl
  ; keeps-types = λ _ _ found → found
  ; written = []∀
  }
write-frame Γ m ((id , v) ∷ ws) typed checked
  with fold-cons fresh Γ (id ⦂ typeof v) (writes-types ws) checked
... | env , added , tail with fresh-success Γ id (typeof v) added
...   | refl , new , _ with write-frame ((id ⦂ typeof v) ∷ Γ) (ins id v m) ws (insert-typed typed refl) tail
...     | F = record
  { typed-after = WriteFrame.typed-after F
  ; extends = λ k t found →
      trans (WriteFrame.extends F k t (type-preserved Γ id (typeof v) k t new found))
            (lookup-preserved Γ m id v new k t found)
  ; keeps-types = λ k t found →
      WriteFrame.keeps-types F k t (type-preserved Γ id (typeof v) k t new found)
  ; written =
      (trans (WriteFrame.extends F id (typeof v) self-type) (lookup-inserted m id v) ,
        WriteFrame.keeps-types F id (typeof v) self-type) ∷∀ WriteFrame.written F
  }
  where
  self-type : type-of ((id ⦂ typeof v) ∷ Γ) id ≡ just (typeof v)
  self-type = type-inserted Γ id (typeof v)

declared-writes : ∀ {ds} → DeclaredValues ds → List (Identifier × IrValue)
declared-writes []ᵈ = []
declared-writes (_∷ᵈ_ {ti = ti} v (_ , _ , rest)) =
  (TypedIdentifier.name ti , v) ∷ declared-writes rest

declared-types : ∀ {ds} (values : DeclaredValues ds) → writes-types (declared-writes values) ≡ ds
declared-types []ᵈ = refl
declared-types (_∷ᵈ_ {ti = id ⦂ t} v (typed , _ , rest)) rewrite typed | declared-types rest = refl

declared-mem : ∀ m {ds} (values : DeclaredValues ds)
  → apply-writes m (declared-writes values) ≡ install-declared m values
declared-mem m []ᵈ = refl
declared-mem m (_∷ᵈ_ {ti = ti} v (_ , _ , rest)) = declared-mem (ins (TypedIdentifier.name ti) v m) rest

init-decodes : ∀ s p {st} → init s p ≡ just st
  → decode-inputs (IrSource.inputs s) (ProofPreimage.inputs p) ≡ just (State.mem st)
init-decodes s p ok with decode-inputs (IrSource.inputs s) (ProofPreimage.inputs p) in decoded
... | nothing with () ← ok
init-decodes s p ok | just m with IrSource.do-communications-commitment s | ProofPreimage.comm-commitment p
... | false | _ = cong (λ st′ → just (State.mem st′)) (just-injective ok)
... | true | nothing with () ← ok
... | true | just (_ , _) = cong (λ st′ → just (State.mem st′)) (just-injective ok)

record InitialStore (s : IrSource) (p : ProofPreimage) (Γ : Env) (m : Mem) : Set where
  field
    values : DeclaredValues (IrSource.inputs s)
    raw : declared-raw values ≡ ProofPreimage.inputs p
    installed : install-declared ∅ values ≡ m
    frame : WriteFrame [] Γ ∅ m (declared-writes values)

initial-store : ∀ s p {st Γ} → init s p ≡ just st
  → fold-check fresh [] (IrSource.inputs s) ≡ just Γ → InitialStore s p Γ (State.mem st)
initial-store s p {st} {Γ} initialized checked with decode-inputs-sound _ _ (init-decodes s p initialized)
... | vs , raw , installed = record
  { values = vs
  ; raw = raw
  ; installed = installed
  ; frame = subst (λ m → WriteFrame [] Γ ∅ m (declared-writes vs))
      (trans (declared-mem ∅ vs) installed)
      (write-frame [] ∅ (declared-writes vs) (λ _ _ ())
        (trans (cong (fold-check fresh []) (declared-types vs)) checked))
  }
