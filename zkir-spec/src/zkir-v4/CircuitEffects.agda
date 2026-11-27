{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.CircuitEffects (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Syntax ⋯
open import zkir-v4.Types ⋯
open import zkir-v4.Semantics ⋯
open import zkir-v4.Circuit ⋯
open import zkir-v4.CircuitBridge ⋯
open import zkir-v4.Encoding ⋯ using (decode; encode-accumulator)
open import zkir-v4.Validation ⋯ using (resolve-vk)
open import zkir-v4.ProofSlots using (keep)

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; map; length; take; drop)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Nat using (_+_)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Sum using (inj₂)
import Data.Unit
import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

public-result : IrType → State → Identifier → Bool → IrValue → State
public-result t st id true v =
  record (out1 st id v) { pto-rem = drop (encoded-len t) (State.pto-rem st) }
public-result t st id false v = out1 st id v

private-result : IrType → State → Identifier → Bool → IrValue → State
private-result t st id true v =
  record (out1 st id v) { priv-rem = drop (encoded-len t) (State.priv-rem st) }
private-result t st id false v = out1 st id v

ReadValue : Bool → IrType → List Fr → IrValue → Set
ReadValue true  t stream v = decode t (take (encoded-len t) stream) ≡ just v
ReadValue false t _      v = default-val t ≡ v

private
  witness-cell-ok : ∀ src w st t id v
                    → CircuitWitness.assign w id ≡ just v
                    → typeof v ≡ t
                    → stepᶜ src w st (witness-cell t id)
                       ≡ just (record st { mem = ins id v (CircuitState.mem st) })
  witness-cell-ok src w st t id v assigned typed =
    trans (cong (λ lookup → (lookup >>= assign-value t) >>= write-one w st id) assigned)
      (trans (cong (_>>= write-one w st id) (guard-pass (typeof v ≟T t) typed (just v)))
        (write-agreed true w st ((id , v) ∷ []) (inj₂ assigned , Data.Unit.tt)))

public-read-agrees : ∀ p src w st retained g t id active v
                    → eval-guard (State.mem st) g ≡ just active
                    → ReadValue active t (State.pto-rem st) v
                    → CircuitWitness.assign w id ≡ just v
                    → typeof v ≡ t
                    → Agreement p src w st retained (public-input g t id)
                         (public-result t st id active v) retained
public-read-agrees p src w st retained g t id true v guard-ok decoded assigned typed
  rewrite guard-ok | decoded = refl , witness-cell-ok src w (view st retained) t id v assigned typed
public-read-agrees p src w st retained g t id false v guard-ok refl assigned typed
  rewrite guard-ok = refl , witness-cell-ok src w (view st retained) t id v assigned typed

private-read-agrees : ∀ p src w st retained g t id active v
                     → eval-guard (State.mem st) g ≡ just active
                     → ReadValue active t (State.priv-rem st) v
                     → CircuitWitness.assign w id ≡ just v
                     → typeof v ≡ t
                     → Agreement p src w st retained (private-input g t id)
                          (private-result t st id active v) retained
private-read-agrees p src w st retained g t id true v guard-ok decoded assigned typed
  rewrite guard-ok | decoded = refl , witness-cell-ok src w (view st retained) t id v assigned typed
private-read-agrees p src w st retained g t id false v guard-ok refl assigned typed
  rewrite guard-ok = refl , witness-cell-ok src w (view st retained) t id v assigned typed

impact-result : ∀ (st : State) (ops : List Operand) → Bool → List Fr → State
impact-result st ops true vs =
  record st { pis = State.pis st ++ vs
            ; pi-skips = State.pi-skips st ++ (nothing ∷ [])
            ; pti-idx = State.pti-idx st + length ops }
impact-result st ops false _ =
  record st { pis = State.pis st ++ map (λ _ → 0ᶠ) ops
            ; pi-skips = State.pi-skips st ++ (just (length ops) ∷ []) }

ImpactRead : ProofPreimage → State → List Operand → Bool → List Fr → Set
ImpactRead p st ops true vs =
  take (length ops) (drop (State.pti-idx st) (ProofPreimage.pub-transcript-inputs p)) ≡ vs
ImpactRead _ _ _ false _ = Data.Unit.⊤

impact-agrees : ∀ p src w st retained g ops active vs
                 → resolve𝔹 (State.mem st) g ≡ just active
                 → resolve-all-Fr (State.mem st) ops ≡ just vs
                 → ImpactRead p st ops active vs
                 → Agreement p src w st retained (impact g ops)
                      (impact-result st ops active vs) retained
impact-agrees p src w st retained g ops true vs guard-ok vals-ok transcript-ok
  rewrite guard-ok | vals-ok =
  guard-pass
    (take (length ops) (drop (State.pti-idx st) (ProofPreimage.pub-transcript-inputs p)) ≟LFr vs)
    transcript-ok (just (impact-result st ops true vs)) , refl
impact-agrees p src w st retained g ops false vs guard-ok vals-ok _
  rewrite guard-ok | vals-ok = refl , refl

bind-result : State → Identifier → List Byte → List (List Byte) → State
bind-result st id blob for-later =
  record st { proofs = insert-proof id blob (State.proofs st)
            ; proof-rem = for-later
            ; inner-witnesses = State.inner-witnesses st ++ (blob ∷ []) }

proof-slot-agrees : ∀ p src w st g id remaining raw for-later active
                    → State.proof-rem st ≡ raw ∷ for-later
                    → resolve𝔹 (State.mem st) g ≡ just active
                    → Agreement p src w st (keep active raw ∷ remaining) (inner-proof g id)
                         (bind-result st id (keep active raw) for-later) remaining
proof-slot-agrees p src w st g id remaining raw for-later active slots bit
  rewrite slots | bit = refl , refl

-- Only the primitive verifier gadget is imported.  The statements
-- quantify over correctly parsed fixed keys; no pairing validity is
-- needed until the outer protocol checks the deferred accumulators.
record PreparationLaws : Set where
  field
    active-prepares : ∀ key vs blob → key-well-formed key ≡ true
                    → prepare-compatible key vs blob true ≡ true
                    → prepare-circuit key vs blob true ≡ prepare-active key vs blob
    inactive-prepares : ∀ key vs blob → key-well-formed key ≡ true
                      → prepare-compatible key vs blob false ≡ true
                      → prepare-circuit key vs blob false ≡ just trivial-accumulator

    -- Successful circuit preparations establish the corresponding native
    -- result.  This direction makes no assertion that malformed data work.
    prepared-result : ∀ key vs blob active acc → key-well-formed key ≡ true
                    → prepare-circuit key vs blob active ≡ just acc
                    → (if active then prepare-active key vs blob else just trivial-accumulator) ≡ just acc

PreparationResult : Bool → List Byte → List Fr → List Byte → Accumulator → Set
PreparationResult true key vs blob acc = prepare-active key vs blob ≡ just acc
PreparationResult false _ _ _ acc = trivial-accumulator ≡ acc

Preparation : Bool → List Byte → List Fr → List Byte → Accumulator → Set
Preparation active key vs blob acc =
  prepare-compatible key vs blob active ≡ true × PreparationResult active key vs blob acc

PreparationForward : Set
PreparationForward =
  ∀ key values proof active acc → key-well-formed key ≡ true
  → Preparation active key values proof acc
  → prepare-circuit key values proof active ≡ just acc

preparation-forward : PreparationLaws → PreparationForward
preparation-forward laws key values proof true acc parsed (compatible , prepared) =
  trans (PreparationLaws.active-prepares laws key values proof parsed compatible) prepared
preparation-forward laws key values proof false .(trivial-accumulator) parsed (compatible , refl) =
  PreparationLaws.inactive-prepares laws key values proof parsed compatible

PreparationBackward : Set
PreparationBackward =
  ∀ key values proof active acc → key-well-formed key ≡ true
  → prepare-circuit key values proof active ≡ just acc
  → (if active then prepare-active key values proof else just trivial-accumulator) ≡ just acc

preparation-backward : PreparationLaws → PreparationBackward
preparation-backward = PreparationLaws.prepared-result

prepare-agrees-using : ∀ (laws : PreparationForward) p src w st retained g hash ops proof out
                   active vs blob key acc
                 → resolve𝔹 (State.mem st) g ≡ just active
                 → resolve-all-Fr (State.mem st) ops ≡ just vs
                 → State.proofs st proof ≡ just blob
                 → resolve-vk hash (IrSource.inner-vks src) ≡ just key
                 → key-well-formed key ≡ true
                 → Preparation active key vs blob acc
                 → Agrees w out (val-accumulator acc)
                 → Agreement p src w st retained (prepare-verification g hash ops proof out)
                      (out1 st out (val-accumulator acc)) retained
prepare-agrees-using laws p src w st retained g hash ops proof out true vs blob key acc
  bit vals slot key-found parsed (compatible , prepared) agrees =
  off , on
  where
  off : step p src st (prepare-verification g hash ops proof out)
        ≡ just (out1 st out (val-accumulator acc))
  off rewrite bit | vals | slot | key-found | parsed | prepared = refl
  on : stepᶜ src w (view st retained) (prepare-proof g hash ops proof out)
       ≡ just (view (out1 st out (val-accumulator acc)) retained)
  on = prepare-forward src w (view st retained) g hash ops proof out true vs blob key acc
         bit vals slot key-found parsed (laws key vs blob true acc parsed (compatible , prepared))
         agrees
prepare-agrees-using laws p src w st retained g hash ops proof out false vs blob key .(trivial-accumulator)
  bit vals slot key-found parsed (compatible , refl) agrees =
  off , on
  where
  off : step p src st (prepare-verification g hash ops proof out)
        ≡ just (out1 st out (val-accumulator trivial-accumulator))
  off rewrite bit | vals | slot | key-found = refl
  on : stepᶜ src w (view st retained) (prepare-proof g hash ops proof out)
       ≡ just (view (out1 st out (val-accumulator trivial-accumulator)) retained)
  on = prepare-forward src w (view st retained) g hash ops proof out false vs blob key trivial-accumulator
         bit vals slot key-found parsed (laws key vs blob false trivial-accumulator parsed (compatible , refl)) agrees

prepare-agrees : ∀ (laws : PreparationLaws) p src w st retained g hash ops proof out
                   active vs blob key acc
                 → resolve𝔹 (State.mem st) g ≡ just active
                 → resolve-all-Fr (State.mem st) ops ≡ just vs
                 → State.proofs st proof ≡ just blob
                 → resolve-vk hash (IrSource.inner-vks src) ≡ just key
                 → key-well-formed key ≡ true
                 → Preparation active key vs blob acc
                 → Agrees w out (val-accumulator acc)
                 → Agreement p src w st retained (prepare-verification g hash ops proof out)
                      (out1 st out (val-accumulator acc)) retained
prepare-agrees laws = prepare-agrees-using (preparation-forward laws)

fold-agrees : ∀ p src w st retained ops out a b rest acc
              → resolve-accs (State.mem st) ops ≡ just (a ∷ b ∷ rest)
              → fold-accumulators (a ∷ b ∷ rest) ≡ just acc
              → Agrees w out (val-accumulator acc)
              → Agreement p src w st retained (accumulate ops out)
                   (out1 st out (val-accumulator acc)) retained
fold-agrees p src w st retained ops out a b rest acc vals folded agrees =
  off , fold-forward src w (view st retained) ops out a b rest acc vals folded agrees
  where
  off : step p src st (accumulate ops out) ≡ just (out1 st out (val-accumulator acc))
  off rewrite vals | folded = refl

collect-agrees : ∀ m ts ops → collectOutputs m ts ops ≡ collect-outputs m ts ops
collect-agrees m [] [] = refl
collect-agrees m [] (_ ∷ _) = refl
collect-agrees m (_ ∷ _) [] = refl
collect-agrees m (t ∷ ts) (op ∷ ops) with resolve m op
... | nothing = refl
... | just v with typeof v ≟T t
...   | Relation.Nullary.no _ = refl
...   | Relation.Nullary.yes _ rewrite collect-agrees m ts ops = refl

output-agrees : ∀ p src w st retained ops values
               → collectOutputs (State.mem st) (IrSource.outputs src) ops ≡ just values
               → Agreement p src w st retained (circuit-output ops)
                    (record st { outs = State.outs st ++ values }) retained
output-agrees p src w st retained ops values collected = off , on
  where
  off : step p src st (circuit-output ops)
        ≡ just (record st { outs = State.outs st ++ values })
  off rewrite collected = refl
  on : stepᶜ src w (view st retained) (record-output ops)
       ≡ just (view (record st { outs = State.outs st ++ values }) retained)
  on rewrite sym (collect-agrees (State.mem st) (IrSource.outputs src) ops) | collected = refl

exposure-result : State → Accumulator → State
exposure-result st acc =
  record st { acc-pis = State.acc-pis st ++ encode-accumulator acc
            ; exposed = State.exposed st ++ (acc ∷ []) }

expose-agrees : ∀ p src w st retained op acc
                → resolve-acc (State.mem st) op ≡ just acc
                → Agreement p src w st retained (verify-accumulator op)
                     (exposure-result st acc) retained
expose-agrees p src w st retained op acc ok rewrite ok = refl , refl
