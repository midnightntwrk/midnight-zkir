{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.ForwardShape (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Syntax ⋯
open import zkir-v4.Types ⋯
open import zkir-v4.Semantics ⋯ hiding (write)
open import zkir-v4.SemanticsProperties ⋯ using (Trace; done; next; AcceptedRun; preprocess-inversion)
open import zkir-v4.Circuit ⋯
open import zkir-v4.CircuitBridge ⋯ using (Agrees; WriteAgreement)
open import zkir-v4.CircuitProof ⋯ using (Common; apply; core-step)
open import zkir-v4.CircuitPure ⋯
open import zkir-v4.CircuitEffects ⋯
open import zkir-v4.RunShape ⋯
open import zkir-v4.Encoding ⋯ using (decode)
open import zkir-v4.Validation ⋯ using (resolve-vk)
open import zkir-v4.ProofSlots using (keep)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; length; take; drop)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (_≤_)
open import Data.Product using (_×_; _,_; ∃; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import Relation.Nullary using (yes; no)

-- A producer writing a single-assignment witness must agree with new
-- computed cells wherever it supplies them.  Its transcript cells must
-- contain the decoded or default value.  These local conditions never
-- ask for a successful circuit step, a computed result, or a guard value.
Aligns : CircuitWitness → State → Instruction → Bool → Set
Aligns w st i checked = ∀ ws → compute (State.mem st) i ≡ just ws → WriteAgreement checked w ws

-- Only the branch selected by the actual guard needs a transcript cell.
GuardedCell : CircuitWitness → State → Maybe Operand → Identifier → IrType → List Fr → Set
GuardedCell w st g id t raw = ∀ active v → eval-guard (State.mem st) g ≡ just active
  → ReadValue active t raw v → CircuitWitness.assign w id ≡ just v × typeof v ≡ t

data Supported (s : IrSource) (w : CircuitWitness) (st : State) : Instruction → Set where
  shared-ok : ∀ {i} → Common i → Aligns w st i (check-shared-writes i) → Supported s w st i
  special-ok : ∀ {i} → Special (State.mem st) i → Aligns w st i (special-checked i) → Supported s w st i
  bit-constraint-ok : ∀ {x n} → n ≤ FR-BITS → Aligns w st (constrain-bits x n) true
                    → Supported s w st (constrain-bits x n)
  division-ok : ∀ {x n os} → n ≤ FR-BITS → Aligns w st (div-mod-power-of-two x n os) true
              → Supported s w st (div-mod-power-of-two x n os)
  recon-ok : ∀ {d m n o} → n ≤ FR-BITS → Aligns w st (reconstitute-field d m n o) true
           → Supported s w st (reconstitute-field d m n o)
  public-ok : ∀ {g t id} → GuardedCell w st g id t (State.pto-rem st) → Supported s w st (public-input g t id)
  private-ok : ∀ {g t id} → GuardedCell w st g id t (State.priv-rem st) → Supported s w st (private-input g t id)
  impact-ok : ∀ {g ops} → (resolve𝔹 (State.mem st) g ≡ just false →
                            ∃ λ vs → resolve-all-Fr (State.mem st) ops ≡ just vs)
            → Supported s w st (impact g ops)
  slot-ok : ∀ {g id} → Supported s w st (inner-proof g id)
  prepare-ok : ∀ {g h ops id out}
             → (∀ key → resolve-vk h (IrSource.inner-vks s) ≡ just key → key-well-formed key ≡ true)
             → (∀ flag vs blob key → resolve𝔹 (State.mem st) g ≡ just flag
                 → resolve-all-Fr (State.mem st) ops ≡ just vs → State.proofs st id ≡ just blob
                 → resolve-vk h (IrSource.inner-vks s) ≡ just key → prepare-compatible key vs blob flag ≡ true)
             → (∀ acc → prepare-result s st g h ops id ≡ just acc → Agrees w out (val-accumulator acc))
             → Supported s w st (prepare-verification g h ops id out)
  fold-ok : ∀ {ops out} → (∀ acc → fold-result (State.mem st) ops ≡ just acc → Agrees w out (val-accumulator acc))
          → Supported s w st (accumulate ops out)
  expose-ok : ∀ {op} → Supported s w st (verify-accumulator op)
  output-ok : ∀ {ops} → Supported s w st (circuit-output ops)

private
  -- The first-list result is the prefix added to the normalized proof stream.
  Local : ∀ p s w st i after → Set
  Local p s w st i after = ∃ λ prefix →
    (State.inner-witnesses after ≡ State.inner-witnesses st ++ prefix) ×
    (∀ tail → ReadyStep p s w st (prefix ++ tail) i after tail)

  same : ∀ st → State.inner-witnesses st ≡ State.inner-witnesses st ++ []
  same st = sym (++-identityʳ (State.inner-witnesses st))

  pure : ∀ p s w st i after
       → (∀ {ws tail} → compute (State.mem st) i ≡ just ws → ReadyStep p s w st tail i (apply st ws) tail)
       → (compute (State.mem st) i >>= λ ws → just (apply st ws)) ≡ just after
       → Local p s w st i after
  pure p s w st i after mk ok with compute (State.mem st) i in calc
  ... | nothing with () ← ok
  ... | just ws with refl ← just-injective ok = [] , same st , λ tail → mk refl

  unbind : ∀ {A B : Set} (x : Maybe A) (f : A → Maybe B) {y}
         → (x >>= f) ≡ just y → ∃ λ v → x ≡ just v × f v ≡ just y
  unbind nothing _ ()
  unbind (just v) _ ok = v , refl , ok

  prep-result : ∀ flag key vs blob acc
              → (if flag then (if key-well-formed key then prepare-active key vs blob else nothing)
                 else just trivial-accumulator) ≡ just acc → PreparationResult flag key vs blob acc
  prep-result false key vs blob acc = just-injective
  prep-result true key vs blob acc ok with key-well-formed key
  ... | false with () ← ok
  ... | true = ok

  invert : ∀ p s w st i after → Supported s w st i → step p s st i ≡ just after → Local p s w st i after
  invert p s w st i after (shared-ok c align) ok rewrite core-step p s st i c =
    pure p s w st i after (λ calc → common c calc (align _ calc)) ok
  invert p s w st i after (special-ok cond align) ok rewrite special-off p s st i cond =
    pure p s w st i after (λ calc → special cond calc (align _ calc)) ok
  invert p s w st i after (bit-constraint-ok bound align) ok =
    pure p s w st i after (λ calc → bit-constraint bound calc (align _ calc)) ok
  invert p s w st i after (division-ok bound align) ok =
    pure p s w st i after (λ calc → division bound calc (align _ calc)) ok
  invert p s w st i after (recon-ok bound align) ok =
    pure p s w st i after (λ calc → reconstitution bound calc (align _ calc)) ok
  invert p s w st (public-input g t id) after (public-ok cell) ok with eval-guard (State.mem st) g in bit
  ... | nothing with () ← ok
  ... | just false with refl ← just-injective ok =
    [] , same st , λ tail → public-read bit refl (proj₁ (cell false _ refl refl)) (proj₂ (cell false _ refl refl))
  ... | just true with decode t (take (encoded-len t) (State.pto-rem st)) in dec
  ...   | nothing with () ← ok
  ...   | just v with refl ← just-injective ok =
    [] , same st , λ tail → public-read bit dec (proj₁ (cell true v refl dec)) (proj₂ (cell true v refl dec))
  invert p s w st (private-input g t id) after (private-ok cell) ok with eval-guard (State.mem st) g in bit
  ... | nothing with () ← ok
  ... | just false with refl ← just-injective ok =
    [] , same st , λ tail → private-read bit refl (proj₁ (cell false _ refl refl)) (proj₂ (cell false _ refl refl))
  ... | just true with decode t (take (encoded-len t) (State.priv-rem st)) in dec
  ...   | nothing with () ← ok
  ...   | just v with refl ← just-injective ok =
    [] , same st , λ tail → private-read bit dec (proj₁ (cell true v refl dec)) (proj₂ (cell true v refl dec))
  invert p s w st (impact g ops) after (impact-ok inactive) ok with resolve𝔹 (State.mem st) g in bit
  ... | nothing with () ← ok
  ... | just false with refl ← just-injective ok | vs , resolved ← inactive refl =
    [] , same st , λ tail → impact-step bit resolved tt
  ... | just true with resolve-all-Fr (State.mem st) ops in resolved
  ...   | nothing with () ← ok
  ...   | just vs with take (length ops) (drop (State.pti-idx st) (ProofPreimage.pub-transcript-inputs p)) ≟LFr vs
  ...     | no _ with () ← ok
  ...     | yes received with refl ← just-injective ok =
    [] , same st , λ tail → impact-step bit resolved received
  invert p s w st (inner-proof g id) after slot-ok ok with State.proof-rem st in slots
  ... | [] with () ← ok
  ... | raw ∷ rest with resolve𝔹 (State.mem st) g in bit
  ...   | nothing with () ← ok
  ...   | just active with refl ← just-injective ok =
    (keep active raw ∷ []) , refl , λ tail → proof-slot slots bit
  invert p s w st (prepare-verification g h ops id out) after (prepare-ok parsed compatible align) ok
    with unbind (prepare-result s st g h ops id) _ ok
  ... | acc , prepared , assigned with refl ← just-injective assigned
    with unbind (resolve𝔹 (State.mem st) g) _ prepared
  ...   | flag , bit , resolved with unbind (resolve-all-Fr (State.mem st) ops) _ resolved
  ...     | vs , vals , found with unbind (State.proofs st id) _ found
  ...       | blob , pr , keyed with unbind (resolve-vk h (IrSource.inner-vks s)) _ keyed
  ...         | key , key-ok , actual = [] , same st , λ tail →
    prepare-step bit vals pr key-ok (parsed key key-ok) (compatible flag vs blob key bit vals pr key-ok , prep-result flag key vs blob acc actual) (align acc prepared)
  invert p s w st (accumulate ops out) after (fold-ok align) ok
    with unbind (fold-result (State.mem st) ops) _ ok
  ... | acc , folded , assigned with refl ← just-injective assigned
    with unbind (resolve-accs (State.mem st) ops) _ folded
  ...   | [] , _ , ()
  ...   | _ ∷ [] , _ , ()
  ...   | a ∷ b ∷ rs , vals , result = [] , same st , λ tail → fold-step vals result (align acc folded)
  invert p s w st (verify-accumulator x) after expose-ok ok with resolve-acc (State.mem st) x in resolved
  ... | nothing with () ← ok
  ... | just acc with refl ← just-injective ok = [] , same st , λ tail → expose-step resolved
  invert p s w st (circuit-output ops) after output-ok ok with collectOutputs (State.mem st) (IrSource.outputs s) ops in vals
  ... | nothing with () ← ok
  ... | just vs with refl ← just-injective ok = [] , same st , λ tail → output-step vals

-- The accepted interpreter chooses all intermediate states.  A caller
-- supplies only the local conditions for states reached by that trace.
Along : ∀ {p s st is final} → CircuitWitness → Trace p s st is final → Set
Along w done = ⊤
Along {s = s} w (next {i} {st = st} ok rest) = Supported s w st i × Along w rest

ready-trace : ∀ {p s st is final} w (tr : Trace p s st is final) → Along w tr →
              ∃ λ slots → State.inner-witnesses final ≡ State.inner-witnesses st ++ slots
                        × ReadyRun p s w st slots is final []
ready-trace {st = st} w done _ = [] , same st , empty
ready-trace {p} {s} w (next {i} {st = st} {mid} ok rest) (local , later)
  with invert p s w st i mid local ok | ready-trace w rest later
... | prefix , grew , head | tail , accumulated , ready =
  prefix ++ tail ,
  trans accumulated (trans (cong (_++ tail) grew) (++-assoc (State.inner-witnesses st) prefix tail)) ,
  instr (head tail) ready

open import zkir-v4.SlotReplay ⋯ using (initial-history)

ready-from-preprocess : ∀ s p final (w : CircuitWitness) (accepted : preprocess s p ≡ just final)
                      → let a = preprocess-inversion {s} {p} accepted in Along w (AcceptedRun.trace a)
                      → ReadyRun p s w (AcceptedRun.initial (preprocess-inversion {s} {p} accepted))
                          (State.inner-witnesses final) (IrSource.instructions s) final []
ready-from-preprocess s p final w accepted with preprocess-inversion {s} {p} accepted
... | a = build
  where
  build : Along w (AcceptedRun.trace a)
        → ReadyRun p s w (AcceptedRun.initial a) (State.inner-witnesses final) (IrSource.instructions s) final []
  build local with ready-trace w (AcceptedRun.trace a) local
  ... | slots , history , ready =
    subst (λ xs → ReadyRun p s w (AcceptedRun.initial a) xs (IrSource.instructions s) final [])
      (sym (trans history (cong (_++ slots) (initial-history s p _ (AcceptedRun.initialized a))))) ready
