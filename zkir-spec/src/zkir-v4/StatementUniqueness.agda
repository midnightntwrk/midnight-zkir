{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.StatementUniqueness (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Syntax ⋯
open import zkir-v4.Types ⋯
open import zkir-v4.Semantics ⋯
open import zkir-v4.SemanticsProperties ⋯ using (AcceptedRun; Exhausted; preprocess-inversion)
open import zkir-v4.Circuit ⋯
open import zkir-v4.CircuitBridge ⋯ using (view)
open import zkir-v4.CircuitProof ⋯ using (honest-witness)
open import zkir-v4.CircuitEffects ⋯ using (PreparationLaws; PreparationForward; preparation-forward)
open import zkir-v4.CircuitEvents ⋯
open import zkir-v4.CircuitForward ⋯
open import zkir-v4.CircuitExtraction ⋯ renaming (empty to empty-fragment)
open import zkir-v4.CircuitInputs ⋯ using (InitialInputsAgree; initial-inputs-encode; init-forward)
open import zkir-v4.Encoding ⋯ using () renaming (encode to encode-value)
open import zkir-v4.EncodingProperties ⋯ using (EncodingLaws; decode-encode-sound)
open import zkir-v4.SlotReplay ⋯ using (with-slots; preprocess-normalized)
open import zkir-v4.Validation ⋯ using (validate)

open import Data.Bool using (true; false; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; length; drop)
open import Data.List.Properties using (++-identityʳ; ++-assoc; take++drop≡id; drop-drop; drop-all)
open import Data.Maybe using (just; nothing; _>>=_)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; trans)

private
  Slots = List (List Byte)

  remaining-impacts : ProofPreimage → State → List Fr
  remaining-impacts p st = drop (State.pti-idx st) (ProofPreimage.pub-transcript-inputs p)

  -- A fragment accounts for the prefix consumed in each stream.
  record Pieces (p : ProofPreimage) (st : State) (retained : Slots)
                (after : State) (later : Slots) (f : Fragment) : Set where
    field
      impacts : remaining-impacts p st ≡ Fragment.impacts f ++ remaining-impacts p after
      public-reads : State.pto-rem st ≡ Fragment.public-reads f ++ State.pto-rem after
      private-reads : State.priv-rem st ≡ Fragment.private-reads f ++ State.priv-rem after
      proofs : retained ≡ Fragment.proofs f ++ later

  identity-pieces : ∀ p st retained → Pieces p st retained st retained empty-fragment
  identity-pieces _ _ _ = record
    { impacts = refl ; public-reads = refl ; private-reads = refl ; proofs = refl }

  combine : ∀ {p st retained mid more last later f g}
    → Pieces p st retained mid more f → Pieces p mid more last later g
    → Pieces p st retained last later (append f g)
  combine {f = f} left right = record
    { impacts = join (Fragment.impacts f) (Pieces.impacts left) (Pieces.impacts right)
    ; public-reads = join (Fragment.public-reads f) (Pieces.public-reads left) (Pieces.public-reads right)
    ; private-reads = join (Fragment.private-reads f) (Pieces.private-reads left) (Pieces.private-reads right)
    ; proofs = join (Fragment.proofs f) (Pieces.proofs left) (Pieces.proofs right)
    }
    where
    join : ∀ {A : Set} (prefix : List A) {a b c suffix}
      → a ≡ prefix ++ b → b ≡ suffix ++ c → a ≡ (prefix ++ suffix) ++ c
    join prefix {c = c} {suffix = suffix} first second =
      trans first (trans (cong (prefix ++_) second) (sym (++-assoc prefix suffix c)))

  step-fragment : ∀ {p src w st retained i after later}
    → ReadyStep p src w st retained i after later
    → Σ Fragment λ f →
        (event (view st retained) (view after later) i ≡ just f) × Pieces p st retained after later f
  step-fragment {i = i} (common lowering _ _) =
    empty-fragment , common-eventless i lowering _ _ ,
      record { impacts = refl ; public-reads = refl ; private-reads = refl ; proofs = refl }
  step-fragment (bit-constraint _ _ _) =
    empty-fragment , refl , record { impacts = refl ; public-reads = refl ; private-reads = refl ; proofs = refl }
  step-fragment (division _ _ _) =
    empty-fragment , refl , record { impacts = refl ; public-reads = refl ; private-reads = refl ; proofs = refl }
  step-fragment (reconstitution _ _ _) =
    empty-fragment , refl , record { impacts = refl ; public-reads = refl ; private-reads = refl ; proofs = refl }
  step-fragment (special support _ _) =
    empty-fragment , special-eventless support _ _ ,
      record { impacts = refl ; public-reads = refl ; private-reads = refl ; proofs = refl }

  step-fragment {st = st} (public-read {t = t} {id = id} {active = true} {v = v} bit read _ _)
    rewrite bit | inserted-value id v (State.mem st) =
    record empty-fragment { public-reads = encode-value v } , refl ,
    record
      { impacts = refl
      ; public-reads = trans (sym (take++drop≡id (encoded-len t) (State.pto-rem st)))
                              (cong (_++ drop (encoded-len t) (State.pto-rem st))
                                    (sym (decode-encode-sound {t = t} read)))
      ; private-reads = refl
      ; proofs = refl
      }
  step-fragment (public-read {active = false} bit _ _ _) rewrite bit =
    empty-fragment , refl , record { impacts = refl ; public-reads = refl ; private-reads = refl ; proofs = refl }
  step-fragment {st = st} (private-read {t = t} {id = id} {active = true} {v = v} bit read _ _)
    rewrite bit | inserted-value id v (State.mem st) =
    record empty-fragment { private-reads = encode-value v } , refl ,
    record
      { impacts = refl
      ; public-reads = refl
      ; private-reads = trans (sym (take++drop≡id (encoded-len t) (State.priv-rem st)))
                              (cong (_++ drop (encoded-len t) (State.priv-rem st))
                                    (sym (decode-encode-sound {t = t} read)))
      ; proofs = refl
      }
  step-fragment (private-read {active = false} bit _ _ _) rewrite bit =
    empty-fragment , refl , record { impacts = refl ; public-reads = refl ; private-reads = refl ; proofs = refl }
  step-fragment {p = p} {st = st} (impact-step {ops = ops} {active = true} {values = values} bit resolved read)
    rewrite bit | resolved =
    record empty-fragment { impacts = values } , refl ,
    record
      { impacts = trans (sym (take++drop≡id (length ops) (remaining-impacts p st)))
                        (trans (cong (_++ drop (length ops) (remaining-impacts p st)) read)
                               (cong (values ++_) (drop-drop (State.pti-idx st) (length ops)
                                                            (ProofPreimage.pub-transcript-inputs p))))
      ; public-reads = refl ; private-reads = refl ; proofs = refl
      }
  step-fragment (impact-step {active = false} bit _ _) rewrite bit =
    empty-fragment , refl , record { impacts = refl ; public-reads = refl ; private-reads = refl ; proofs = refl }
  step-fragment {st = st} (proof-slot {id = id} {raw = raw} {active = true} _ bit)
    rewrite bit | inserted-proof id raw (State.proofs st) =
    record empty-fragment { proofs = raw ∷ [] } , refl ,
      record { impacts = refl ; public-reads = refl ; private-reads = refl ; proofs = refl }
  step-fragment {st = st} (proof-slot {id = id} {active = false} _ bit)
    rewrite bit | inserted-proof id [] (State.proofs st) =
    record empty-fragment { proofs = [] ∷ [] } , refl ,
      record { impacts = refl ; public-reads = refl ; private-reads = refl ; proofs = refl }
  step-fragment (prepare-step _ _ _ _ _ _ _) =
    empty-fragment , refl , record { impacts = refl ; public-reads = refl ; private-reads = refl ; proofs = refl }
  step-fragment (fold-step _ _ _) =
    empty-fragment , refl , record { impacts = refl ; public-reads = refl ; private-reads = refl ; proofs = refl }
  step-fragment (expose-step _) =
    empty-fragment , refl , record { impacts = refl ; public-reads = refl ; private-reads = refl ; proofs = refl }
  step-fragment (output-step _) =
    empty-fragment , refl , record { impacts = refl ; public-reads = refl ; private-reads = refl ; proofs = refl }

  gather-fragments : ∀ {p src w st retained is final rest}
    → PreparationForward
    → ReadyRun p src w st retained is final rest
    → Σ Fragment λ f →
        (gather src w (view st retained) is ≡ just f) × Pieces p st retained final rest f
  gather-fragments laws ReadyRun.empty = empty-fragment , refl , identity-pieces _ _ _
  gather-fragments laws (instr ready rest)
    with agrees-step-using laws ready | step-fragment ready | gather-fragments laws rest
  ... | _ , step-ok | first , event-ok , first-pieces | later , gathered , later-pieces
    rewrite step-ok | event-ok | gathered =
    append first later , refl , combine first-pieces later-pieces

  initial-streams : ∀ src p st → init src p ≡ just st
    → (remaining-impacts p st ≡ ProofPreimage.pub-transcript-inputs p)
      × (State.pto-rem st ≡ ProofPreimage.pub-transcript-outputs p)
      × (State.priv-rem st ≡ ProofPreimage.priv-transcript p)
  initial-streams src p st ok
    with decode-inputs (IrSource.inputs src) (ProofPreimage.inputs p)
  ... | nothing with ok
  ...   | ()
  initial-streams src p st ok | just _ with IrSource.do-communications-commitment src
  ... | false with just-injective ok
  ...   | refl = refl , refl , refl
  initial-streams src p st ok | just _ | true with ProofPreimage.comm-commitment p
  ... | nothing with ok
  ...   | ()
  initial-streams src p st ok | just _ | true | just (_ , _) with just-injective ok
  ... | refl = refl , refl , refl

  fragment-exhausted : ∀ src p start final f
    → init src p ≡ just start → Exhausted p final
    → Pieces p start (State.inner-witnesses final) final [] f
    → (Fragment.impacts f ≡ ProofPreimage.pub-transcript-inputs p)
      × (Fragment.public-reads f ≡ ProofPreimage.pub-transcript-outputs p)
      × (Fragment.private-reads f ≡ ProofPreimage.priv-transcript p)
      × (Fragment.proofs f ≡ State.inner-witnesses final)
  fragment-exhausted src p start final f initialized exhausted pieces
    with initial-streams src p start initialized
  ... | impacts , public-reads , private-reads =
    last-piece (Fragment.impacts f)
      (trans (sym impacts) (Pieces.impacts pieces)) last-impact ,
    last-piece (Fragment.public-reads f)
      (trans (sym public-reads) (Pieces.public-reads pieces)) (Exhausted.public-outputs-used exhausted) ,
    last-piece (Fragment.private-reads f)
      (trans (sym private-reads) (Pieces.private-reads pieces)) (Exhausted.private-used exhausted) ,
    last-piece (Fragment.proofs f) (Pieces.proofs pieces) refl
    where
    last-piece : ∀ {A : Set} (used : List A) {stream leftover}
      → stream ≡ used ++ leftover → leftover ≡ [] → used ≡ stream
    last-piece used eq refl = trans (sym (++-identityʳ used)) (sym eq)
    last-impact : remaining-impacts p final ≡ []
    last-impact =
      trans (cong (λ n → drop n (ProofPreimage.pub-transcript-inputs p))
                  (Exhausted.public-inputs-used exhausted))
            (drop-all _ (ProofPreimage.pub-transcript-inputs p) ≤-refl)

-- The canonical preimage retains all fields visible to the run. Proof
-- slots carry the normalized witnessed bytes, and a disabled commitment
-- has no pair. The external Rust key-location field is outside the model.
canonical : IrSource → ProofPreimage → State → ProofPreimage
canonical src p final = record p
  { inner-proofs = State.inner-witnesses final
  ; comm-commitment =
      if IrSource.do-communications-commitment src
      then ProofPreimage.comm-commitment p else nothing
  }

private
  without-commitment : ProofPreimage → ProofPreimage
  without-commitment p = record p { comm-commitment = nothing }

  init-ignores-disabled-commitment : ∀ src p
    → IrSource.do-communications-commitment src ≡ false
    → init src (without-commitment p) ≡ init src p
  init-ignores-disabled-commitment src p disabled
    rewrite disabled with decode-inputs (IrSource.inputs src) (ProofPreimage.inputs p)
  ... | nothing = refl
  ... | just _ = refl

  run-ignores-commitment : ∀ src p st instructions
    → run (without-commitment p) src st instructions ≡ run p src st instructions
  run-ignores-commitment src p st [] = refl
  run-ignores-commitment src p st (i ∷ is) with step p src st i
  ... | nothing = refl
  ... | just next = run-ignores-commitment src p next is

  finish-ignores-disabled-commitment : ∀ src p st
    → IrSource.do-communications-commitment src ≡ false
    → finish src (without-commitment p) st ≡ finish src p st
  finish-ignores-disabled-commitment src p st disabled
    with State.pto-rem st | State.priv-rem st | State.proof-rem st
  ... | [] | [] | [] rewrite disabled = refl
  ... | _ ∷ _ | _ | _ = refl
  ... | [] | _ ∷ _ | _ = refl
  ... | [] | [] | _ ∷ _ = refl

  preprocess-ignores-disabled-commitment : ∀ src p
    → IrSource.do-communications-commitment src ≡ false
    → preprocess src (without-commitment p) ≡ preprocess src p
  preprocess-ignores-disabled-commitment src p disabled with validate src
  ... | false = refl
  ... | true rewrite init-ignores-disabled-commitment src p disabled
    with init src p
  ... | nothing = refl
  ... | just start rewrite run-ignores-commitment src p start (IrSource.instructions src)
    with run p src start (IrSource.instructions src)
  ... | nothing = refl
  ... | just final = finish-ignores-disabled-commitment src p final disabled

  canonical-enabled : ∀ src p final → IrSource.do-communications-commitment src ≡ true
    → canonical src p final ≡ with-slots p (State.inner-witnesses final)
  canonical-enabled src p final flag = cong (λ enabled →
    record (with-slots p (State.inner-witnesses final))
      { comm-commitment = if enabled then ProofPreimage.comm-commitment p else nothing }) flag

  canonical-disabled : ∀ src p final → IrSource.do-communications-commitment src ≡ false
    → canonical src p final ≡ without-commitment (with-slots p (State.inner-witnesses final))
  canonical-disabled src p final flag = cong (λ enabled →
    record (with-slots p (State.inner-witnesses final))
      { comm-commitment = if enabled then ProofPreimage.comm-commitment p else nothing }) flag

-- Erasing inactive slots and a disabled commitment preserves the
-- complete accepted run, including both public input blocks.
canonical-accepted : ∀ src p final → preprocess src p ≡ just final
  → preprocess src (canonical src p final) ≡ just final
canonical-accepted src p final accepted
  with IrSource.do-communications-commitment src in flag
... | true =
  trans (cong (preprocess src) (canonical-enabled src p final flag))
        (preprocess-normalized src p final accepted)
... | false =
  trans (cong (preprocess src) (canonical-disabled src p final flag))
    (trans (preprocess-ignores-disabled-commitment src (with-slots p (State.inner-witnesses final)) flag)
           (preprocess-normalized src p final accepted))

private
  extract-gathered : ∀ src p final start f
    → let w = honest-witness p final in
      initᶜ src w ≡ just (view start (State.inner-witnesses final))
    → gather src (honest-witness p final) (view start (State.inner-witnesses final))
        (IrSource.instructions src) ≡ just f
    → encode-inputs (State.mem start) (IrSource.inputs src) ≡ ProofPreimage.inputs p
    → Fragment.impacts f ≡ ProofPreimage.pub-transcript-inputs p
    → Fragment.public-reads f ≡ ProofPreimage.pub-transcript-outputs p
    → Fragment.private-reads f ≡ ProofPreimage.priv-transcript p
    → Fragment.proofs f ≡ State.inner-witnesses final
    → satisfies src (honest-witness p final) (view final [])
    → extract src (honest-witness p final) ≡ just (canonical src p final)
  extract-gathered src p final start f initialized gathered raw impacts public-reads private-reads proofs satisfied
    rewrite satisfied | initialized | gathered | raw | impacts | public-reads | private-reads | proofs = refl

extract-honest : ∀ src p final → PreparationForward
  → (accepted : preprocess src p ≡ just final)
  → let start = AcceptedRun.initial (preprocess-inversion {src} {p} accepted)
        w = honest-witness p final in
    (initᶜ src w ≡ just (view start (State.inner-witnesses final)))
  → ReadyRun p src (honest-witness p final)
      (AcceptedRun.initial (preprocess-inversion {src} {p} accepted))
      (State.inner-witnesses final) (IrSource.instructions src) final []
  → encode-inputs (State.mem (AcceptedRun.initial (preprocess-inversion {src} {p} accepted)))
                 (IrSource.inputs src) ≡ ProofPreimage.inputs p
  → satisfies src (honest-witness p final) (view final [])
  → extract src (honest-witness p final) ≡ just (canonical src p final)
extract-honest src p final laws accepted initialized ready raw satisfied =
  prove-fragment (gather-fragments laws ready)
  where
  info = preprocess-inversion {src} {p} accepted
  start = AcceptedRun.initial info
  prove-fragment : (Σ Fragment λ f →
    gather src (honest-witness p final) (view start (State.inner-witnesses final))
      (IrSource.instructions src) ≡ just f
    × Pieces p start (State.inner-witnesses final) final [] f)
    → extract src (honest-witness p final) ≡ just (canonical src p final)
  prove-fragment (f , gathered , pieces)
    with fragment-exhausted src p start final f
           (AcceptedRun.initialized info) (AcceptedRun.streams-exhausted info) pieces
  ... | impacts , public-reads , private-reads , proofs =
    extract-gathered src p final start f initialized gathered raw impacts public-reads private-reads proofs satisfied

-- Extraction is a function. If the same witness has two accepted
-- explanations under the correspondence hypotheses, their canonical
-- representatives agree. This includes equality on all active slots.
canonical-unique-for-witness : ∀ src w p q p-final q-final
  → extract src w ≡ just (canonical src p p-final)
  → extract src w ≡ just (canonical src q q-final)
  → canonical src p p-final ≡ canonical src q q-final
canonical-unique-for-witness _ _ _ _ _ _ a b = just-injective (trans (sym a) b)

-- An explanation supplies the accepted trace's local circuit-side
-- premises and agrees with the original declared inputs.
record HonestExplanation (src : IrSource) (p : ProofPreimage) (final : State) : Set where
  field
    accepted : preprocess src p ≡ just final
    input-agreement : InitialInputsAgree src p (honest-witness p final)
    ready : ReadyRun p src (honest-witness p final)
              (AcceptedRun.initial (preprocess-inversion {src} {p} accepted))
              (State.inner-witnesses final) (IrSource.instructions src) final []

extract-explanation : EncodingLaws → PreparationLaws → ∀ {src p final}
  → HonestExplanation src p final
  → extract src (honest-witness p final) ≡ just (canonical src p final)
extract-explanation codecs prepare {src} {p} {final} explanation =
  extract-honest src p final (preparation-forward prepare) accepted initialized ready raw satisfying
  where
  open HonestExplanation explanation
  accepted-run = preprocess-inversion {src} {p} accepted
  initialized = init-forward codecs src p (honest-witness p final)
                  input-agreement refl refl (AcceptedRun.initialized accepted-run)
  raw = initial-inputs-encode codecs src p (honest-witness p final)
          input-agreement (AcceptedRun.initialized accepted-run)
  satisfying = forward src p final codecs prepare accepted input-agreement ready

explanations-unique-modulo-erasure : EncodingLaws → PreparationLaws
  → ∀ {src p q p-final q-final}
  → HonestExplanation src p p-final
  → HonestExplanation src q q-final
  → honest-witness p p-final ≡ honest-witness q q-final
  → canonical src p p-final ≡ canonical src q q-final
explanations-unique-modulo-erasure codecs prepare {src} {p} {q} {p-final} {q-final} a b same =
  canonical-unique-for-witness src (honest-witness q q-final) p q p-final q-final
    (trans (cong (extract src) (sym same)) (extract-explanation codecs prepare a))
    (extract-explanation codecs prepare b)
