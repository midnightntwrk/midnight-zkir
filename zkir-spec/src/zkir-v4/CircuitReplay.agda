{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.CircuitReplay (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Syntax ⋯
open import zkir-v4.Types ⋯
open import zkir-v4.Semantics ⋯ hiding (write)
open import zkir-v4.Circuit ⋯
open import zkir-v4.CircuitBridge ⋯
open import zkir-v4.CircuitBackward ⋯
open import zkir-v4.CircuitClosedEffects ⋯
open import zkir-v4.CircuitEffects ⋯
open import zkir-v4.CircuitExtraction ⋯
open import zkir-v4.CircuitInputs ⋯
open import zkir-v4.Encoding ⋯ using () renaming (encode to encode-value)
open import zkir-v4.EncodingProperties ⋯
open import zkir-v4.ProofSlots using (keep)
open import zkir-v4.Validation ⋯ using (validate)

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; map; length; take; drop)
open import Data.List.Properties using (++-assoc; ++-identityʳ; length-++)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Nat using (_≟_; suc)
import Data.String
import Relation.Nullary.Negation
open import Data.Product using (_×_; _,_; Σ; proj₁)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import Relation.Nullary using (yes; no)

-- Preconditions arise where the Rust synthesis contract omits an
-- interpreter check.  A skipped typed input has the default value,
-- and a skipped proof slot carries no bytes.  Runtime guard bits are
-- checked even at instructions whose synthesis ignores the guard.
data ReplayAction (w : CircuitWitness) (m : Mem) (proofs : List (List Byte)) :
                  Instruction → Fragment → Set where
  pure : ∀ {i} → PureAdmissible m i → ReplayAction w m proofs i empty
  closed : ∀ {i} → ClosedEffect i → ReplayAction w m proofs i empty
  active-impact : ∀ {g ops values}
    → resolve𝔹 m g ≡ just true → resolve-all-Fr m ops ≡ just values
    → ReplayAction w m proofs (impact g ops) (record empty { impacts = values })
  inactive-impact : ∀ {g ops values}
    → resolve𝔹 m g ≡ just false → resolve-all-Fr m ops ≡ just values
    → ReplayAction w m proofs (impact g ops) empty
  active-public : ∀ {g t id v}
    → eval-guard m g ≡ just true → valid-type t ≡ true
    → ReplayAction w m proofs (public-input g t id) (record empty { public-reads = encode-value v })
  inactive-public : ∀ {g t id}
    → eval-guard m g ≡ just false → CircuitWitness.assign w id ≡ just (default-val t)
    → ReplayAction w m proofs (public-input g t id) empty
  active-private : ∀ {g t id v}
    → eval-guard m g ≡ just true → valid-type t ≡ true
    → ReplayAction w m proofs (private-input g t id) (record empty { private-reads = encode-value v })
  inactive-private : ∀ {g t id}
    → eval-guard m g ≡ just false → CircuitWitness.assign w id ≡ just (default-val t)
    → ReplayAction w m proofs (private-input g t id) empty
  inner-slot : ∀ {g id active blob rest}
    → resolve𝔹 m g ≡ just active → proofs ≡ blob ∷ rest → keep active blob ≡ blob
    → ReplayAction w m proofs (inner-proof g id) (record empty { proofs = blob ∷ [] })

-- The shape ties every fragment to the circuit cells that produced it.
-- It records no off-circuit evaluation or acceptance.
data ReplayTrace (src : IrSource) (w : CircuitWitness) :
                 CircuitState → List Instruction → Fragment → CircuitState → Set where
  end : ∀ {st} → ReplayTrace src w st [] empty st
  next : ∀ {st i after is local suffix final}
       → stepᶜ src w st (lower i) ≡ just after
       → event st after i ≡ just local
       → ReplayAction w (CircuitState.mem st) (CircuitState.proof-rem st) i local
       → ReplayTrace src w after is suffix final
       → ReplayTrace src w st (i ∷ is) (append local suffix) final

gather-trace : ∀ {src w st is streams final}
             → ReplayTrace src w st is streams final → gather src w st is ≡ just streams
gather-trace end = refl
gather-trace (next circuit-step observed _ rest)
  rewrite circuit-step | observed | gather-trace rest = refl

record Available (p : ProofPreimage) (st : State) (suffix : Fragment) : Set where
  constructor available
  field
    consumed    : List Fr
    cursor      : State.pti-idx st ≡ length consumed
    impact-tail : ProofPreimage.pub-transcript-inputs p ≡ consumed ++ Fragment.impacts suffix
    public-tail : State.pto-rem st ≡ Fragment.public-reads suffix
    private-tail : State.priv-rem st ≡ Fragment.private-reads suffix
    proof-tail  : State.proof-rem st ≡ Fragment.proofs suffix

private
  take-front : ∀ {A : Set} (xs ys : List A) → take (length xs) (xs ++ ys) ≡ xs
  take-front [] _ = refl
  take-front (x ∷ xs) ys = cong (x ∷_) (take-front xs ys)

  drop-front : ∀ {A : Set} (xs ys : List A) → drop (length xs) (xs ++ ys) ≡ ys
  drop-front [] _ = refl
  drop-front (_ ∷ xs) ys = drop-front xs ys

  resolved-length : ∀ m ops values
                  → resolve-all-Fr m ops ≡ just values → length ops ≡ length values
  resolved-length _ [] .[] refl = refl
  resolved-length m (op ∷ ops) values eq with resolveᶠ m op
  ... | nothing with () ← eq
  resolved-length m (op ∷ ops) values eq | just x with resolve-all-Fr m ops in rest
  ... | nothing with () ← eq
  ... | just xs with refl ← eq = cong suc (resolved-length m ops xs rest)

  transport-frame : ∀ {p before after suffix}
                  → State.pti-idx after ≡ State.pti-idx before
                  → State.pto-rem after ≡ State.pto-rem before
                  → State.priv-rem after ≡ State.priv-rem before
                  → State.proof-rem after ≡ State.proof-rem before
                  → Available p before suffix → Available p after suffix
  transport-frame pti pto priv proof (available consumed cursor impacts publics privates proofs) =
    available consumed (trans pti cursor) impacts (trans pto publics)
      (trans priv privates) (trans proof proofs)

  active-decoded : ∀ (laws : EncodingLaws) t v actual tail
                 → typeof v ≡ t → valid-type t ≡ true
                 → actual ≡ encode-value v ++ tail
                 → ReadValue true t actual v
  active-decoded laws t v actual tail refl valid refl
    rewrite take-encode v tail = encode-decode laws v valid

  active-dropped : ∀ t v actual tail
                 → typeof v ≡ t → actual ≡ encode-value v ++ tail
                 → drop (encoded-len t) actual ≡ tail
  active-dropped t v actual tail refl refl = drop-encode v tail

ReplayResult : ProofPreimage → IrSource → State → Instruction → CircuitState → Fragment → Set
ReplayResult p src st i target suffix =
  Σ State λ after →
     (step p src st i ≡ just after)
   × (view after (CircuitState.proof-rem target) ≡ target)
   × Available p after suffix

private
  just-injective : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
  just-injective refl = refl

  inserted : ∀ m id v → ins id v m id ≡ just v
  inserted m id v with id Data.String.≟ id
  ... | yes _ = refl
  ... | no unequal = Relation.Nullary.Negation.contradiction refl unequal

  public-selected : ∀ st retained g t id actual saved
                  → eval-guard (State.mem st) g ≡ just true
                  → event (view st retained)
                       (record (view st retained) { mem = ins id actual (State.mem st) })
                       (public-input g t id)
                       ≡ just (record empty { public-reads = encode-value saved })
                  → encode-value actual ≡ encode-value saved
  public-selected st retained g t id actual saved bit observed
    rewrite bit | inserted (State.mem st) id actual =
    cong Fragment.public-reads (just-injective observed)

  private-selected : ∀ st retained g t id actual saved
                   → eval-guard (State.mem st) g ≡ just true
                   → event (view st retained)
                        (record (view st retained) { mem = ins id actual (State.mem st) })
                        (private-input g t id)
                        ≡ just (record empty { private-reads = encode-value saved })
                   → encode-value actual ≡ encode-value saved
  private-selected st retained g t id actual saved bit observed
    rewrite bit | inserted (State.mem st) id actual =
    cong Fragment.private-reads (just-injective observed)

  finish-step : ∀ p src w st retained i target suffix after
               → Agreement p src w st retained i after retained
               → stepᶜ src w (view st retained) (lower i) ≡ just target
               → Available p after suffix
               → ReplayResult p src st i target suffix
  finish-step p src w st retained i target suffix after (off , on) accepted avail
    with refl ← just-injective (trans (sym on) accepted) = after , off , refl , avail

replay-step-using : ∀ (encoding : EncodingLaws) (prepare : PreparationBackward)
               p src w st retained i target local suffix
            → stepᶜ src w (view st retained) (lower i) ≡ just target
            → event (view st retained) target i ≡ just local
            → ReplayAction w (State.mem st) retained i local
            → Available p st (append local suffix)
            → ReplayResult p src st i target suffix
replay-step-using encoding prepare p src w st retained i target .empty suffix ok observed (pure allowed) available-before
  with pure-preprocess-step p src w st retained i target allowed ok
... | after , off , refl =
  after , off , refl ,
  transport-frame (PureFrame.pti-idx-same frame) (PureFrame.pto-rem-same frame)
    (PureFrame.priv-rem-same frame) (PureFrame.proof-rem-same frame) available-before
  where frame : PureFrame st after
        frame = pure-frame p src st i after allowed off
replay-step-using encoding prepare p src w st retained i target .empty suffix ok observed (closed allowed) available-before
  with closed-effect-backward-using prepare p src w st retained i target allowed ok
... | after , off , refl , frame =
  after , off , refl ,
  transport-frame (ClosedEffectFrame.pti-idx-same frame) (ClosedEffectFrame.pto-rem-same frame)
    (ClosedEffectFrame.priv-rem-same frame) (ClosedEffectFrame.proof-rem-same frame) available-before
replay-step-using encoding prepare p src w st retained (impact g ops) target _ suffix ok observed
  (active-impact {values = values} bit resolved)
  (available consumed cursor impacts pub priv proofs) =
  finish-step p src w st retained (impact g ops) target suffix
    (impact-result st ops true values) (impact-agrees p src w st retained g ops true values bit resolved checked) ok
    (available (consumed ++ values) advanced remaining pub priv proofs)
  where
  checked : ImpactRead p st ops true values
  checked rewrite cursor | impacts | drop-front consumed (values ++ Fragment.impacts suffix)
        | resolved-length (State.mem st) ops values resolved =
    take-front values (Fragment.impacts suffix)

  advanced : State.pti-idx (impact-result st ops true values) ≡ length (consumed ++ values)
  advanced rewrite cursor | resolved-length (State.mem st) ops values resolved =
    sym (length-++ consumed {ys = values})

  remaining : ProofPreimage.pub-transcript-inputs p ≡ (consumed ++ values) ++ Fragment.impacts suffix
  remaining = trans impacts (sym (++-assoc consumed values (Fragment.impacts suffix)))
replay-step-using encoding prepare p src w st retained (impact g ops) target .empty suffix ok observed
  (inactive-impact {values = values} bit resolved) available-before =
  finish-step p src w st retained (impact g ops) target suffix (impact-result st ops false values)
    (impact-agrees p src w st retained g ops false values bit resolved tt) ok (transport-frame refl refl refl refl available-before)
replay-step-using encoding prepare p src w st retained (public-input g t id) target _ suffix ok observed
  (active-public {v = saved} bit admissible)
  (available consumed cursor impacts pub priv proofs)
  with witness-cell-backward src w (view st retained) t id ok
... | actual , assigned , typed , refl =
  next-state , proj₁ agreed , refl , available consumed cursor impacts remaining priv proofs
  where
  current-raw : State.pto-rem st ≡ encode-value actual ++ Fragment.public-reads suffix
  current-raw = trans pub (cong (_++ Fragment.public-reads suffix)
                   (sym (public-selected st retained g t id actual saved bit observed)))
  next-state = public-result t st id true actual
  remaining = active-dropped t actual (State.pto-rem st) (Fragment.public-reads suffix) typed current-raw
  agreed = public-read-agrees p src w st retained g t id true actual bit
             (active-decoded encoding t actual (State.pto-rem st) (Fragment.public-reads suffix)
               typed admissible current-raw)
             assigned typed
replay-step-using encoding prepare p src w st retained (public-input g t id) target .empty suffix ok observed
  (inactive-public bit defaulted) available-before
  with witness-cell-backward src w (view st retained) t id ok
... | actual , assigned , typed , refl with refl ← just-injective (trans (sym defaulted) assigned) =
  public-result t st id false actual ,
  proj₁ (public-read-agrees p src w st retained g t id false actual bit refl assigned typed) ,
  refl , transport-frame refl refl refl refl available-before
replay-step-using encoding prepare p src w st retained (private-input g t id) target _ suffix ok observed
  (active-private {v = saved} bit admissible)
  (available consumed cursor impacts pub priv proofs)
  with witness-cell-backward src w (view st retained) t id ok
... | actual , assigned , typed , refl =
  next-state , proj₁ agreed , refl , available consumed cursor impacts pub remaining proofs
  where
  current-raw : State.priv-rem st ≡ encode-value actual ++ Fragment.private-reads suffix
  current-raw = trans priv (cong (_++ Fragment.private-reads suffix)
                   (sym (private-selected st retained g t id actual saved bit observed)))
  next-state = private-result t st id true actual
  remaining = active-dropped t actual (State.priv-rem st) (Fragment.private-reads suffix) typed current-raw
  agreed = private-read-agrees p src w st retained g t id true actual bit
             (active-decoded encoding t actual (State.priv-rem st) (Fragment.private-reads suffix)
               typed admissible current-raw)
             assigned typed
replay-step-using encoding prepare p src w st retained (private-input g t id) target .empty suffix ok observed
  (inactive-private bit defaulted) available-before
  with witness-cell-backward src w (view st retained) t id ok
... | actual , assigned , typed , refl with refl ← just-injective (trans (sym defaulted) assigned) =
  private-result t st id false actual ,
  proj₁ (private-read-agrees p src w st retained g t id false actual bit refl assigned typed) ,
  refl , transport-frame refl refl refl refl available-before
replay-step-using encoding prepare p src w st retained (inner-proof g id) target _ suffix ok observed
  (inner-slot {active = active} {blob = blob} {rest = rest} bit slots canonical)
  (available consumed cursor impacts pub priv proofs)
  with refl ← slots
  with refl ← just-injective ok =
  bind-result st id blob (Fragment.proofs suffix) ,
  off , refl , available consumed cursor impacts pub priv refl
  where
  off : step p src st (inner-proof g id) ≡ just (bind-result st id blob (Fragment.proofs suffix))
  off rewrite proofs | bit | canonical = refl

replay-run-using : ∀ (encoding : EncodingLaws) (prepare : PreparationBackward)
              p src w st retained is streams target
            → ReplayTrace src w (view st retained) is streams target
            → Available p st streams
            → Σ State λ final →
                 (run p src st is ≡ just final)
               × (view final (CircuitState.proof-rem target) ≡ target)
               × Available p final empty
replay-run-using encoding prepare p src w st retained [] streams target end avail =
  st , refl , refl , avail
replay-run-using encoding prepare p src w st retained (i ∷ is) streams target
  (next {after = after} {local = local} {suffix = suffix} circuit-step observed action rest) avail
  with replay-step-using encoding prepare p src w st retained i after local suffix circuit-step observed action avail
... | next-state , off , refl , subsequent
  with replay-run-using encoding prepare p src w next-state (CircuitState.proof-rem after)
         is suffix target rest subsequent
...   | final , off-rest , view-ok , exhausted rewrite off = final , off-rest , view-ok , exhausted

circuit-trace-runs : ∀ {src w start is streams target}
                    → ReplayTrace src w start is streams target
                    → runᶜ src w start (map lower is) ≡ just target
circuit-trace-runs end = refl
circuit-trace-runs (next circuit-step _ _ rest) rewrite circuit-step = circuit-trace-runs rest

private
  initial-streams : ∀ src p st
                  → init src p ≡ just st
                  → (State.pti-idx st ≡ 0)
                    × (State.pto-rem st ≡ ProofPreimage.pub-transcript-outputs p)
                    × (State.priv-rem st ≡ ProofPreimage.priv-transcript p)
                    × (State.proof-rem st ≡ ProofPreimage.inner-proofs p)
  initial-streams src p st eq with decode-inputs (IrSource.inputs src) (ProofPreimage.inputs p)
  ... | nothing with () ← eq
  initial-streams src p st eq | just _ with IrSource.do-communications-commitment src
  ... | false with refl ← just-injective eq = refl , refl , refl , refl
  initial-streams src p st eq | just _ | true with ProofPreimage.comm-commitment p
  ... | nothing with () ← eq
  ... | just (_ , _) with refl ← just-injective eq = refl , refl , refl , refl

  finish-extracted : ∀ src p st
                    → Available p st empty
                    → check-commit src p st ≡ just st
                    → finish src p st ≡ just st
  finish-extracted src p st (available consumed cursor impacts pub priv proofs) comm
    rewrite pub | priv | proofs =
    trans (guard-pass (State.pti-idx st ≟ length (ProofPreimage.pub-transcript-inputs p))
             all-impacts (check-commit src p st)) comm
    where
    all-impacts : State.pti-idx st ≡ length (ProofPreimage.pub-transcript-inputs p)
    all-impacts = trans cursor (cong length (sym (trans impacts (++-identityʳ consumed))))

  finish-circuit-commitment : ∀ src w st
                            → finishᶜ src w st ≡ just st
                            → finish-commitment src w st ≡ just st
  finish-circuit-commitment src w st eq
    with full-public-inputsᶜ st ≟LFr CircuitWitness.full-pis w
  ... | yes _ = eq
  ... | no _ with () ← eq

  transfers-commitment : ∀ src w p st retained
                        → ProofPreimage.comm-commitment p
                           ≡ (if IrSource.do-communications-commitment src
                              then CircuitWitness.comm-commitment w else nothing)
                        → (IrSource.do-communications-commitment src ≡ true →
                            encode-inputs (State.mem st) (IrSource.inputs src) ≡ ProofPreimage.inputs p)
                        → finish-commitment src w (view st retained) ≡ just (view st retained)
                        → check-commit src p st ≡ just st
  transfers-commitment src w p st retained same-comm same-inputs checked
    with IrSource.do-communications-commitment src
  ... | false = refl
  ... | true rewrite same-comm | sym (same-inputs refl) with CircuitWitness.comm-commitment w
  ...   | nothing with () ← checked
  transfers-commitment src w p st retained same-comm same-inputs checked | true | just (c , r)
    with c ≟ᶠ transient-commit
      (encode-inputs (State.mem st) (IrSource.inputs src) ++ encode-outputs (view st retained)) r
  ... | yes _ = refl
  ... | no _ with () ← checked

  built-preimage : IrSource → CircuitWitness → CircuitState → Fragment → ProofPreimage
  built-preimage src w start streams =
    replay-inputs src w start (record
      { inputs = []
      ; binding-input = CircuitWitness.binding-input w
      ; comm-commitment = nothing
      ; pub-transcript-inputs = Fragment.impacts streams
      ; pub-transcript-outputs = Fragment.public-reads streams
      ; priv-transcript = Fragment.private-reads streams
      ; inner-proofs = Fragment.proofs streams
      })

  replay-original : ∀ src w start streams →
                     replay-inputs src w start (built-preimage src w start streams)
                       ≡ built-preimage src w start streams
  replay-original src w start streams = refl

  terminal-from-circuit : ∀ src w start target
                        → validate src ≡ true
                        → initᶜ src w ≡ just start
                        → runᶜ src w start (map lower (IrSource.instructions src)) ≡ just target
                        → satisfies src w target
                        → finishᶜ src w target ≡ just target
  terminal-from-circuit src w start target valid initial ran ok
    rewrite valid | initial | ran = ok

  finish-source : ∀ src p st final
                  → validate src ≡ true
                  → init src p ≡ just st
                  → run p src st (IrSource.instructions src) ≡ just final
                  → finish src p final ≡ just final
                  → preprocess src p ≡ just final
  finish-source src p st final valid initial ran complete
    rewrite valid | initial | ran = complete

record PrefixReplay (src : IrSource) (w : CircuitWitness) (start target : CircuitState)
                    (p : ProofPreimage) : Set where
  field
    off-start off-final : State
    off-initialized : init src p ≡ just off-start
    off-ran : run p src off-start (IrSource.instructions src) ≡ just off-final
    start-view : view off-start (CircuitWitness.inner-proofs w) ≡ start
    final-view : view off-final (CircuitState.proof-rem target) ≡ target
    off-exhausted : Available p off-final empty

replay-prefix : ∀ (encoding : EncodingLaws) (prepare : PreparationBackward) src w start target streams
              → ValidDeclarations (IrSource.inputs src)
              → initᶜ src w ≡ just start
              → ReplayTrace src w start (IrSource.instructions src) streams target
              → PrefixReplay src w start target (built-preimage src w start streams)
replay-prefix encoding prepare src w start target streams declarations initialized trace
  with init-backward encoding src w (built-preimage src w start streams) declarations initialized
... | decoded , initial , same-start rewrite replay-original src w start streams
  with initial-streams src (built-preimage src w start streams) decoded initial
...   | zero , pub , priv , proofs with sym same-start
...     | refl
  with replay-run-using encoding prepare (built-preimage src w start streams) src w decoded
         (CircuitWitness.inner-proofs w) (IrSource.instructions src) streams target trace
         (available [] zero refl pub priv proofs)
...       | final , ran , matches , exhausted = record
  { off-start = decoded ; off-final = final ; off-initialized = initial ; off-ran = ran
  ; start-view = refl ; final-view = matches ; off-exhausted = exhausted
  }

-- Extraction walks the successful circuit in source order and supplies
-- one canonical preimage.  The shape hypotheses check the primitive
-- differences at each cell.  The result includes equality of the
-- statement block, the exposed accumulators, and the typed outputs.
extraction-complete-using : ∀ (encoding : EncodingLaws) (prepare : PreparationBackward)
                        src w start target streams
                      → validate src ≡ true
                      → ValidDeclarations (IrSource.inputs src)
                      → initᶜ src w ≡ just start
                      → satisfies src w target
                      → ReplayTrace src w start (IrSource.instructions src) streams target
                      → (IrSource.do-communications-commitment src ≡ true →
                          encode-inputs (CircuitState.mem target) (IrSource.inputs src)
                            ≡ encode-inputs (CircuitState.mem start) (IrSource.inputs src))
                      → Σ ProofPreimage λ p → Σ State λ final →
                           (extract src w ≡ just p)
                         × (preprocess src p ≡ just final)
                         × (view final (CircuitState.proof-rem target) ≡ target)
extraction-complete-using encoding prepare src w start target streams valid declarations
  initialized satisfied trace stable =
  preimage , final , extracted , preprocessed , view-ok
  where
  replayed = replay-prefix encoding prepare src w start target streams declarations initialized trace
  open PrefixReplay replayed
  final = off-final
  view-ok = final-view
  preimage = built-preimage src w start streams
  extracted : extract src w ≡ just preimage
  extracted rewrite satisfied | initialized | gather-trace trace = refl
  terminal = terminal-from-circuit src w _ target valid initialized (circuit-trace-runs trace) satisfied
  comm-ok = transfers-commitment src w preimage final (CircuitState.proof-rem target)
              refl
              (λ enabled → trans (cong (λ s → encode-inputs (CircuitState.mem s) (IrSource.inputs src)) view-ok)
                                  (stable enabled))
              (subst (λ s → finish-commitment src w s ≡ just s) (sym view-ok)
                (finish-circuit-commitment src w target terminal))
  preprocessed = finish-source src preimage off-start final valid off-initialized off-ran
                   (finish-extracted src preimage final off-exhausted comm-ok)

replay-step : ∀ (encoding : EncodingLaws) (prepare : PreparationLaws)
               p src w st retained i target local suffix
            → stepᶜ src w (view st retained) (lower i) ≡ just target
            → event (view st retained) target i ≡ just local
            → ReplayAction w (State.mem st) retained i local
            → Available p st (append local suffix)
            → ReplayResult p src st i target suffix
replay-step encoding prepare = replay-step-using encoding (preparation-backward prepare)

replay-run : ∀ (encoding : EncodingLaws) (prepare : PreparationLaws)
              p src w st retained is streams target
            → ReplayTrace src w (view st retained) is streams target
            → Available p st streams
            → Σ State λ final →
                 (run p src st is ≡ just final)
               × (view final (CircuitState.proof-rem target) ≡ target)
               × Available p final empty
replay-run encoding prepare = replay-run-using encoding (preparation-backward prepare)

extraction-complete : ∀ (encoding : EncodingLaws) (prepare : PreparationLaws)
                        src w start target streams
                      → validate src ≡ true
                      → ValidDeclarations (IrSource.inputs src)
                      → initᶜ src w ≡ just start
                      → satisfies src w target
                      → ReplayTrace src w start (IrSource.instructions src) streams target
                      → (IrSource.do-communications-commitment src ≡ true →
                          encode-inputs (CircuitState.mem target) (IrSource.inputs src)
                            ≡ encode-inputs (CircuitState.mem start) (IrSource.inputs src))
                      → Σ ProofPreimage λ p → Σ State λ final →
                           (extract src w ≡ just p)
                         × (preprocess src p ≡ just final)
                         × (view final (CircuitState.proof-rem target) ≡ target)
extraction-complete encoding prepare = extraction-complete-using encoding (preparation-backward prepare)
