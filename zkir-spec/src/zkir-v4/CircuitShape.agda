{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.CircuitShape (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Syntax ⋯
open import zkir-v4.Types ⋯
open import zkir-v4.Semantics ⋯
open import zkir-v4.Circuit ⋯
open import zkir-v4.CircuitBridge ⋯
open import zkir-v4.CircuitForward ⋯
open import zkir-v4.CircuitProof ⋯ using (honest-witness)
open import zkir-v4.CommitmentInputs ⋯ using (honest-terminal-inputs)
open import zkir-v4.InputProperties ⋯ using (DeclaredValues; []ᵈ; _∷ᵈ_)
open import zkir-v4.CircuitInputs ⋯ using (ValidDeclarations; InitialInputsAgree; init-forward; initial-inputs-encode)
open import zkir-v4.SemanticsProperties ⋯ using (AcceptedRun; preprocess-inversion)
open import zkir-v4.CircuitEffects ⋯
open import zkir-v4.CircuitBackward ⋯
open import zkir-v4.CircuitClosedEffects ⋯
open import zkir-v4.CircuitExtraction ⋯ renaming (empty to empty-fragment)
open import zkir-v4.CircuitReplay ⋯
open import zkir-v4.Encoding ⋯ using () renaming (encode to encode-value)
open import zkir-v4.EncodingProperties ⋯ using (decode-admissible; EncodingLaws)
open import zkir-v4.CircuitEvents ⋯ using (common-eventless; special-eventless; inserted-value; inserted-proof)
open import zkir-v4.ProofSlots using (keep)

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; take)
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

Origin : ∀ {i} → CircuitWitness → CircuitState → CircuitState → Set
Origin {i} w st after =
  Σ Fragment λ f → (event st after i ≡ just f)
                   × ReplayAction w (CircuitState.mem st) (CircuitState.proof-rem st) i f

private
  checked-bound : ∀ m i {writes}
                → preprocess-bounded m i ≡ just writes
                → preprocess-bit-bounds i ≡ true
  checked-bound m i ok with preprocess-bit-bounds i
  ... | true = refl
  ... | false with () ← ok

  declared-valid : ∀ {declarations} → DeclaredValues declarations → ValidDeclarations declarations
  declared-valid []ᵈ = All.[]
  declared-valid (v ∷ᵈ (typed , allowed , rest)) =
    All._∷_ (subst (λ t → valid-type t ≡ true) typed allowed) (declared-valid rest)

  normalized-twice : ∀ (b : Bool) (raw : List Byte) → keep b (keep b raw) ≡ keep b raw
  normalized-twice true _  = refl
  normalized-twice false _ = refl

ready-step-origin : ∀ {p src w st retained i after later}
                  → ReadyStep p src w st retained i after later
                  → Origin {i} w (view st retained) (view after later)
ready-step-origin {st = st} {retained} {i} {after} {later}
  (common lowering _ _) =
  empty-fragment , common-eventless i lowering (view st retained) (view after later)
                 , pure (common-op lowering)
ready-step-origin {st = st} {i = i@(constrain-bits _ _)} (bit-constraint _ computed _) =
  empty-fragment , refl , pure (bit-constraint-op (checked-bound (State.mem st) i computed))
ready-step-origin {st = st} {i = i@(div-mod-power-of-two _ _ _)} (division _ computed _) =
  empty-fragment , refl , pure (division-op (checked-bound (State.mem st) i computed))
ready-step-origin {st = st} {i = i@(reconstitute-field _ _ _ _)} (reconstitution _ computed _) =
  empty-fragment , refl , pure (reconstitution-op (checked-bound (State.mem st) i computed))
ready-step-origin {st = st} {retained} {after = after} {later}
  (special support _ _) =
  empty-fragment , special-eventless support (view st retained) (view after later)
                 , pure (special-op support)
ready-step-origin {st = st} {retained}
  (public-read {g = g} {t} {id} {true} {v} bit decoded assigned typed) =
  record empty-fragment { public-reads = encode-value v } ,
  observed , active-public {v = v} bit
    (decode-admissible {t = t} {raw = take (encoded-len t) (State.pto-rem st)} {v = v} decoded)
  where
  observed : event (view st retained) (view (public-result t st id true v) retained)
                   (public-input g t id)
             ≡ just (record empty-fragment { public-reads = encode-value v })
  observed rewrite bit | inserted-value id v (State.mem st) = refl
ready-step-origin {st = st} {retained}
  (public-read {g = g} {t} {id} {false} bit refl assigned typed) =
  empty-fragment , observed , inactive-public bit assigned
  where
  observed : event (view st retained)
                   (view (public-result t st id false (default-val t)) retained)
                   (public-input g t id) ≡ just empty-fragment
  observed rewrite bit = refl
ready-step-origin {st = st} {retained}
  (private-read {g = g} {t} {id} {true} {v} bit decoded assigned typed) =
  record empty-fragment { private-reads = encode-value v } ,
  observed , active-private {v = v} bit
    (decode-admissible {t = t} {raw = take (encoded-len t) (State.priv-rem st)} {v = v} decoded)
  where
  observed : event (view st retained) (view (private-result t st id true v) retained)
                   (private-input g t id)
             ≡ just (record empty-fragment { private-reads = encode-value v })
  observed rewrite bit | inserted-value id v (State.mem st) = refl
ready-step-origin {st = st} {retained}
  (private-read {g = g} {t} {id} {false} bit refl assigned typed) =
  empty-fragment , observed , inactive-private bit assigned
  where
  observed : event (view st retained)
                   (view (private-result t st id false (default-val t)) retained)
                   (private-input g t id) ≡ just empty-fragment
  observed rewrite bit = refl
ready-step-origin {st = st} {retained}
  (impact-step {g = g} {ops} {true} {values} bit resolved _) =
  record empty-fragment { impacts = values } , observed , active-impact bit resolved
  where
  observed : event (view st retained) (view (impact-result st ops true values) retained) (impact g ops)
             ≡ just (record empty-fragment { impacts = values })
  observed rewrite bit | resolved = refl
ready-step-origin {st = st} {retained}
  (impact-step {g = g} {ops} {false} {values} bit resolved _) =
  empty-fragment , observed , inactive-impact bit resolved
  where
  observed : event (view st retained) (view (impact-result st ops false values) retained) (impact g ops)
             ≡ just empty-fragment
  observed rewrite bit = refl
ready-step-origin {st = st}
  (proof-slot {retained} {g} {id} {raw} {rest} {active} slots bit) =
  record empty-fragment { proofs = keep active raw ∷ [] } ,
  observed , inner-slot bit refl (normalized-twice active raw)
  where
  observed : event (view st (keep active raw ∷ retained))
                    (view (bind-result st id (keep active raw) rest) retained) (inner-proof g id)
             ≡ just (record empty-fragment { proofs = keep active raw ∷ [] })
  observed rewrite bit | inserted-proof id (keep active raw) (State.proofs st)
                   | normalized-twice active raw = refl
ready-step-origin (prepare-step _ _ _ _ _ _ _) = empty-fragment , refl , closed prepare-effect
ready-step-origin (fold-step _ _ _) = empty-fragment , refl , closed fold-effect
ready-step-origin (expose-step _) = empty-fragment , refl , closed expose-effect
ready-step-origin (output-step _) = empty-fragment , refl , closed output-effect

ready-replay : ∀ {p src w st retained is final later}
             → PreparationLaws
             → ReadyRun p src w st retained is final later
             → Σ Fragment λ f → ReplayTrace src w (view st retained) is f (view final later)
ready-replay laws empty = empty-fragment , end
ready-replay laws (instr ready rest) with ready-step-origin ready | ready-replay laws rest
... | local , observed , action | suffix , trace =
  append local suffix , next (proj₂ (agrees-step laws ready)) observed action trace

-- Every honest preprocessing path with the forward premises supplies
-- its own extraction trace.  This yields membership in the domain of
-- the extractor without an additional backward witness-shape premise.
honest-extraction-domain : ∀ (encoding : EncodingLaws) (prepare : PreparationLaws)
                               src p final
                           → (accepted : preprocess src p ≡ just final)
                           → InitialInputsAgree src p (honest-witness p final)
                           → ReadyRun p src (honest-witness p final)
                               (AcceptedRun.initial (preprocess-inversion {src} {p} accepted))
                               (State.inner-witnesses final) (IrSource.instructions src) final []
                           → Σ ProofPreimage λ extracted →
                               extract src (honest-witness p final) ≡ just extracted
honest-extraction-domain encoding prepare src p final accepted assigned ready
  with ready-replay prepare ready
... | streams , trace =
  extract-evidence
    (extraction-complete encoding prepare src w start (view final []) streams
      (AcceptedRun.source-valid run-info) (declared-valid (proj₁ assigned)) initialized
      (forward src p final encoding prepare accepted assigned ready) trace
      (λ _ → trans terminal-inputs (sym original-inputs)))
  where
  run-info = preprocess-inversion {src} {p} accepted
  w = honest-witness p final
  start = view (AcceptedRun.initial run-info) (State.inner-witnesses final)
  initialized = init-forward encoding src p w assigned refl refl (AcceptedRun.initialized run-info)
  terminal-inputs = honest-terminal-inputs src p (AcceptedRun.initial run-info) final
                      (State.inner-witnesses final) [] assigned (AcceptedRun.initialized run-info) ready
  original-inputs = initial-inputs-encode encoding src p w assigned (AcceptedRun.initialized run-info)
  extract-evidence : (Σ ProofPreimage λ q → Σ State λ result →
                        (extract src w ≡ just q) × (preprocess src q ≡ just result)
                        × (view result [] ≡ view final []))
                   → Σ ProofPreimage λ q → extract src w ≡ just q
  extract-evidence (q , _ , found , _ , _) = q , found
