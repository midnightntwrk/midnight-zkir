{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.RecursiveVerification (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Syntax ⋯
open import zkir-v4.Types ⋯
open import zkir-v4.Circuit ⋯
open import zkir-v4.CircuitEffects ⋯ using (PreparationLaws; preparation-forward)
open import zkir-v4.CircuitProperties ⋯ using (satisfying-public-inputs; satisfying-run; SatisfiedRun; Trace; next; end)
open import zkir-v4.CircuitBridge ⋯ using (write-backward)
open import zkir-v4.Operations ⋯ using (Mem; ∅; ins; resolveᶠ; to𝔹; _≟LFr_; _≟B_)
open import zkir-v4.Validation ⋯ using (validate; resolve-vk)
open import zkir-v4.ReverseShape ⋯ using (immediate-true)
open import zkir-v4.Protocol ⋯
open import zkir-v4.EncodingProperties ⋯ using (EncodingLaws)
open import zkir-v4.ProducerCorrespondence ⋯ using (module ForKey)
open import zkir-v4.ProtocolProperties ⋯ using (module Backend)
open import zkir-v4.ProtocolProperties ⋯ public using (instance-inj)

open import Data.Bool using (true; false; T)
open import Data.Empty using (⊥-elim)
open import Data.Bool.Properties using (T?)
import Data.Vec.Base as Vec
open import Data.List using (List; []; _∷_; _++_; length; map)
open import Data.List.Relation.Unary.All as All using (All)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ)
open import Data.Product using (∃; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_; yes; no; Dec; does)

data Exposure : Set where
  separate folded : Exposure

count : Exposure → ℕ
count separate = 2
count folded = 1

ending : Exposure → List Instruction
ending separate = verify-accumulator (var "%a") ∷ verify-accumulator (var "%b") ∷ []
ending folded = accumulate (var "%a" ∷ var "%b" ∷ []) "%f" ∷ verify-accumulator (var "%f") ∷ []

-- Each inner key expects one native public field and no carried accumulators.
-- Both modes use the same two declared inputs and publish them in the same order.
wrapper : (table : List (List Byte)) (h₁ h₂ : List Byte) → Exposure → IrSource
wrapper table h₁ h₂ mode = mk-ir-source V0 ("%x" ⦂ native ∷ "%y" ⦂ native ∷ []) [] false
  (impact (imm 1ᶠ) (var "%x" ∷ var "%y" ∷ []) ∷
   inner-proof (imm 1ᶠ) "%p" ∷
   prepare-verification (imm 1ᶠ) h₁ (var "%x" ∷ []) "%p" "%a" ∷
   inner-proof (imm 1ᶠ) "%q" ∷
   prepare-verification (imm 1ᶠ) h₂ (var "%y" ∷ []) "%q" "%b" ∷ ending mode) table

-- These are the two canonical source tables. With two entries the digests
-- must differ; two uses of a single key share its one entry.
private
  digest : List Byte → List Byte
  digest k = Vec.toList (sha256-bytes k)

  finds-head : ∀ k tail → resolve-vk (digest k) (k ∷ tail) ≡ just k
  finds-head k tail with digest k ≟B digest k
  ... | yes _ = refl
  ... | no neq = ⊥-elim (neq refl)

  yes-test : ∀ {P : Set} (d : Dec P) → P → does d ≡ true
  yes-test (yes _) _ = refl
  yes-test (no n) p = ⊥-elim (n p)

  no-test : ∀ {P : Set} (d : Dec P) → ¬ P → does d ≡ false
  no-test (yes p) n = ⊥-elim (n p)
  no-test (no _) _ = refl

  one-test = yes-test (1ᶠ ≟ᶠ 1ᶠ) refl
  self-test = λ (k : List Byte) → yes-test (digest k ≟B digest k) refl

module SharedKey (k : List Byte) where
  table = k ∷ []
  resolves = finds-head k []
  validated : ∀ mode → validate (wrapper table (digest k) (digest k) mode) ≡ true
  validated separate rewrite one-test | one-test | self-test k = refl
  validated folded rewrite one-test | one-test | self-test k = refl

module DistinctKeys (k l : List Byte) (distinct : ¬ (digest k ≡ digest l)) where
  table = k ∷ l ∷ []
  first-key = finds-head k (l ∷ [])
  second-key : resolve-vk (digest l) table ≡ just l
  second-key with digest l ≟B digest k
  ... | yes eq = ⊥-elim (distinct (sym eq))
  ... | no _ = finds-head l []

  private
    different = no-test (digest k ≟B digest l) distinct
    opposite = no-test (digest l ≟B digest k) (λ eq → distinct (sym eq))

  validated : ∀ mode → validate (wrapper table (digest k) (digest l) mode) ≡ true
  validated separate rewrite one-test | one-test | different | opposite | self-test k | self-test l = refl
  validated folded rewrite one-test | one-test | different | opposite | self-test k | self-test l = refl

data Exposes (a b : Accumulator) : Exposure → List Accumulator → Set where
  both : Exposes a b separate (a ∷ b ∷ [])
  batch : ∀ {f} → fold-accumulators (a ∷ b ∷ []) ≡ just f → Exposes a b folded (f ∷ [])

Valid : Accumulator → Set
Valid a = T (pairing-valid a)

-- Direct verification is independently supplied, at the same inner Poseidon
-- transcript, processed key, full instance and KZG parameters as preparation.
record DirectLaws (Direct : List Byte → List Fr → List Byte → Set)
                  (key : List Byte) (pi : List Fr) : Set where
  field
    direct-prepares : ∀ p → Direct key pi p → prepare-compatible key pi p true ≡ true ×
      (∃ λ a → prepare-active key pi p ≡ just a × Valid a)
    valid-instance : ∀ p a → prepare-active key pi p ≡ just a → Valid a →
      ∃ λ raw → Direct key pi raw

module Active {Direct : List Byte → List Fr → List Byte → Set} {key pi}
              (laws : DirectLaws Direct key pi) (chip : PreparationLaws)
              (parsed : key-well-formed key ≡ true) where

  direct-to-circuit : ∀ p → Direct key pi p →
    ∃ λ a → prepare-circuit key pi p true ≡ just a × Valid a
  direct-to-circuit p ok with DirectLaws.direct-prepares laws p ok
  ... | compatible , a , eq , va =
    a , preparation-forward chip key pi p true a parsed (compatible , eq) , va

  circuit-to-direct : ∀ p a → prepare-circuit key pi p true ≡ just a → Valid a →
    ∃ λ raw → Direct key pi raw
  circuit-to-direct p a eq =
    DirectLaws.valid-instance laws p a (PreparationLaws.prepared-result chip key pi p true a parsed eq)

-- The inactive branch discharges only the trivial equation. It still has a
-- structural key/slot requirement and makes no claim about the proof bytes.
disabled-valid : PreparationLaws → Valid trivial-accumulator → ∀ k xs p →
  key-well-formed k ≡ true → prepare-compatible k xs p false ≡ true →
  ∃ λ a → prepare-circuit k xs p false ≡ just a × Valid a
disabled-valid chip neutral k xs p parsed compatible =
  trivial-accumulator , PreparationLaws.inactive-prepares chip k xs p parsed compatible , neutral

FoldComplete : Set
FoldComplete = ∀ a b → Valid a → Valid b →
  ∃ λ f → fold-accumulators (a ∷ b ∷ []) ≡ just f × Valid f

Folding : Exposure → Set
Folding separate = ⊤
Folding folded = FoldComplete

private
  active : to𝔹 1ᶠ ≡ just true
  active = immediate-true (mk-state ∅ (λ _ → nothing) [] [] [] [])

module Wrapper (table : List (List Byte)) (h₁ h₂ k₁ k₂ : List Byte)
  (key₁ : resolve-vk h₁ table ≡ just k₁) (key₂ : resolve-vk h₂ table ≡ just k₂)
  (parsed₁ : key-well-formed k₁ ≡ true) (parsed₂ : key-well-formed k₂ ≡ true) where

  source : Exposure → IrSource
  source = wrapper table h₁ h₂

  record Prepared (x y : Fr) (mode : Exposure) (carried : List Accumulator) : Set where
    constructor prepared
    field
      p q : List Byte
      a b : Accumulator
      left  : prepare-circuit k₁ (x ∷ []) p true ≡ just a
      right : prepare-circuit k₂ (y ∷ []) q true ≡ just b
      exposed : Exposes a b mode carried

  private
    fields : Fr → Fr → Fr → List Fr
    fields binding x y = binding ∷ x ∷ y ∷ []

    input-store : Fr → Fr → Mem
    input-store x y = ins "%y" (val-native y) (ins "%x" (val-native x) ∅)

  builds : ∀ mode → validate (source mode) ≡ true → ∀ binding x y carried →
    Prepared x y mode carried → ∃ λ w → ∃ λ final →
      satisfies (source mode) w final × CircuitWitness.full-pis w ≡ instance-fields carried (fields binding x y)
  builds mode valid binding x y carried (prepared p q a b pa pb exposure) with exposure
  ... | both = w , result
    where
    pi = instance-fields (a ∷ b ∷ []) (fields binding x y)
    w = mk-witness (input-store x y) pi binding nothing (p ∷ q ∷ [])
    result : ∃ λ final → satisfies (source separate) w final × CircuitWitness.full-pis w ≡ pi
    result rewrite valid | active | key₁ | parsed₁ | pa | key₂ | parsed₂ | pb
      with pi ≟LFr pi
    ... | yes _ = _ , refl , refl
    ... | no neq = ⊥-elim (neq refl)
  ... | batch {f} folded-ok = w , result
    where
    pi = instance-fields (f ∷ []) (fields binding x y)
    w = mk-witness (input-store x y) pi binding nothing (p ∷ q ∷ [])
    result : ∃ λ final → satisfies (source folded) w final × CircuitWitness.full-pis w ≡ pi
    result rewrite valid | active | key₁ | parsed₁ | pa | key₂ | parsed₂ | pb | folded-ok
      with pi ≟LFr pi
    ... | yes _ = _ , refl , refl
    ... | no neq = ⊥-elim (neq refl)

  private
    install : CircuitState → Identifier → Accumulator → CircuitState
    install st id a = record st { mem = ins id (val-accumulator a) (CircuitState.mem st) }

    prep-result : ∀ mode w st h k operand proof-name out x p {after} →
      resolveᶠ (CircuitState.mem st) operand ≡ just x →
      CircuitState.proofs st proof-name ≡ just p →
      resolve-vk h table ≡ just k → key-well-formed k ≡ true →
      stepᶜ (source mode) w st (prepare-proof (imm 1ᶠ) h (operand ∷ []) proof-name out) ≡ just after →
      ∃ λ a → prepare-circuit k (x ∷ []) p true ≡ just a × after ≡ install st out a
    prep-result mode w st h k operand proof-name out x p rx slot key parsed ok
      rewrite active | rx | slot | key | parsed with prepare-circuit k (x ∷ []) p true
    ... | nothing with () ← ok
    ... | just a = a , refl , write-backward true w st ((out , val-accumulator a) ∷ []) ok

    impact-result : ∀ mode w st {after} →
      stepᶜ (source mode) w st (publish-impact (imm 1ᶠ) (var "%x" ∷ var "%y" ∷ [])) ≡ just after →
      ∃ λ x → ∃ λ y →
        resolveᶠ (CircuitState.mem st) (var "%x") ≡ just x ×
        resolveᶠ (CircuitState.mem st) (var "%y") ≡ just y ×
        after ≡ record st { pis = CircuitState.pis st ++ (x ∷ y ∷ []) }
    impact-result mode w st ok rewrite active with resolveᶠ (CircuitState.mem st) (var "%x")
    ... | nothing with () ← ok
    ... | just x with resolveᶠ (CircuitState.mem st) (var "%y")
    ...   | nothing with () ← ok
    ...   | just y = x , y , refl , refl , sym (just-injective ok)

    tail-shape : ∀ mode w m proofs slots statement a b {final} →
      let st = mk-state m proofs slots [] statement [] in
      Trace (source mode) w (install (install st "%a" a) "%b" b) (map lower (ending mode)) final →
      Exposes a b mode (CircuitState.accs final) × CircuitState.pis final ≡ statement
    tail-shape separate w m proofs slots statement a b (next refl (next refl end)) = both , refl
    tail-shape folded w m proofs slots statement a b (next {st = before} ok rest)
      with fold-accumulators (a ∷ b ∷ []) in reduced
    ... | nothing with () ← ok
    ... | just f with refl ← write-backward true w before (("%f" , val-accumulator f) ∷ []) ok
      with next refl end ← rest = batch reduced , refl

    Observed : Exposure → CircuitWitness → CircuitState → Set
    Observed mode w final = ∃ λ x → ∃ λ y → Prepared x y mode (CircuitState.accs final) ×
      CircuitState.pis final ≡ fields (CircuitWitness.binding-input w) x y

    walk : ∀ mode w m slots {final} →
      let st = mk-state m (λ _ → nothing) slots [] (CircuitWitness.binding-input w ∷ []) [] in
      Trace (source mode) w st (map lower (IrSource.instructions (source mode))) final →
      Observed mode w final
    walk mode w m slots (next {st = start} impact-ok rest) with impact-result mode w start impact-ok
    ... | x , y , rx , ry , refl with slots | rest
    ...   | [] | next () _
    ...   | p ∷ more | next refl (next {st = before-left} left tail)
      with prep-result mode w before-left h₁ k₁ (var "%x") "%p" "%a" x p rx refl key₁ parsed₁ left
    ...     | a , pa , refl with more | tail
    ...       | [] | next () _
    ...       | q ∷ slots′ | next refl (next {st = before-right} right rest′)
      with prep-result mode w before-right h₂ k₂ (var "%y") "%q" "%b" y q ry refl key₂ parsed₂ right
    ...         | b , pb , refl with tail-shape mode w m _ slots′ _ a b rest′
    ...           | exposure , statement = x , y , prepared p q a b pa pb exposure , statement

    observe : ∀ mode w final → satisfies (source mode) w final → Observed mode w final
    observe mode w final ok with satisfying-run (source mode) w final ok
    ... | record { initialized = init-ok ; path = path }
      with declare w ∅ (IrSource.inputs (source mode))
    ...   | nothing with () ← init-ok
    ...   | just m with refl ← just-injective init-ok = walk mode w m _ path

    exposure-count : ∀ {a b mode carried} → Exposes a b mode carried → length carried ≡ count mode
    exposure-count both = refl
    exposure-count (batch _) = refl

  -- This event is impossible in separate mode. In folded mode it identifies
  -- the two actual prepared obligations and the successful carried equation.
  data BadFold (x y : Fr) : Exposure → List Accumulator → Set where
    cancellation : ∀ {p q a b f} →
      prepare-circuit k₁ (x ∷ []) p true ≡ just a →
      prepare-circuit k₂ (y ∷ []) q true ≡ just b →
      fold-accumulators (a ∷ b ∷ []) ≡ just f →
      Valid f → ¬ (Valid a × Valid b) → BadFold x y folded (f ∷ [])

  module Composition (Direct : List Byte → List Fr → List Byte → Set)
                     (left-law : ∀ x → DirectLaws Direct k₁ (x ∷ []))
                     (right-law : ∀ y → DirectLaws Direct k₂ (y ∷ []))
                     (chip : PreparationLaws)
                     (OuterOK : Exposure → List Byte → List Fr → Set) where

    module V (mode : Exposure) = Verification (OuterOK mode)
    module B (mode : Exposure) = Backend (OuterOK mode)
    module K (mode : Exposure) = ForKey (source mode) (OuterOK mode)

    BothDirect : Fr → Fr → Set
    BothDirect x y = (∃ λ p → Direct k₁ (x ∷ []) p) × (∃ λ q → Direct k₂ (y ∷ []) q)

    Accepted : Exposure → Fr → Fr → Fr → Set
    Accepted mode binding x y = ∃ λ proof → V.Accepts mode (count mode) proof (fields binding x y)

    private
      expose-valid : (mode : Exposure) → Folding mode → ∀ a b → Valid a → Valid b →
        ∃ λ carried → Exposes a b mode carried × All Valid carried
      expose-valid separate _ a b left right =
        _ , both , left All.∷ right All.∷ All.[]
      expose-valid folded folds a b left right with folds a b left right
      ... | f , eq , good = _ , batch eq , good All.∷ All.[]

    complete : ∀ mode → validate (source mode) ≡ true → B.FromCircuit mode (source mode) →
      Folding mode → ∀ binding x y → BothDirect x y → Accepted mode binding x y
    complete mode valid backend folds binding x y ((p , left) , (q , right))
      with Active.direct-to-circuit (left-law x) chip parsed₁ p left
         | Active.direct-to-circuit (right-law y) chip parsed₂ q right
    ... | a , pa , va | b , pb , vb with expose-valid mode folds a b va vb
    ...   | carried , exposure , pairs with builds mode valid binding x y carried
             (prepared p q a b pa pb exposure)
    ...     | w , final , sat , bound with backend w final sat
    ...       | raw , verified = V.proof raw carried , record
      { count-matches = exposure-count exposure
      ; outer-valid = subst (OuterOK mode raw) bound verified
      ; pairings = pairs }

    private
      recover : EncodingLaws → ∀ mode → K.ExtractsWitness mode →
        ∀ binding x y pr → V.Accepts mode (count mode) pr (fields binding x y) →
        Prepared x y mode (V.Proof.carried {mode = mode} pr)
      recover codecs mode backend binding x y pr accepted
        with backend (V.Proof.raw {mode = mode} pr) _ (V.Accepts.outer-valid {mode = mode} accepted)
      ... | w , final , sat , bound with observe mode w final sat
      ...   | x′ , y′ , prep , stmt with instance-inj codecs (CircuitState.accs final) (V.Proof.carried {mode = mode} pr)
              (trans (exposure-count (Prepared.exposed prep)) (sym (V.Accepts.count-matches {mode = mode} accepted)))
              (trans (satisfying-public-inputs {source mode} {w} sat) bound)
      ...     | same , suffix with trans (sym stmt) suffix
      ...       | refl = subst (Prepared x y mode) same prep

      classify : ∀ {x y mode carried} → Prepared x y mode carried → All Valid carried →
        BothDirect x y ⊎ BadFold x y mode carried
      classify {x} {y} (prepared p q a b pa pb both) (va All.∷ vb All.∷ All.[]) =
        inj₁ (Active.circuit-to-direct (left-law x) chip parsed₁ p a pa va ,
              Active.circuit-to-direct (right-law y) chip parsed₂ q b pb vb)
      classify {x} {y} (prepared p q a b pa pb (batch eq)) (vf All.∷ All.[])
        with T? (pairing-valid a) | T? (pairing-valid b)
      ... | yes va | yes vb =
        inj₁ (Active.circuit-to-direct (left-law x) chip parsed₁ p a pa va ,
              Active.circuit-to-direct (right-law y) chip parsed₂ q b pb vb)
      ... | no bad | _ = inj₂ (cancellation pa pb eq vf (λ pair → bad (proj₁ pair)))
      ... | yes _ | no bad = inj₂ (cancellation pa pb eq vf (λ pair → bad (proj₂ pair)))

    sound-or-bad-fold : EncodingLaws → ∀ mode → K.ExtractsWitness mode →
      ∀ binding x y pr → V.Accepts mode (count mode) pr (fields binding x y) →
      BothDirect x y ⊎ BadFold x y mode (V.Proof.carried {mode = mode} pr)
    sound-or-bad-fold codecs mode backend binding x y pr accepted =
      classify (recover codecs mode backend binding x y pr accepted) (V.Accepts.pairings {mode = mode} accepted)

    separate-sound : EncodingLaws → K.ExtractsWitness separate →
      ∀ binding x y → Accepted separate binding x y → BothDirect x y
    separate-sound codecs backend binding x y (pr , accepted)
      with sound-or-bad-fold codecs separate backend binding x y pr accepted
    ... | inj₁ direct = direct
    ... | inj₂ ()

    folded-sound : EncodingLaws → K.ExtractsWitness folded →
      ∀ binding x y pr → V.Accepts folded 1 pr (fields binding x y) →
      ¬ BadFold x y folded (V.Proof.carried {mode = folded} pr) → BothDirect x y
    folded-sound codecs backend binding x y pr accepted no-bad
      with sound-or-bad-fold codecs folded backend binding x y pr accepted
    ... | inj₁ direct = direct
    ... | inj₂ bad = ⊥-elim (no-bad bad)

    -- The two wrapper keys differ. Conversion preserves the external statement.
    separate-to-folded : EncodingLaws → K.ExtractsWitness separate →
      validate (source folded) ≡ true → B.FromCircuit folded (source folded) → FoldComplete →
      ∀ binding x y → Accepted separate binding x y → Accepted folded binding x y
    separate-to-folded codecs extractor valid backend folds binding x y accepted =
      complete folded valid backend folds binding x y (separate-sound codecs extractor binding x y accepted)

    folded-to-separate : EncodingLaws → K.ExtractsWitness folded →
      validate (source separate) ≡ true → B.FromCircuit separate (source separate) →
      ∀ binding x y pr → V.Accepts folded 1 pr (fields binding x y) →
      ¬ BadFold x y folded (V.Proof.carried {mode = folded} pr) → Accepted separate binding x y
    folded-to-separate codecs extractor valid backend binding x y pr accepted no-bad =
      complete separate valid backend tt binding x y (folded-sound codecs extractor binding x y pr accepted no-bad)

-- One induction step for a Poseidon-transcript inner proof with a carried
-- prefix. Bind the same carried values into the full instance and check all
-- their pairings in addition to the opening equation of this proof.
module Nested (Direct : List Byte → List Fr → List Byte → Set)
              (chip : PreparationLaws)
              (key : List Byte) (parsed : key-well-formed key ≡ true) where
  open Verification (λ raw pi → Direct key pi raw)

  record Deferred (n : ℕ) (pr : Proof) (stmt : List Fr) : Set where
    constructor deferred
    field
      count-ok : length (Proof.carried pr) ≡ n
      opening : Accumulator
      prepared-opening : prepare-circuit key (instance-fields (Proof.carried pr) stmt)
                            (Proof.raw pr) true ≡ just opening
      checked : All Valid (opening ∷ Proof.carried pr)

  direct-to-deferred : ∀ {n pr s} → DirectLaws Direct key (instance-fields (Proof.carried pr) s) →
    Accepts n pr s → Deferred n pr s
  direct-to-deferred {pr = pr} {s} laws ok with Active.direct-to-circuit laws chip parsed (Proof.raw pr) (Accepts.outer-valid ok)
  ... | a , eq , va = deferred (Accepts.count-matches ok) a eq (va All.∷ Accepts.pairings ok)

  deferred-to-direct : ∀ {n pr s} → DirectLaws Direct key (instance-fields (Proof.carried pr) s) → Deferred n pr s →
    ∃ λ raw → Accepts n (proof raw (Proof.carried pr)) s
  deferred-to-direct {pr = pr} {s} laws (deferred count-ok a eq (va All.∷ carried-ok))
    with Active.circuit-to-direct laws chip parsed (Proof.raw pr) a eq va
  ... | raw , direct = raw , record
    { count-matches = count-ok ; outer-valid = direct ; pairings = carried-ok }

  -- For proof representations with identical acceptance by both parsers the
  -- byte-preserving version follows under this stronger, local native law.
  ExactAt : Proof → List Fr → Set
  ExactAt pr s = let pi = instance-fields (Proof.carried pr) s in
    ∀ a → prepare-active key pi (Proof.raw pr) ≡ just a → Valid a → Direct key pi (Proof.raw pr)

  deferred-to-direct-exact : ∀ {n pr s} → ExactAt pr s → Deferred n pr s → Accepts n pr s
  deferred-to-direct-exact {pr = pr} {s} exact (deferred count-ok a eq (va All.∷ carried-ok)) = record
    { count-matches = count-ok
    ; outer-valid = exact a (PreparationLaws.prepared-result chip key
        (instance-fields (Proof.carried pr) s) (Proof.raw pr) true a parsed eq) va
    ; pairings = carried-ok }
